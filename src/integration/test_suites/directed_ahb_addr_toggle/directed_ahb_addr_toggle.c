// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// ---------------------------------------------------------------------
// Test: directed_ahb_addr_toggle
// Description:
//     Directed test to improve AHB address-bit toggle coverage. Certain
//     haddr bits (26, 23, 19) never toggle in normal simulation runs. This
//     test issues loads to addresses within the AHB peripheral window
//     (0x1000_0000 - 0x3FFF_FFFF) that have those bits set. These addresses
//     route to the bus and drive haddr with the bit asserted; being unmapped
//     they return an hresp error.
//
//     IMPORTANT (why this uses the NMI vector, not mtvec):
//     In VeeR EL2 *every* external (bus) load is issued through the
//     non-blocking load CAM (el2_lsu_bus_buffer.sv: lsu_nonblock_load_valid_m
//     has no side-effect exclusion). A bus-error response therefore comes back
//     after the load has retired and is reported as an *imprecise* error -> a
//     D-bus-load NMI (mcause = 0xF0000001), NOT a synchronous, mtvec-caught
//     load-access-fault. The NMI redirects to SOC_IFC INTERNAL_NMI_VECTOR.
//     In addition, the first imprecise error latches mdseac and suppresses
//     further error capture until mdeau is written, so the handler MUST clear
//     mdeau to re-arm error detection for the next faulting load.
//
//     Flow: main() installs an NMI handler and enters run_targets(). Each
//     target load produces an imprecise D-bus NMI; the handler counts it,
//     clears mcause/mdeau, advances the target index, and resumes execution
//     back at run_targets() (via mepc). A benign mapped read between targets
//     drives the asserted haddr bits back 1->0 so both edges are covered.
// ---------------------------------------------------------------------

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv-interrupts.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"


volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Target addresses in the AHB peripheral window (0x1000_0000 - 0x3FFF_FFFF).
// Each is unmapped, so a read drives haddr with the indicated bit(s) set and
// returns an hresp error -> imprecise D-bus-load NMI.
//   bit 26        : 0x14000000
//   bit 23        : 0x10800000
//   bit 19        : 0x10080000
//   bits 26,23,19 : 0x14880000
static const uint32_t AHB_TARGETS[] = {
    0x14000000UL,
    0x10800000UL,
    0x10080000UL,
    0x14880000UL,
};
#define NUM_TARGETS (sizeof(AHB_TARGETS) / sizeof(AHB_TARGETS[0]))

// Index of the next target to exercise, and count of NMIs observed. These are
// advanced by the NMI handler and read back in run_targets(); execution
// resumes in-place (no reset) so plain volatiles suffice.
volatile uint32_t g_target_idx  = 0;
volatile uint32_t g_fault_count = 0;

void run_targets(void);

// Force the faulting access to be a 4-byte (non-compressed) lw. Using
// lsu_read_32 could emit a compressed load; keeping it explicit documents that
// the bus transaction (and thus the haddr drive) is a single 32-bit read.
static inline uint32_t fault_lw(uintptr_t a) {
    uint32_t v;
    __asm__ volatile(".option push\n.option norvc\nlw %0,0(%1)\n.option pop"
                     : "=r"(v) : "r"(a) : "memory");
    return v;
}

// NMI handler installed at SOC_IFC INTERNAL_NMI_VECTOR. Only the expected
// imprecise D-bus-load NMI is tolerated: count it, clear the error state
// (mcause + mdeau to re-arm mdseac capture), advance to the next target, and
// redirect mepc so the (implicit) mret resumes at run_targets(). Because the
// error is imprecise the interrupted mepc is meaningless, so we restart from a
// known point rather than resuming it.
void __attribute__((interrupt("machine"), aligned(4))) nmi_handler(void) {
    uint_xlen_t cause = csr_read_mcause();
    if ((cause & MCAUSE_NMI_CODE_DBUS_LOAD_VALUE) == MCAUSE_NMI_CODE_DBUS_LOAD_VALUE) {
        g_fault_count++;
        g_target_idx++;
        csr_write_mcause(0x0);
        csr_write_mdeau(0x0);
        csr_write_mepc((uintptr_t)run_targets);
    } else {
        VPRINTF(FATAL, "Unexpected NMI in ahb_addr_toggle: mcause=%x mepc=%x\n",
                (uint32_t)cause, (uint32_t)csr_read_mepc());
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
}

// Walk the remaining targets. For each: drive haddr low with a benign mapped
// read (1->0 edge), then issue the faulting load (0->1 edge). The faulting
// load raises an imprecise D-bus NMI; the handler advances g_target_idx and
// resumes here, so the loop below re-reads the updated index and continues.
void run_targets(void) {
    while (g_target_idx < NUM_TARGETS) {
        uint32_t idx = g_target_idx;
        VPRINTF(LOW, "AHB toggle addr=0x%08x\n", AHB_TARGETS[idx]);
        (void)lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_REV_ID); // 1->0 edge
        (void)fault_lw(AHB_TARGETS[idx]);                   // 0->1 edge + NMI

        // The imprecise error normally raises an NMI within a few cycles, and
        // the handler restarts run_targets() with g_target_idx advanced, so we
        // do not fall through. Give the error time to drain; if no NMI arrives
        // the target failed to fault and the test must fail.
        for (volatile uint32_t k = 0; k < 4000; k++) { }
        VPRINTF(FATAL, "[FAIL] no NMI for target idx=%u addr=0x%08x (count=%u)\n",
                idx, AHB_TARGETS[idx], (uint32_t)g_fault_count);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    if (g_fault_count != NUM_TARGETS) {
        VPRINTF(FATAL, "[FAIL] fault count mismatch: got=%u expected=%u\n",
                (uint32_t)g_fault_count, (uint32_t)NUM_TARGETS);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    VPRINTF(LOW, "AHB address toggle complete (fault_count=%u)\n",
            (uint32_t)g_fault_count);
    SEND_STDOUT_CTRL(0xff); // PASS
    while (1);
}

void main(void) {
    VPRINTF(LOW, "----------------------------------\nAHB Address Toggle Directed Test  !!\n----------------------------------\n");

    // Standard interrupt/CSR init.
    init_interrupts();

    // External AHB load errors arrive as imprecise D-bus NMIs, so route them to
    // a test-local handler instead of letting them escalate to a reset.
    lsu_write_32((uintptr_t)(CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR), (uint32_t)nmi_handler);

    run_targets();
}
