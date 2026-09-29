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
//     haddr bits (26, 23, 19) never toggle in normal simulation runs.
//     This test issues loads and stores to addresses within the AHB
//     peripheral window (0x1000_0000 - 0x3FFF_FFFF) that have those bits
//     set. These addresses route to the bus and drive haddr with the bit
//     asserted, but being unmapped they return an hresp error which the
//     RISC-V core reports as a load/store access-fault.
//
//     A test-local trap handler is installed around the faulting accesses
//     so we do NOT modify the shared caliptra_isr.c (whose default handler
//     kills the sim on any access-fault that is not a DCCM/ICCM ECC event).
//     After the faulting accesses, a normal mapped read is performed so the
//     asserted haddr bits toggle back 1->0.
// ---------------------------------------------------------------------

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
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

// Count of expected access-faults observed by the test-local trap handler
volatile uint32_t g_expected_fault_count = 0;

// Target addresses in the AHB peripheral window (0x1000_0000 - 0x3FFF_FFFF).
// Each is unmapped, so a read/write drives haddr with the indicated bit(s)
// set and returns an hresp error -> access-fault.
//   bit 26        : 0x14000000
//   bit 23        : 0x10800000
//   bit 19        : 0x10080000
//   bits 26,23,19 : 0x14880000
#define AHB_ADDR_BIT26      0x14000000UL
#define AHB_ADDR_BIT23      0x10800000UL
#define AHB_ADDR_BIT19      0x10080000UL
#define AHB_ADDR_BIT_ALL3   0x14880000UL

#define EXPECTED_FAULT_COUNT 8

// Test-local trap handler. Installed in mtvec DIRECT mode around the faulting
// accesses. Advances mepc past the (forced 4-byte) faulting instruction and
// counts the expected access-fault. Any other trap kills the sim with error.
void __attribute__((interrupt("machine"), aligned(4))) ahb_fault_handler(void) {
    uint_xlen_t cause = csr_read_mcause();
    if (!(cause & MCAUSE_INTERRUPT_BIT_MASK) &&
        ((cause == RISCV_EXCP_LOAD_ACCESS_FAULT) || (cause == RISCV_EXCP_STORE_AMO_ACCESS_FAULT))) {
        // Faulting access is a forced 4-byte lw/sw (see fault_lw/fault_sw), so
        // advancing mepc by exactly 4 resumes at the next instruction.
        csr_write_mepc(csr_read_mepc() + 4);
        g_expected_fault_count++;
    } else {
        VPRINTF(FATAL, "Unexpected trap in ahb_addr_toggle: mcause=%x mepc=%x\n", (uint32_t)cause, (uint32_t)csr_read_mepc());
        SEND_STDOUT_CTRL(0x1); // kill with ERROR
        while (1);
    }
}

// Force the faulting accesses to be 4-byte (non-compressed) lw/sw so that a
// mepc+4 skip in the handler is always exact. Do NOT use lsu_read_32 /
// lsu_write_32 for the faulting accesses since those could be compressed.
static inline uint32_t fault_lw(uintptr_t a) {
    uint32_t v;
    __asm__ volatile(".option push\n.option norvc\nlw %0,0(%1)\n.option pop"
                     : "=r"(v) : "r"(a) : "memory");
    return v;
}
static inline void fault_sw(uintptr_t a, uint32_t d) {
    __asm__ volatile(".option push\n.option norvc\nsw %1,0(%0)\n.option pop"
                     :: "r"(a), "r"(d) : "memory");
}

// Exercise one target address: read (drives haddr, faults), write (drives
// haddr, faults), then a normal mapped read so the asserted haddr bit(s)
// toggle back 1->0.
static void toggle_addr(uintptr_t addr) {
    VPRINTF(LOW, "AHB toggle addr=0x%08x\n", (uint32_t)addr);
    (void)fault_lw(addr);           // load access-fault
    fault_sw(addr, 0xDEADBEEF);     // store access-fault
    // Normal mapped read drives haddr back to a low-address value so the
    // previously-asserted bits toggle 1->0.
    (void)lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_REV_ID);
}

void main(void) {
    uint_xlen_t saved_mtvec;

    VPRINTF(LOW, "----------------------------------\nAHB Address Toggle Directed Test  !!\n----------------------------------\n");

    // Setup the interrupt CSR configuration (standard test init)
    init_interrupts();

    // Save the current trap vector and install the test-local handler in
    // DIRECT mode (low 2 bits = 0). Exceptions do not require mstatus.MIE.
    saved_mtvec = csr_read_mtvec();
    csr_write_mtvec(((uintptr_t)ahb_fault_handler) & ~0x3UL);

    // Perform the 8 faulting accesses (read + write to each of the 4 targets),
    // interleaved with a normal mapped read so haddr bits toggle 1->0.
    toggle_addr(AHB_ADDR_BIT26);
    toggle_addr(AHB_ADDR_BIT23);
    toggle_addr(AHB_ADDR_BIT19);
    toggle_addr(AHB_ADDR_BIT_ALL3);

    // Restore the original trap vector before evaluating results.
    csr_write_mtvec(saved_mtvec);

    // Verify we observed exactly the expected number of access-faults.
    if (g_expected_fault_count != EXPECTED_FAULT_COUNT) {
        VPRINTF(FATAL, "[FAIL] fault count mismatch: got=%u expected=%u\n",
                (uint32_t)g_expected_fault_count, (uint32_t)EXPECTED_FAULT_COUNT);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    VPRINTF(LOW, "AHB address toggle complete (fault_count=%u)\n", (uint32_t)g_expected_fault_count);

    // Signal PASS
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
