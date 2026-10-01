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
// Test: directed_ahb_hold_err
// Description:
//     Directed test to cover the two conditional response paths of the shared
//     AHB slave interface wrapper src/libs/rtl/ahb_slv_sif.sv:
//       - the FAULT path (hresp=H_ERROR, 2-cycle), driven when a peripheral
//         asserts its `err` input.
//       - the HOLD path (hreadyout_o low wait-state), driven when a peripheral
//         asserts its `hld` input. The transaction still completes OKAY, so
//         these accesses do NOT fault the core.
//
//     IMPORTANT (how the fault is delivered):
//     These faulting targets all live in the external AHB peripheral window.
//     In VeeR EL2 every external load is issued through the non-blocking load
//     CAM, so an hresp error returns *after* the access has retired and is
//     reported as an *imprecise* D-bus NMI (mcause 0xF0000001 for a load,
//     0xF0000000 for a store), NOT a synchronous mtvec access-fault. The NMI
//     redirects to SOC_IFC INTERNAL_NMI_VECTOR, and the first imprecise error
//     latches mdseac and suppresses further capture until mdeau is written, so
//     the handler must clear mdeau to re-arm for the next faulting access.
//
//     A per-peripheral RTL survey established which blocks actually route a
//     live `err`/`hld` back into ahb_slv_sif from firmware-reachable accesses
//     (many candidate ports are tied to 1'b0 in RTL):
//
//     FAULT path (deterministically reachable from FW):
//       - soc_ifc : access to an address inside the soc_ifc window that maps to
//                   no sub-client (mbox / soc_ifc_reg / sha_acc / dma) asserts
//                   uc_error (soc_ifc_arb.sv). This is a valid, designed SLVERR
//                   response to an unmapped access (see soc_ifc_top.sv, the
//                   removed ERR_SOC_IFC_AHB_ERR note).
//       - csrng   : access to an unmapped register offset asserts addrmiss ->
//                   reg_error (csrng_reg_top.sv, AW=7).
//       - entropy_src : same addrmiss -> reg_error (entropy_src_reg_top.sv, AW=8).
//       - aes     : access to an unmapped AES-core (TLUL) offset -> addrmiss ->
//                   reg_error -> tlul d_error -> ahb_err (aes_reg_top.sv, AW=8).
//       - kmac/sha3 : access to an unmapped KMAC-core (TLUL) offset -> addrmiss
//                   -> reg_error -> tlul d_error -> ahb_err (kmac_reg_top.sv).
//
//     HOLD path (deterministically reachable from FW):
//       - aes     : any access to a valid AES-core (TLUL) register asserts
//                   ahb_hold for the TLUL request/response round-trip
//                   (caliptra_tlul_adapter_vh hld_o).
//       - kmac/sha3 : same TLUL round-trip wait-state on a valid KMAC-core reg.
//
//     Blocks whose err/hld are tied off (no firmware-reachable stimulus) are
//     logged and skipped: ecc, keyvault, pcrvault, datavault, sha256, sha512,
//     entropy_combiner (err tied 0 and/or hld tied 0); doe, hmac (both tied 0).
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

// ---------------------------------------------------------------------
// FAULT-path target addresses. Each access to these addresses asserts the
// corresponding peripheral's ahb_slv_sif `err` input, producing hresp=H_ERROR
// and an imprecise D-bus NMI in the core.
// ---------------------------------------------------------------------
// soc_ifc window is 0x3000_0000-0x3007_FFFF; offset 0x0_0000 maps to no
// sub-client (mbox=0x2_0000, sha_acc=0x2_1000, dma=0x2_2000, soc_ifc_reg=
// 0x3_0000, mbox_sram=0x4_0000) -> uc_error.
#define FLT_ADDR_SOC_IFC     (CLP_SOC_IFC_REG_BASE_ADDR - 0x30000UL) /* 0x30000000 */
// csrng reg block AW=7 (0x00-0x7F); last register MAIN_SM_STATE=0x5C. Offset
// 0x60 is an unmapped hole -> addrmiss -> reg_error.
#define FLT_ADDR_CSRNG       (CLP_CSRNG_REG_BASE_ADDR + 0x60UL)      /* 0x20002060 */
// entropy_src reg block AW=8 (0x00-0xFF); last register MAIN_SM_STATE=0xE0.
// Offset 0xF0 is an unmapped hole -> addrmiss -> reg_error.
#define FLT_ADDR_ENTROPY_SRC (CLP_ENTROPY_SRC_REG_BASE_ADDR + 0xF0UL)/* 0x200030F0 */
// AES-core TLUL space is offset < 0x800 within the AES window; AES-core AW=8,
// last register CTRL_GCM_SHADOWED=0x88. Offset 0x8C is unmapped -> addrmiss ->
// reg_error -> tlul d_error -> ahb_err.
#define FLT_ADDR_AES         (CLP_AES_REG_BASE_ADDR + 0x8CUL)        /* 0x1001108C */
// KMAC-core TLUL space is offset < 0x1000 within the sha3 window; KMAC config
// registers end at ERR_CODE=0x4C and the next mapped region is the STATE window
// at 0x400. Offset 0x50 is unmapped -> addrmiss -> reg_error -> tlul d_error ->
// ahb_err.
#define FLT_ADDR_KMAC        (CLP_KMAC_BASE_ADDR + 0x50UL)           /* 0x10040050 */

// ---------------------------------------------------------------------
// HOLD-path target addresses. Ordinary reads of these VALID core registers
// traverse the TLUL request/response handshake, asserting ahb_hold (hreadyout
// wait-state) for the round-trip. The transactions complete OKAY (no fault).
// ---------------------------------------------------------------------
#define HOLD_ADDR_AES        (CLP_AES_REG_STATUS)                    /* 0x10011084 */
#define HOLD_ADDR_KMAC       (CLP_KMAC_STATUS)                       /* 0x1004001C */

// Flat list of faulting operations: a read and a write to each of the 5 FAULT
// peripherals (2 * 5 = 10). Both directions assert `err` and are expected to
// raise an imprecise D-bus NMI.
typedef struct { const char *name; uintptr_t addr; uint8_t is_write; } fault_op_t;
static const fault_op_t FAULT_OPS[] = {
    {"soc_ifc  rd", FLT_ADDR_SOC_IFC,     0}, {"soc_ifc  wr", FLT_ADDR_SOC_IFC,     1},
    {"csrng    rd", FLT_ADDR_CSRNG,       0}, {"csrng    wr", FLT_ADDR_CSRNG,       1},
    {"entropy  rd", FLT_ADDR_ENTROPY_SRC, 0}, {"entropy  wr", FLT_ADDR_ENTROPY_SRC, 1},
    {"aes      rd", FLT_ADDR_AES,         0}, {"aes      wr", FLT_ADDR_AES,         1},
    {"kmac     rd", FLT_ADDR_KMAC,        0}, {"kmac     wr", FLT_ADDR_KMAC,        1},
};
#define NUM_FAULT_OPS (sizeof(FAULT_OPS) / sizeof(FAULT_OPS[0]))

// Index of the next faulting op and count of NMIs observed. Advanced by the NMI
// handler and read back in run_faults(); execution resumes in-place (no reset).
volatile uint32_t g_fault_idx   = 0;
volatile uint32_t g_fault_count = 0;

void run_faults(void);

// Force the faulting accesses to be 4-byte (non-compressed) lw/sw so the bus
// transaction (and thus the ahb_slv_sif stimulus) is an explicit 32-bit access.
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

// NMI handler installed at SOC_IFC INTERNAL_NMI_VECTOR. Only the expected
// imprecise D-bus NMI (top nibble of mcause = 0xF, covers both load and store)
// is tolerated: count it, clear the error state (mcause + mdeau to re-arm
// mdseac capture), advance to the next op, and redirect mepc so the (implicit)
// mret resumes at run_faults(). The imprecise mepc is meaningless, so we
// restart from a known point rather than resuming it.
void __attribute__((interrupt("machine"), aligned(4))) nmi_handler(void) {
    uint_xlen_t cause = csr_read_mcause();
    if ((cause & MCAUSE_NMI_BIT_MASK) == MCAUSE_NMI_BIT_MASK) {
        g_fault_count++;
        g_fault_idx++;
        csr_write_mcause(0x0);
        csr_write_mdeau(0x0);
        csr_write_mepc((uintptr_t)run_faults);
    } else {
        VPRINTF(FATAL, "Unexpected trap in hold/fault test: mcause=%x mepc=%x\n",
                (uint32_t)cause, (uint32_t)csr_read_mepc());
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
}

// Walk the remaining faulting ops. Each op asserts the peripheral `err`, which
// raises an imprecise D-bus NMI; the handler advances g_fault_idx and resumes
// here, so the loop re-reads the updated index and continues.
void run_faults(void) {
    while (g_fault_idx < NUM_FAULT_OPS) {
        uint32_t i = g_fault_idx;
        VPRINTF(LOW, "AHB fault path: %s addr=0x%08x\n", FAULT_OPS[i].name, (uint32_t)FAULT_OPS[i].addr);
        if (FAULT_OPS[i].is_write)
            fault_sw(FAULT_OPS[i].addr, 0xDEADBEEF);
        else
            (void)fault_lw(FAULT_OPS[i].addr);

        // The imprecise error normally raises an NMI within a few cycles, and
        // the handler restarts run_faults() with g_fault_idx advanced, so we do
        // not fall through. Give the error time to drain; if no NMI arrives the
        // op failed to fault and the test must fail.
        for (volatile uint32_t k = 0; k < 4000; k++) { }
        VPRINTF(FATAL, "[FAIL] no NMI for fault op idx=%u addr=0x%08x (count=%u)\n",
                i, (uint32_t)FAULT_OPS[i].addr, (uint32_t)g_fault_count);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    if (g_fault_count != NUM_FAULT_OPS) {
        VPRINTF(FATAL, "[FAIL] fault count mismatch: got=%u expected=%u\n",
                (uint32_t)g_fault_count, (uint32_t)NUM_FAULT_OPS);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    VPRINTF(LOW, "AHB hold/fault complete (fault_count=%u)\n", (uint32_t)g_fault_count);
    SEND_STDOUT_CTRL(0xff); // PASS
    while (1);
}

// Exercise one HOLD target: a normal mapped read that induces a wait-state
// (asserts the peripheral `hld`) but completes OKAY, so it does not fault.
static void hold_access(const char *name, uintptr_t addr) {
    uint32_t v = lsu_read_32(addr);
    VPRINTF(LOW, "AHB hold path: %s addr=0x%08x rdata=0x%08x (no fault)\n", name, (uint32_t)addr, v);
}

void main(void) {
    VPRINTF(LOW, "----------------------------------\nAHB HOLD / FAULT Directed Test !!\n----------------------------------\n");

    // Standard interrupt/CSR init.
    init_interrupts();

    // External AHB error responses arrive as imprecise D-bus NMIs, so route them
    // to a test-local handler instead of letting them escalate to a hang/reset.
    lsu_write_32((uintptr_t)(CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR), (uint32_t)nmi_handler);

    // -----------------------------------------------------------------
    // HOLD phase (no faults). TLUL-backed AES and KMAC core register reads
    // assert ahb_hold for the request/response round-trip. These are the
    // firmware-reachable holds in this design (the vault blocks tie hld to 0).
    // -----------------------------------------------------------------
    VPRINTF(LOW, "-- HOLD (wait-state) path --\n");
    hold_access("aes ",  HOLD_ADDR_AES);
    hold_access("kmac",  HOLD_ADDR_KMAC);

    // -----------------------------------------------------------------
    // Blocks whose ahb_slv_sif err/hld are tied off in RTL (no firmware
    // stimulus) are intentionally skipped and logged for the record.
    // -----------------------------------------------------------------
    VPRINTF(LOW, "-- skipped (fault/hold tied off in RTL) --\n");
    VPRINTF(LOW, "  ecc/kv/pv/dv/sha256/sha512: reg rd/wr fault tied 0; hld tied 0\n");
    VPRINTF(LOW, "  entropy_combiner: fault tied 0, hld tied 0; doe/hmac: fault+hld tied 0\n");

    // -----------------------------------------------------------------
    // FAULT phase. Each op raises an imprecise D-bus NMI serviced by
    // nmi_handler above, which advances the index and resumes run_faults().
    // -----------------------------------------------------------------
    VPRINTF(LOW, "-- FAULT (hresp) path --\n");
    run_faults();
}
