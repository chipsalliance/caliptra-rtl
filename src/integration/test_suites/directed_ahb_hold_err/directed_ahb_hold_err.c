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
//       - the ERROR path (hresp=H_ERROR, 2-cycle), driven when a peripheral
//         asserts its `err` input. This FAULTS the RISC-V core (load/store
//         access-fault).
//       - the HOLD path (hreadyout_o low wait-state), driven when a peripheral
//         asserts its `hld` input. The transaction still completes OKAY, so
//         these accesses do NOT fault the core.
//
//     A per-peripheral RTL survey established which blocks actually route a
//     live `err`/`hld` back into ahb_slv_sif from firmware-reachable accesses
//     (many candidate ports are tied to 1'b0 in RTL):
//
//     ERROR path (deterministically reachable from FW):
//       - soc_ifc : access to an address inside the soc_ifc window that maps to
//                   no sub-client (mbox / soc_ifc_reg / sha_acc / dma) asserts
//                   uc_error (soc_ifc_arb.sv).
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
//
//     The ERROR accesses are performed with a test-local mtvec DIRECT-mode
//     handler installed around them (mirrors directed_ahb_addr_toggle) so the
//     shared caliptra_isr.c default handler is not involved. The handler accepts
//     load/store access-faults, advances mepc past the forced 4-byte lw/sw, and
//     counts the fault; any other trap kills the sim. The HOLD accesses are
//     ordinary mapped reads performed OUTSIDE the handler window (they do not
//     fault).
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

// ---------------------------------------------------------------------
// ERROR-path target addresses. Each access to these addresses asserts the
// corresponding peripheral's ahb_slv_sif `err` input, producing hresp=H_ERROR
// and a RISC-V load/store access-fault.
// ---------------------------------------------------------------------
// soc_ifc window is 0x3000_0000-0x3007_FFFF; offset 0x0_0000 maps to no
// sub-client (mbox=0x2_0000, sha_acc=0x2_1000, dma=0x2_2000, soc_ifc_reg=
// 0x3_0000, mbox_sram=0x4_0000) -> uc_error.
#define ERR_ADDR_SOC_IFC     (CLP_SOC_IFC_REG_BASE_ADDR - 0x30000UL) /* 0x30000000 */
// csrng reg block AW=7 (0x00-0x7F); last register MAIN_SM_STATE=0x5C. Offset
// 0x60 is an unmapped hole -> addrmiss -> reg_error.
#define ERR_ADDR_CSRNG       (CLP_CSRNG_REG_BASE_ADDR + 0x60UL)      /* 0x20002060 */
// entropy_src reg block AW=8 (0x00-0xFF); last register MAIN_SM_STATE=0xE0.
// Offset 0xF0 is an unmapped hole -> addrmiss -> reg_error.
#define ERR_ADDR_ENTROPY_SRC (CLP_ENTROPY_SRC_REG_BASE_ADDR + 0xF0UL)/* 0x200030F0 */
// AES-core TLUL space is offset < 0x800 within the AES window; AES-core AW=8,
// last register CTRL_GCM_SHADOWED=0x88. Offset 0x8C is unmapped -> addrmiss ->
// reg_error -> tlul d_error -> ahb_err.
#define ERR_ADDR_AES         (CLP_AES_REG_BASE_ADDR + 0x8CUL)        /* 0x1001108C */
// KMAC-core TLUL space is offset < 0x1000 within the sha3 window; KMAC config
// registers end at ERR_CODE=0x4C and the next mapped region is the STATE window
// at 0x400. Offset 0x50 is unmapped -> addrmiss -> reg_error -> tlul d_error ->
// ahb_err.
#define ERR_ADDR_KMAC        (CLP_KMAC_BASE_ADDR + 0x50UL)           /* 0x10040050 */

// Two faults (read + write) are expected for each of the 5 ERROR peripherals.
#define EXPECTED_FAULT_COUNT 10

// ---------------------------------------------------------------------
// HOLD-path target addresses. Ordinary reads of these VALID core registers
// traverse the TLUL request/response handshake, asserting ahb_hold (hreadyout
// wait-state) for the round-trip. The transactions complete OKAY (no fault).
// ---------------------------------------------------------------------
#define HOLD_ADDR_AES        (CLP_AES_REG_STATUS)                    /* 0x10011084 */
#define HOLD_ADDR_KMAC       (CLP_KMAC_STATUS)                       /* 0x1004001C */

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
        VPRINTF(FATAL, "Unexpected trap in ahb_hold_err: mcause=%x mepc=%x\n", (uint32_t)cause, (uint32_t)csr_read_mepc());
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

// Exercise one ERROR target: a read (drives the peripheral `err`, faults) and a
// write (drives `err`, faults). Each is expected to increment the fault count.
static void err_access(const char *name, uintptr_t addr) {
    VPRINTF(LOW, "AHB err path: %s addr=0x%08x (expect 2 faults)\n", name, (uint32_t)addr);
    (void)fault_lw(addr);       // load access-fault
    fault_sw(addr, 0xDEADBEEF); // store access-fault
}

// Exercise one HOLD target: a normal mapped read that induces a wait-state
// (asserts the peripheral `hld`) but completes OKAY, so it does not fault.
static void hold_access(const char *name, uintptr_t addr) {
    uint32_t v = lsu_read_32(addr);
    VPRINTF(LOW, "AHB hold path: %s addr=0x%08x rdata=0x%08x (no fault)\n", name, (uint32_t)addr, v);
}

void main(void) {
    uint_xlen_t saved_mtvec;

    VPRINTF(LOW, "----------------------------------\nAHB HOLD / ERROR Directed Test !!\n----------------------------------\n");

    // Setup the interrupt CSR configuration (standard test init). This brings
    // the shared caliptra_isr vectored handler online; the test-local DIRECT
    // handler below temporarily overrides it only for the ERROR accesses.
    init_interrupts();

    // -----------------------------------------------------------------
    // HOLD phase (performed OUTSIDE the local handler window; no faults).
    // TLUL-backed AES and KMAC core register reads assert ahb_hold for the
    // request/response round-trip. These are the firmware-reachable holds in
    // this design (the vault blocks tie their hld input to 1'b0).
    // -----------------------------------------------------------------
    VPRINTF(LOW, "-- HOLD (wait-state) path --\n");
    hold_access("aes ",  HOLD_ADDR_AES);
    hold_access("kmac",  HOLD_ADDR_KMAC);

    // -----------------------------------------------------------------
    // ERROR phase. Save the current trap vector and install the test-local
    // handler in DIRECT mode (low 2 bits = 0). Exceptions do not require
    // mstatus.MIE.
    // -----------------------------------------------------------------
    VPRINTF(LOW, "-- ERROR (hresp) path --\n");
    saved_mtvec = csr_read_mtvec();
    csr_write_mtvec(((uintptr_t)ahb_fault_handler) & ~0x3UL);

    err_access("soc_ifc    ", ERR_ADDR_SOC_IFC);
    err_access("csrng      ", ERR_ADDR_CSRNG);
    err_access("entropy_src", ERR_ADDR_ENTROPY_SRC);
    err_access("aes        ", ERR_ADDR_AES);
    err_access("kmac/sha3  ", ERR_ADDR_KMAC);

    // Restore the original trap vector before evaluating results.
    csr_write_mtvec(saved_mtvec);

    // -----------------------------------------------------------------
    // Blocks whose ahb_slv_sif err/hld are tied off in RTL (no firmware
    // stimulus) are intentionally skipped and logged for the record.
    // -----------------------------------------------------------------
    VPRINTF(LOW, "-- skipped (err/hld tied off in RTL) --\n");
    VPRINTF(LOW, "  ecc/kv/pv/dv/sha256/sha512: reg rd/wr err tied 0; hld tied 0\n");
    VPRINTF(LOW, "  entropy_combiner: err tied 0, hld tied 0; doe/hmac: err+hld tied 0\n");
    VPRINTF(LOW, "  csrng/entropy_src/soc_ifc hold: shadow/arb only, not reliably FW-driven\n");

    // Verify we observed exactly the expected number of access-faults.
    if (g_expected_fault_count != EXPECTED_FAULT_COUNT) {
        VPRINTF(FATAL, "[FAIL] fault count mismatch: got=%u expected=%u\n",
                (uint32_t)g_expected_fault_count, (uint32_t)EXPECTED_FAULT_COUNT);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    VPRINTF(LOW, "AHB hold/err complete (fault_count=%u)\n", (uint32_t)g_expected_fault_count);

    // Signal PASS
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
