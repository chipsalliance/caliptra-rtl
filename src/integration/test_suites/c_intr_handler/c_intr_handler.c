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
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"


//int whisperPrintf(const char* format, ...);
//#define ee_printf whisperPrintf


volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

//TODO: Fix this since ISR is not currently populating these variables.
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// ---------------------------------------------------------------------------
// INTR_BLOCK_RF register-file sweep (coverage helper)
// ---------------------------------------------------------------------------
// Every peripheral instantiates the identical interrupt register-file
// (see src/libs/rtl/interrupt_regs.rdl). Offsets from the GLOBAL_INTR_EN_R
// base address (== INTR_BLOCK_RF_START) are the same for all blocks:
#define INTR_RF_GLOBAL_EN_OFF   0x000  // GLOBAL_INTR_EN_R      (sw=rw)
#define INTR_RF_ERROR_EN_OFF    0x004  // ERROR_INTR_EN_R       (sw=rw)
#define INTR_RF_NOTIF_EN_OFF    0x008  // NOTIF_INTR_EN_R       (sw=rw)
#define INTR_RF_ERROR_STS_OFF   0x014  // ERROR_INTERNAL_INTR_R (sw=rw, woclr / W1C)
#define INTR_RF_NOTIF_STS_OFF   0x018  // NOTIF_INTERNAL_INTR_R (sw=rw, woclr / W1C)
#define INTR_RF_ERROR_TRIG_OFF  0x01c  // ERROR_INTR_TRIG_R     (sw=rw, woset singlepulse)
#define INTR_RF_NOTIF_TRIG_OFF  0x020  // NOTIF_INTR_TRIG_R     (sw=rw, woset singlepulse)
#define INTR_RF_ERROR_CNT_OFF   0x100  // first ERROR *_INTR_COUNT_R      (sw=rw counter)
#define INTR_RF_NOTIF_CNT_OFF   0x180  // first NOTIF *_INTR_COUNT_R      (sw=rw counter)
#define INTR_RF_ERROR_INCR_OFF  0x200  // first ERROR *_INTR_COUNT_INCR_R (sw=r read-only)

// GLOBAL_INTR_EN_R (== INTR_BLOCK_RF_START) base address for all 12 blocks.
static const uint32_t intr_rf_base[] = {
    CLP_DOE_REG_INTR_BLOCK_RF_START,
    CLP_ECC_REG_INTR_BLOCK_RF_START,
    CLP_HMAC_REG_INTR_BLOCK_RF_START,
    CLP_SHA512_REG_INTR_BLOCK_RF_START,
    CLP_SHA256_REG_INTR_BLOCK_RF_START,
    CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_START,
    CLP_SOC_IFC_REG_INTR_BLOCK_RF_START,
    CLP_ABR_REG_INTR_BLOCK_RF_START,
    CLP_AES_CLP_REG_INTR_BLOCK_RF_START,
    CLP_AXI_DMA_REG_INTR_BLOCK_RF_START,
    CLP_ENTROPY_COMBINER_REG_INTR_BLOCK_RF_START,
    CLP_SHA3_INTR_BLOCK_RF_START
};

// Varied patterns to drive both directions of every hwdata/hrdata bit line.
static const uint32_t intr_rf_patterns[] = {
    0x00000000, 0xFFFFFFFF, 0xAAAAAAAA, 0x55555555
};

// Sweep every peripheral INTR_BLOCK_RF for coverage: write varied patterns to
// each RW register and read them back (toggling the AHB hwdata/hrdata buses in
// both directions), and exercise the interrupt counters so the counter read
// data varies. MUST be called with global interrupts disabled (mstatus.MIE=0)
// so the ISR is not invoked by the status bits set via the trigger registers.
static void intr_block_rf_sweep(void) {
    // RW registers to walk with every pattern (EN + TRIG registers).
    static const uint32_t rw_off[] = {
        INTR_RF_GLOBAL_EN_OFF, INTR_RF_ERROR_EN_OFF, INTR_RF_NOTIF_EN_OFF,
        INTR_RF_ERROR_TRIG_OFF, INTR_RF_NOTIF_TRIG_OFF
    };
    const uint32_t nblk = sizeof(intr_rf_base) / sizeof(intr_rf_base[0]);
    const uint32_t npat = sizeof(intr_rf_patterns) / sizeof(intr_rf_patterns[0]);
    const uint32_t nrw  = sizeof(rw_off) / sizeof(rw_off[0]);

    VPRINTF(LOW, "INTR_BLOCK_RF register sweep start (%x blocks)\n", nblk);

    for (uint32_t b = 0; b < nblk; b++) {
        uint32_t base = intr_rf_base[b];
        VPRINTF(MEDIUM, "INTR_BLOCK_RF sweep base=%x\n", base);

        // Drive every RW register with all patterns and read each back. This
        // toggles the write (hwdata) and read (hrdata) bus lines in both
        // directions. Only implemented bits latch; the bus still toggles.
        for (uint32_t r = 0; r < nrw; r++) {
            for (uint32_t p = 0; p < npat; p++) {
                lsu_write_32(base + rw_off[r], intr_rf_patterns[p]);
                (void) lsu_read_32(base + rw_off[r]);
            }
        }

        // Exercise the counters. The COUNT_R registers are sw=rw, so write
        // several varied values and read them back to vary the counter read
        // data on the hrdata bus.
        for (uint32_t p = 0; p < npat; p++) {
            lsu_write_32(base + INTR_RF_ERROR_CNT_OFF, intr_rf_patterns[p]);
            (void) lsu_read_32(base + INTR_RF_ERROR_CNT_OFF);
            lsu_write_32(base + INTR_RF_NOTIF_CNT_OFF, ~intr_rf_patterns[p]);
            (void) lsu_read_32(base + INTR_RF_NOTIF_CNT_OFF);
        }
        // A walking pattern for good measure, then read back.
        lsu_write_32(base + INTR_RF_ERROR_CNT_OFF, 0xDEADBEEF);
        lsu_write_32(base + INTR_RF_NOTIF_CNT_OFF, 0x21524110);
        (void) lsu_read_32(base + INTR_RF_ERROR_CNT_OFF);
        (void) lsu_read_32(base + INTR_RF_NOTIF_CNT_OFF);

        // The *_INTR_COUNT_INCR_R registers are sw=r (read-only); the write is
        // a harmless no-op that still toggles the hwdata bus, and the read
        // toggles the hrdata bus.
        for (uint32_t p = 0; p < npat; p++) {
            lsu_write_32(base + INTR_RF_ERROR_INCR_OFF, intr_rf_patterns[p]);
            (void) lsu_read_32(base + INTR_RF_ERROR_INCR_OFF);
        }

        // Clean up: W1C any status bits set via the trigger writes, zero the
        // counters we scribbled on, and restore all enables to 0 so the
        // machine is left in a clean state.
        lsu_write_32(base + INTR_RF_ERROR_STS_OFF, 0xFFFFFFFF);
        lsu_write_32(base + INTR_RF_NOTIF_STS_OFF, 0xFFFFFFFF);
        lsu_write_32(base + INTR_RF_ERROR_CNT_OFF, 0x00000000);
        lsu_write_32(base + INTR_RF_NOTIF_CNT_OFF, 0x00000000);
        lsu_write_32(base + INTR_RF_ERROR_EN_OFF,  0x00000000);
        lsu_write_32(base + INTR_RF_NOTIF_EN_OFF,  0x00000000);
        lsu_write_32(base + INTR_RF_GLOBAL_EN_OFF, 0x00000000);
    }

    VPRINTF(LOW, "INTR_BLOCK_RF register sweep done\n");
}

// ---------------------------------------------------------------------------
// generic_input_wires toggle-coverage phase
// ---------------------------------------------------------------------------
// TB command 0x96 asks the SoC BFM (caliptra_top_tb_soc_bfm.sv) to drive
// generic_input_wires with a FW-specified 64-bit value. Because
// CPTRA_GENERIC_OUTPUT_WIRES_0 is the STDOUT / command channel (its low byte is
// decoded as the control code), the 64-bit data is passed 32 bits at a time via
// CPTRA_GENERIC_OUTPUT_WIRES_1:
//   *STDOUT = (0x00 << 8) | 0x96 : latch low  32 bits from OUTPUT_WIRES_1
//   *STDOUT = (0x01 << 8) | 0x96 : latch high 32 bits from OUTPUT_WIRES_1 and drive
// The BFM then holds generic_input_wires until the next update; FW reads back via
// CPTRA_GENERIC_INPUT_WIRES_0/_1.
#define GEN_IN_WIRES_CMD  0x96

static void drive_generic_input_wires(uint32_t hi, uint32_t lo) {
    // Latch low half (sub-code 0x00)
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, lo);
    *((volatile uint32_t *)STDOUT) = (0x00 << 8) | GEN_IN_WIRES_CMD;
    // Latch high half and drive (sub-code 0x01)
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, hi);
    *((volatile uint32_t *)STDOUT) = (0x01 << 8) | GEN_IN_WIRES_CMD;
}

// Poll the input wires until they reflect the driven value; gives the BFM a few
// cycles to react to the command before reading back.
static int wait_generic_input_wires(uint32_t exp_hi, uint32_t exp_lo) {
    for (int i = 0; i < 2000; i++) {
        uint32_t lo = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
        uint32_t hi = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1);
        if ((lo == exp_lo) && (hi == exp_hi)) {
            return 1;
        }
    }
    return 0;
}

static void generic_input_wires_toggle_phase(volatile uint32_t *gen_in_toggle_ctr) {
    static const uint32_t patterns[][2] = {
        // {high, low}
        {0xFFFFFFFF, 0xFFFFFFFF},  // 0 -> 1 on all 64 bits
        {0x00000000, 0x00000000},  // 1 -> 0 on all 64 bits
        {0x5A5A5A5A, 0xA5A5A5A5},  // alternating pattern, distinct halves
    };
    const int num_patterns = sizeof(patterns) / sizeof(patterns[0]);
    uint32_t toggle_base = *gen_in_toggle_ctr;

    VPRINTF(LOW, "generic_input_wires toggle phase: baseline gen_in_toggle count=0x%08x\n", toggle_base);

    for (int p = 0; p < num_patterns; p++) {
        uint32_t hi = patterns[p][0];
        uint32_t lo = patterns[p][1];
        drive_generic_input_wires(hi, lo);
        if (!wait_generic_input_wires(hi, lo)) {
            uint32_t rlo = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
            uint32_t rhi = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1);
            VPRINTF(FATAL, "[FAIL] generic_input_wires mismatch: got=0x%08x_%08x expected=0x%08x_%08x\n",
                    rhi, rlo, hi, lo);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        VPRINTF(LOW, "generic_input_wires drove 0x%08x_%08x (readback ok)\n", hi, lo);
    }

    // Each of the programmed values differs from the previous one, so the
    // NOTIF_GEN_IN_TOGGLE hardware counter must have advanced by at least that
    // many distinct changes.
    uint32_t toggle_after = *gen_in_toggle_ctr;
    if (toggle_after < (toggle_base + num_patterns)) {
        VPRINTF(FATAL, "[FAIL] gen_in_toggle count did not advance enough: before=0x%08x after=0x%08x (expected >= +%d)\n",
                toggle_base, toggle_after, num_patterns);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    VPRINTF(LOW, "generic_input_wires toggle phase PASS: gen_in_toggle count 0x%08x -> 0x%08x\n",
            toggle_base, toggle_after);
}

void main(void) {
        int argc=0;
        char *argv[1];

        volatile uint32_t * doe_notif_trig        = (uint32_t *) (CLP_DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * ecc_notif_trig        = (uint32_t *) (CLP_ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * hmac_notif_trig       = (uint32_t *) (CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * hmac_error_trig       = (uint32_t *) (CLP_HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R);
        volatile uint32_t * sha512_notif_trig     = (uint32_t *) (CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * sha256_notif_trig     = (uint32_t *) (CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * sha512_acc_notif_trig = (uint32_t *) (CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * soc_ifc_error_trig    = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R);
        volatile uint32_t * soc_ifc_notif_trig    = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * abr_notif_trig        = (uint32_t *) (CLP_ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * axi_dma_notif_trig    = (uint32_t *) (CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * sha3_notif_trig       = (uint32_t *) (CLP_SHA3_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * aes_notif_trig        = (uint32_t *) (CLP_AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);

        volatile uint32_t * sha512_notif_ctr         = (uint32_t *) (CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
        volatile uint32_t * sha256_notif_ctr         = (uint32_t *) (CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
        volatile uint32_t * sha512_acc_notif_ctr     = (uint32_t *) (CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
        volatile uint32_t * hmac_notif_ctr           = (uint32_t *) (CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
        volatile uint32_t * hmac_error_key_mode_ctr  = (uint32_t *) (CLP_HMAC_REG_INTR_BLOCK_RF_KEY_MODE_ERROR_INTR_COUNT_R);
        volatile uint32_t * hmac_error_key_zero_ctr  = (uint32_t *) (CLP_HMAC_REG_INTR_BLOCK_RF_KEY_ZERO_ERROR_INTR_COUNT_R);        
        volatile uint32_t * ecc_notif_ctr            = (uint32_t *) (CLP_ECC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
        volatile uint32_t * doe_notif_ctr            = (uint32_t *) (CLP_DOE_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_internal_ctr     = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_inv_dev_ctr      = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_cmd_fail_ctr     = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_bad_fuse_ctr     = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_iccm_blocked_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_mbox_ecc_unc_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_wdt_timer1_timeout_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_wdt_timer2_timeout_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_notif_cmd_avail_ctr     = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_notif_mbox_ecc_cor_ctr  = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_notif_debug_locked_ctr  = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_notif_scan_mode_ctr     = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_notif_soc_req_lock_ctr  = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_notif_gen_in_toggle_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R);
        volatile uint32_t * abr_notif_ctr            = (uint32_t *) (CLP_ABR_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
        volatile uint32_t * axi_dma_notif_ctr        = (uint32_t *) (CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_TXN_DONE_INTR_COUNT_R);
        volatile uint32_t * sha3_notif_ctr           = (uint32_t *) (CLP_SHA3_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
        volatile uint32_t * aes_notif_ctr            = (uint32_t *) (CLP_AES_CLP_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);

        uint32_t sha512_intr_count = 0;
        uint32_t sha256_intr_count = 0;
        uint32_t sha512_acc_intr_count = 0;
        uint32_t hmac_notif_intr_count = 0;
        uint32_t hmac_error_intr_count = 0;
        uint32_t hmac_error_intr_count_hw = 0;
        uint32_t ecc_intr_count = 0;
        uint32_t doe_intr_count = 0;
        uint32_t soc_ifc_notif_intr_count = 0;
        uint32_t soc_ifc_notif_intr_count_hw = 0;
        uint32_t soc_ifc_error_intr_count = 0;
        uint32_t soc_ifc_error_intr_count_hw = 0;
        uint32_t abr_intr_count = 0;
        uint32_t axi_dma_intr_count = 0;
        uint32_t sha3_intr_count = 0;
        uint32_t aes_intr_count = 0;
        uint64_t mtime = 0;

        VPRINTF(LOW,"----------------------------------\nCaliptra: Direct ISR Test!!\n----------------------------------\n");

        // Setup the interrupt CSR configuration
        init_interrupts();

        // Zero every HW interrupt COUNT register this test compares against its
        // FW-tracked counts. These counters are sw=rw and persist across a test
        // re-run; intr_block_rf_sweep() also pulses the TRIG registers, which
        // increments the 2nd+ error/notif counters of multi-source blocks (e.g.
        // HMAC KEY_ZERO, SoC_IFC) that its cleanup does not clear. Establish a
        // known-zero baseline so each pass's HW counts match the FW counts.
        volatile uint32_t * const intr_counters[] = {
            sha512_notif_ctr, sha256_notif_ctr, sha512_acc_notif_ctr, hmac_notif_ctr,
            hmac_error_key_mode_ctr, hmac_error_key_zero_ctr, ecc_notif_ctr, doe_notif_ctr,
            soc_ifc_error_internal_ctr, soc_ifc_error_inv_dev_ctr, soc_ifc_error_cmd_fail_ctr,
            soc_ifc_error_bad_fuse_ctr, soc_ifc_error_iccm_blocked_ctr, soc_ifc_error_mbox_ecc_unc_ctr,
            soc_ifc_error_wdt_timer1_timeout_ctr, soc_ifc_error_wdt_timer2_timeout_ctr,
            soc_ifc_notif_cmd_avail_ctr, soc_ifc_notif_mbox_ecc_cor_ctr, soc_ifc_notif_debug_locked_ctr,
            soc_ifc_notif_scan_mode_ctr, soc_ifc_notif_soc_req_lock_ctr, soc_ifc_notif_gen_in_toggle_ctr,
            abr_notif_ctr, axi_dma_notif_ctr, sha3_notif_ctr, aes_notif_ctr
        };
        for (uint32_t i = 0; i < sizeof(intr_counters)/sizeof(intr_counters[0]); i++) {
            *intr_counters[i] = 0;
        }

        // Initialize the counter
        intr_count = 0;

        // Busy loop
        while (intr_count < 64) {
            // Trigger interrupt manually
            // The modulo defines the round-robin period across all trigger
            // slots. Widened from 0x18 to 0x19 to add 1 new slot (0x18=aes)
            // above the existing sha3 slot (0x17).
            if ((intr_count % 0x19) >= 0x18) { //18
                *aes_notif_trig = AES_CLP_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                aes_intr_count++;
            } else if ((intr_count % 0x19) >= 0x17) { //17
                *sha3_notif_trig = SHA3_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                sha3_intr_count++;
            } else if ((intr_count % 0x19) >= 0x16) { //16
                *axi_dma_notif_trig = AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_TXN_DONE_TRIG_MASK;
                axi_dma_intr_count++;
            } else if ((intr_count % 0x19) >= 0x15) { //15
                *abr_notif_trig = ABR_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                abr_intr_count++;
            } else if ((intr_count % 0x19) >= 0x14) { //14
                *hmac_error_trig = 1 << (intr_count % 0x2);
                hmac_error_intr_count++;
            } else if ((intr_count % 0x19) >= 0x12) {
                *sha512_notif_trig = SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                sha512_intr_count++;
            } else if ((intr_count % 0x19) >= 0x11) {
                *sha256_notif_trig = SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                sha256_intr_count++;
            } else if ((intr_count % 0x19) >= 0x10) {
                *sha512_acc_notif_trig = SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                sha512_acc_intr_count++;
            } else if ((intr_count % 0x19) >= 0x0F) {
                *hmac_notif_trig = HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                hmac_notif_intr_count++;
            } else if ((intr_count % 0x19) >= 0x0E) {
                *ecc_notif_trig = ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                ecc_intr_count++;
            } else if ((intr_count % 0x19) >= 0x0D) {
                *doe_notif_trig = DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                doe_intr_count++;
            } else if ((intr_count % 0x19) >= 0x08) { //8-C
                *soc_ifc_notif_trig = 1 << (intr_count % 0x5);
                soc_ifc_notif_intr_count++;
            } else { //0-7
                *soc_ifc_error_trig = 1 << (intr_count % 0x8);
                soc_ifc_error_intr_count++;
            }
            __asm__ volatile ("wfi"); // "Wait for interrupt"
            // Sleep in between triggers to allow ISR to execute and show idle time in sims
            for (uint16_t slp = 0; slp < 100; slp++) {
                __asm__ volatile ("nop"); // Sleep loop as "nop"
            }
        }

        // Disable interrutps
        csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

        // Print interrupt count from FW/HW trackers
        // SHA512
        VPRINTF(MEDIUM, "SHA512 fw count: %x\n", sha512_intr_count);
        VPRINTF(MEDIUM, "SHA512 hw count: %x\n", *sha512_notif_ctr);
        if (sha512_intr_count != *sha512_notif_ctr) {
            VPRINTF(ERROR, "SHA512 count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // SHA256
        VPRINTF(MEDIUM, "SHA256 fw count: %x\n", sha256_intr_count);
        VPRINTF(MEDIUM, "SHA256 hw count: %x\n", *sha256_notif_ctr);
        if (sha256_intr_count != *sha256_notif_ctr) {
            VPRINTF(ERROR, "SHA256 count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // SHA Accelerator
        VPRINTF(MEDIUM, "SHA Accel fw count: %x\n", sha512_acc_intr_count);
        VPRINTF(MEDIUM, "SHA Accel hw count: %x\n", *sha512_acc_notif_ctr);
        if (sha512_acc_intr_count != *sha512_acc_notif_ctr) {
            VPRINTF(ERROR, "SHA512_acc count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // HMAC Notif
        VPRINTF(MEDIUM, "HMAC fw Notif count: %x\n", hmac_notif_intr_count);
        VPRINTF(MEDIUM, "HMAC hw Notif count: %x\n", *hmac_notif_ctr);
        if (hmac_notif_intr_count != *hmac_notif_ctr) {
            VPRINTF(ERROR, "HMAC Notif count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // HMAC Error
        VPRINTF(MEDIUM, "HMAC fw Err count: %x\n", hmac_error_intr_count);
        VPRINTF(MEDIUM, "HMAC hw Err count: %x\n", *hmac_notif_ctr);
        hmac_error_intr_count_hw =  *hmac_error_key_mode_ctr +
                                    *hmac_error_key_zero_ctr;
        if (hmac_error_intr_count != hmac_error_intr_count_hw) {
            VPRINTF(ERROR, "HMAC Err count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }
        // ECC
        VPRINTF(MEDIUM, "ECC fw count: %x\n", ecc_intr_count);
        VPRINTF(MEDIUM, "ECC hw count: %x\n", *ecc_notif_ctr);
        if (ecc_intr_count != *ecc_notif_ctr) {
            VPRINTF(ERROR, "ECC count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // DOE
        VPRINTF(MEDIUM, "DOE fw count: %x\n", doe_intr_count);
        VPRINTF(MEDIUM, "DOE hw count: %x\n", *doe_notif_ctr);
        if (doe_intr_count != *doe_notif_ctr) {
            VPRINTF(ERROR, "DOE count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // SOC_IFC Error
        VPRINTF(MEDIUM, "SOC_IFC Err fw count: %x\n", soc_ifc_error_intr_count);
        soc_ifc_error_intr_count_hw =  *soc_ifc_error_internal_ctr +
                                       *soc_ifc_error_inv_dev_ctr  +
                                       *soc_ifc_error_cmd_fail_ctr +
                                       *soc_ifc_error_bad_fuse_ctr +
                                       *soc_ifc_error_iccm_blocked_ctr +
                                       *soc_ifc_error_mbox_ecc_unc_ctr +
                                       *soc_ifc_error_wdt_timer1_timeout_ctr +
                                       *soc_ifc_error_wdt_timer2_timeout_ctr;
        VPRINTF(MEDIUM, "SOC_IFC Err hw count: %x\n", soc_ifc_error_intr_count_hw);
        if (soc_ifc_error_intr_count != soc_ifc_error_intr_count_hw) {
            VPRINTF(ERROR, "SOC_IFC Error count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // SOC_IFC Notif
        VPRINTF(MEDIUM, "SOC_IFC Notif fw count: %x\n", soc_ifc_notif_intr_count);
        soc_ifc_notif_intr_count_hw =  *soc_ifc_notif_cmd_avail_ctr +
                                       *soc_ifc_notif_mbox_ecc_cor_ctr +
                                       *soc_ifc_notif_debug_locked_ctr +
                                       *soc_ifc_notif_scan_mode_ctr +
                                       *soc_ifc_notif_soc_req_lock_ctr +
                                       *soc_ifc_notif_gen_in_toggle_ctr;
        VPRINTF(MEDIUM, "SOC_IFC Notif hw count: %x\n", soc_ifc_notif_intr_count_hw);
        if (soc_ifc_notif_intr_count != soc_ifc_notif_intr_count_hw) {
            VPRINTF(ERROR, "SOC_IFC Notif count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // ABR
        VPRINTF(MEDIUM, "ABR fw count: %x\n", abr_intr_count);
        VPRINTF(MEDIUM, "ABR hw count: %x\n", *abr_notif_ctr);
        if (abr_intr_count != *abr_notif_ctr) {
            VPRINTF(ERROR, "ABR count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // AXI_DMA
        VPRINTF(MEDIUM, "AXI_DMA fw count: %x\n", axi_dma_intr_count);
        VPRINTF(MEDIUM, "AXI_DMA hw count: %x\n", *axi_dma_notif_ctr);
        if (axi_dma_intr_count != *axi_dma_notif_ctr) {
            VPRINTF(ERROR, "AXI_DMA count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // SHA3
        VPRINTF(MEDIUM, "SHA3 fw count: %x\n", sha3_intr_count);
        VPRINTF(MEDIUM, "SHA3 hw count: %x\n", *sha3_notif_ctr);
        if (sha3_intr_count != *sha3_notif_ctr) {
            VPRINTF(ERROR, "SHA3 count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // AES
        VPRINTF(MEDIUM, "AES fw count: %x\n", aes_intr_count);
        VPRINTF(MEDIUM, "AES hw count: %x\n", *aes_notif_ctr);
        if (aes_intr_count != *aes_notif_ctr) {
            VPRINTF(ERROR, "AES count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // Print total interrupt count
        VPRINTF(MEDIUM, "main end - intr_cnt:%x\n", intr_count);
        if (intr_count != *sha512_notif_ctr + *sha256_notif_ctr + *sha512_acc_notif_ctr + *hmac_notif_ctr + hmac_error_intr_count_hw + *ecc_notif_ctr + *doe_notif_ctr + soc_ifc_error_intr_count_hw + soc_ifc_notif_intr_count_hw + *abr_notif_ctr + *axi_dma_notif_ctr + *sha3_notif_ctr + *aes_notif_ctr) {
            VPRINTF(ERROR, "TOTAL count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // Coverage: sweep all 12 peripheral INTR_BLOCK_RF register files with
        // varied patterns to toggle the AHB hwdata/hrdata buses in both
        // directions and reach the interrupt register blocks that are not
        // otherwise exercised above. Global interrupts are already disabled
        // (mstatus.MIE cleared after the busy loop), so this does not fire the
        // ISR. The sweep leaves all enables/status/counters in a clean state.
        intr_block_rf_sweep();

        // Coverage: exercise generic_input_wires toggling in both directions
        // (0->1 and 1->0 on all 64 bits) via new TB command 0x96, with readback
        // verification. Interrupts are currently disabled (mstatus.MIE cleared
        // after the busy loop), so this only advances the NOTIF_GEN_IN_TOGGLE
        // hardware counter and does not enter the ISR.
        generic_input_wires_toggle_phase(soc_ifc_notif_gen_in_toggle_ctr);

        // Now test timer interrupts
        mtime = (lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_H) << 32) | lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_L);
        // Did we just rollover? Maybe the value read from MTIME_H was stale after reading MTIME_L.
        // Reread.
        if ((mtime & 0xFFFFFFFF) < 0x40) {
            mtime = (lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_H) << 32) | lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_L);
        }

        // Setup a wait time of 1000 clock cycles = 10us
        mtime += 1000;
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIMECMP_L, mtime & 0xFFFFFFFF);
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIMECMP_H, mtime >> 32       );

        // Re-enable interrupts (but not external interrupts)
        csr_clr_bits_mie(MIE_MEI_BIT_MASK);
        csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

        // Poll for Timer Interrupt Handler to complete processing.
        // Timer ISR simply sets mtimecmp back to max values, so poll for that.
        while (lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_RV_MTIMECMP_H) != 0xFFFFFFFF) {
            // Sleep in between triggers to allow ISR to execute and show idle time in sims
            for (uint16_t slp = 0; slp < 100; slp++) {
                __asm__ volatile ("nop"); // Sleep loop as "nop"
            }
        }

        return;
}

