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
#include <string.h>
#include <stdint.h>
#include "printf.h"


//int whisperPrintf(const char* format, ...);
//#define ee_printf whisperPrintf


volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


void main(void) {
        int argc=0;
        char *argv[1];

        volatile uint32_t * doe_notif_trig        = (uint32_t *) (CLP_DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * ecc_notif_trig        = (uint32_t *) (CLP_ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * hmac_notif_trig       = (uint32_t *) (CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * sha512_notif_trig     = (uint32_t *) (CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * sha256_notif_trig     = (uint32_t *) (CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * sha512_acc_notif_trig = (uint32_t *) (CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * soc_ifc_error_trig    = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R);
        volatile uint32_t * soc_ifc_notif_trig    = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);

        volatile uint32_t * sha512_notif_ctr         = (uint32_t *) (CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
        volatile uint32_t * sha256_notif_ctr         = (uint32_t *) (CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
        volatile uint32_t * sha512_acc_notif_ctr     = (uint32_t *) (CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
        volatile uint32_t * hmac_notif_ctr           = (uint32_t *) (CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
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
        volatile uint32_t * soc_ifc_notif_cmd_avail_ctr    = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_notif_mbox_ecc_cor_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_notif_debug_locked_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_notif_soc_req_lock_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R);

        uint32_t sha512_intr_count = 0;
        uint32_t sha256_intr_count = 0;
        uint32_t sha512_acc_intr_count = 0;
        uint32_t hmac_intr_count = 0;
        uint32_t ecc_intr_count = 0;
        uint32_t doe_intr_count = 0;
        uint32_t soc_ifc_notif_intr_count = 0;
        uint32_t soc_ifc_notif_intr_count_hw = 0;
        uint32_t soc_ifc_error_intr_count = 0;
        uint32_t soc_ifc_error_intr_count_hw = 0;

        VPRINTF(LOW,"----------------------------------\nCaliptra: Direct ISR Test!!\n----------------------------------\n");

        // Setup the interrupt CSR configuration
        init_interrupts();

        // Initialize the counter
        intr_count = 0;

        // Busy loop
        while (intr_count < 64) {
            // Trigger interrupt manually
            if ((intr_count % 0x12) >= 0x11) {
                *sha512_notif_trig = SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                sha512_intr_count++;
            } else if ((intr_count % 0x12) >= 0x10) {
                *sha256_notif_trig = SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                sha256_intr_count++;
            } else if ((intr_count % 0x12) >= 0x0F) {
                *sha512_acc_notif_trig = SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                sha512_acc_intr_count++;
            } else if ((intr_count % 0x12) >= 0x0E) {
                *hmac_notif_trig = HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                hmac_intr_count++;
            } else if ((intr_count % 0x12) >= 0x0D) {
                *ecc_notif_trig = ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                ecc_intr_count++;
            } else if ((intr_count % 0x12) >= 0x0C) {
                *doe_notif_trig = DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK;
                doe_intr_count++;
            } else if ((intr_count % 0x12) >= 0x08) { //8-B
                *soc_ifc_notif_trig = 1 << (intr_count % 0x4);
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

        // HMAC
        VPRINTF(MEDIUM, "HMAC fw count: %x\n", hmac_intr_count);
        VPRINTF(MEDIUM, "HMAC hw count: %x\n", *hmac_notif_ctr);
        if (hmac_intr_count != *hmac_notif_ctr) {
            VPRINTF(ERROR, "HMAC count mismatch!\n");
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
                                       *soc_ifc_notif_soc_req_lock_ctr;
        VPRINTF(MEDIUM, "SOC_IFC Notif hw count: %x\n", soc_ifc_notif_intr_count_hw);
        if (soc_ifc_notif_intr_count != soc_ifc_notif_intr_count_hw) {
            VPRINTF(ERROR, "SOC_IFC Notif count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        // Print total interrupt count
        VPRINTF(MEDIUM, "main end - intr_cnt:%x\n", intr_count);
        if (intr_count != *sha512_notif_ctr + *sha256_notif_ctr + *sha512_acc_notif_ctr + *hmac_notif_ctr + *ecc_notif_ctr + *doe_notif_ctr + soc_ifc_error_intr_count_hw + soc_ifc_notif_intr_count_hw) {
            VPRINTF(ERROR, "TOTAL count mismatch!\n");
            SEND_STDOUT_CTRL(0x1); // Kill sim with ERROR
        }

        return;
}

