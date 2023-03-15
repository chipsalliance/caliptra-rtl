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
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"



volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

enum ecc_error_mode_type {
    NONE,
    SINGLE,
    DOUBLE
} ecc_error_mode = NONE;

uint32_t test_mbox_sram_ecc() {
    uint32_t sts = 0;
    volatile uint32_t * soc_ifc_error_mbox_ecc_unc_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R);
    volatile uint32_t * soc_ifc_notif_mbox_ecc_cor_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R);

    // Acquire the mailbox lock
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) != 0);

    // Allocate a large array in Mailbox SRAM
    volatile uint32_t* myarray = (uint32_t*) MBOX_DIR_BASE_ADDR;
    for (uint32_t ii; ii < 64; ii++) {
        myarray[ii] = 64-ii;
    }

    // Read the array from the Mailbox and write to STDOUT
    for (uint32_t ii; ii < 64; ii++) {
        printf("[%d]:%x\n", ii, myarray[ii]); // no verbosity control -- dereferencing the array IS the test
    }

    // Check Interrupt Counts
    if (intr_count == 0) {
        VPRINTF(ERROR, "ERROR: No interrupts received during ECC sram test\n");
        sts = 1;
    }
    // Sleep in between checking/clearing intr_count to allow ISR to execute and show idle time in sims
    for (uint16_t slp = 0; slp < 100; slp++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    intr_count = 0;

    // Get the interrupt count for the expected type
    if (ecc_error_mode == SINGLE) {
        if (*soc_ifc_notif_mbox_ecc_cor_ctr == 0) {
            VPRINTF(ERROR, "ERROR: Unexpected 0 count value for correctable ECC errors\n");
            sts |= 0x04;
        } else {
            VPRINTF(LOW, "Correctable ECC err count: %x\n", *soc_ifc_notif_mbox_ecc_cor_ctr);
        }
    } else if (ecc_error_mode == DOUBLE) {
        if (*soc_ifc_error_mbox_ecc_unc_ctr == 0) {
            VPRINTF(ERROR, "ERROR: Unexpected 0 count value for uncorrectable ECC errors\n");
            sts |= 0x08;
        } else {
            VPRINTF(LOW, "Uncorrectable ECC err count: %x\n", *soc_ifc_error_mbox_ecc_unc_ctr);
        }
    } else {
        VPRINTF(ERROR, "ERROR: Unexpected ecc_error_mode: %x\n", ecc_error_mode);
        sts |= 0x80;
    }

    // Unlock Mailbox
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

    return sts;
}

void main(void) {
        int argc=0;
        char *argv[1];

        volatile uint32_t * sha512_acc_notif_trig = (uint32_t *) (CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * soc_ifc_error_trig    = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R);
        volatile uint32_t * soc_ifc_notif_trig    = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);

        volatile uint32_t * sha512_acc_notif_ctr     = (uint32_t *) (CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_internal_ctr     = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_inv_dev_ctr      = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_cmd_fail_ctr     = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_bad_fuse_ctr     = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_iccm_blocked_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_error_mbox_ecc_unc_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_notif_cmd_avail_ctr    = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_notif_mbox_ecc_cor_ctr = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R);

        uint32_t soc_ifc_notif_intr_count_hw = 0;
        uint32_t soc_ifc_error_intr_count_hw = 0;

        uint32_t sts;

        VPRINTF(LOW, "----------------------------------\nSRAM ECC Smoke Test!!\n----------------------------------\n");

        // Setup the interrupt CSR configuration
        init_interrupts();

        // Initialize the counter
        intr_count = 0;

        // Enable Random ECC single-bit error injection
        SEND_STDOUT_CTRL( 0xfd);
        ecc_error_mode = SINGLE;

        // Execute the test
        sts = test_mbox_sram_ecc();

        // Enable Random ECC double-bit error injection
        SEND_STDOUT_CTRL( 0xfd);
        SEND_STDOUT_CTRL( 0xfe);
        ecc_error_mode = DOUBLE;

        // Execute the test
        sts |= test_mbox_sram_ecc();

        // TODO Test SRAM single-bit errors alongside SHA accel operation to ensure write-back works correctly
        // TODO Test SRAM single-bit errors corrected during a mailbox protocol operation

        // Disable Random ECC double-bit error injection
        SEND_STDOUT_CTRL( 0xfe);
        ecc_error_mode = NONE;

        // Disable interrutps
        csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);

        // Print interrupt count from FW/HW trackers
        // SHA Accelerator
        VPRINTF(LOW, "SHA Accel hw count: %x\n", *sha512_acc_notif_ctr);

        // SOC_IFC Error
        soc_ifc_error_intr_count_hw =  *soc_ifc_error_internal_ctr +
                                       *soc_ifc_error_inv_dev_ctr  +
                                       *soc_ifc_error_cmd_fail_ctr +
                                       *soc_ifc_error_bad_fuse_ctr +
                                       *soc_ifc_error_iccm_blocked_ctr +
                                       *soc_ifc_error_mbox_ecc_unc_ctr;
        VPRINTF(LOW, "SOC_IFC Err hw count: %x\n", soc_ifc_error_intr_count_hw);

        // SOC_IFC Notif
        soc_ifc_notif_intr_count_hw =  *soc_ifc_notif_cmd_avail_ctr +
                                       *soc_ifc_notif_mbox_ecc_cor_ctr;
        VPRINTF(LOW, "SOC_IFC Notif hw count: %x\n", soc_ifc_notif_intr_count_hw);

        // Print ending status
        if (sts) {
            VPRINTF(ERROR, "Detected errors during ECC error injection test. Sts: [%x] - killing sim with error\n", sts);
            SEND_STDOUT_CTRL( 0x1); // Kill sim with ERROR
            while(1);
        }

        return;
}
