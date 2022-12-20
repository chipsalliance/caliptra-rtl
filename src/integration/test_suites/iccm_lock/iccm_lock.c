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

extern uintptr_t iccm_code0_start, iccm_code0_end;
extern uintptr_t iccm_code1_start, iccm_code1_end;
extern uintptr_t iccm_code2_start, iccm_code2_end;
static uint32_t persistent_exec_cnt = 0; // Allocate in .data
static uint8_t  persistent_is_second_pass = 0; // Allocate in .data

void execute_first_pass_from_iccm (void) __attribute__ ((aligned(4),section (".data_iccm0")));
void execute_second_pass_from_iccm (void) __attribute__ ((aligned(4),section (".data_iccm1")));
void execute_fatal_from_iccm (void) __attribute__ ((aligned(4),section (".data_iccm2")));

void main(void) {
        int argc=0;
        char *argv[1];

        uint32_t * DCCM = (uint32_t *) RV_DCCM_SADR;
        uint32_t * ICCM = (uint32_t *) RV_ICCM_SADR;
        volatile uint32_t * doe_notif_trig    = (uint32_t *) (CLP_DOE_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * ecc_notif_trig    = (uint32_t *) (CLP_ECC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * hmac_notif_trig   = (uint32_t *) (CLP_HMAC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * sha512_notif_trig = (uint32_t *) (CLP_SHA512_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
        volatile uint32_t * sha256_notif_trig = (uint32_t *) (CLP_SHA256_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
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
        volatile uint32_t * soc_ifc_notif_cmd_avail_ctr    = (uint32_t *) (CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R);
        volatile uint32_t * soc_ifc_iccm_lock              = (uint32_t *) (CLP_SOC_IFC_REG_ICCM_LOCK);
        volatile uint32_t * soc_ifc_fw_update_reset        = (uint32_t *) (CLP_SOC_IFC_REG_FW_UPDATE_RESET);

        uint32_t * code_word = 0;
        uint32_t * iccm_dest = ICCM;
        void (* iccm_fn) (void) = (void*) ICCM;

        printf("----------------------------------\nICCM Lock Test from SweRV EL2 @WDC !!\n----------------------------------\n");

        // Setup the interrupt CSR configuration
        init_interrupts();

        // Initialize the counter
        intr_count = 0;

        // Check ICCM_LOCK is not currently set
        if (*soc_ifc_iccm_lock & SOC_IFC_REG_ICCM_LOCK_LOCK_MASK == SOC_IFC_REG_ICCM_LOCK_LOCK_MASK) {
            printf("ERROR: ICCM_LOCK set unexpectedly!\n");
            printf("%c", 0x1);
        }

        // Copy code section from Mailbox to ICCM
        //   1. Check if this is the first or Nth pass through main (by reading from a non-reset location e.g. in Mailbox)
        //   2. If 1st:
        //     a. Copy section (A) to ICCM
        //   3. Else:
        //     a. Copy section (B) to ICCM (different print)
        if (persistent_is_second_pass) {
            code_word = (uint32_t *) &iccm_code1_start;
            printf("Copying code from %x to %x\n", (uintptr_t) code_word, (uintptr_t) iccm_dest);
            while (code_word < (uint32_t *) &iccm_code1_end) {
                printf("at %x: %x\n", (uintptr_t) code_word, *code_word);
                *iccm_dest++ = *code_word++;
            }
        } else {
            code_word = (uint32_t *) &iccm_code0_start;
            printf("Copying code from %x [through %x] to %x\n", (uintptr_t) code_word, &iccm_code0_end, (uintptr_t) iccm_dest);
            while (code_word < (uint32_t *) &iccm_code0_end) {
                printf("at %x: %x\n", (uintptr_t) code_word, *code_word);
                *iccm_dest++ = *code_word++;
            }
        }

        // Check interrupt count (die if !0)
        if (intr_count) {
            printf("ERROR: Detected interrupt while copying code to unlocked ICCM!\n");
            printf("%c", 0x1);
        }

        // Execute code from ICCM
        iccm_fn();

        // Code from ICCM (1) increments persistent_exec_cnt. If > 2, then die (it executed > twice)
        // Code from ICCM (2) does not increment.
        if (persistent_exec_cnt > 2) {
            printf("ERROR: First pass code executed from ICCM during second pass (after reset)!\n");
            printf("%c", 0x1);
        }

        // Lock ICCM Writes
        *soc_ifc_iccm_lock = SOC_IFC_REG_ICCM_LOCK_LOCK_MASK;
        if (*soc_ifc_iccm_lock & SOC_IFC_REG_ICCM_LOCK_LOCK_MASK != SOC_IFC_REG_ICCM_LOCK_LOCK_MASK) {
            printf("ERROR: Failed to set ICCM_LOCK!\n");
            printf("%c", 0x1);
        }

        // Copy error code section from Mailbox to ICCM
        //   - This code section will kill the sim with error
        code_word = (uint32_t *) &iccm_code2_start;
        iccm_dest = ICCM;
        printf("Copying code from %x to %x\n", (uintptr_t) code_word, (uintptr_t) iccm_dest);
        while (code_word < (uint32_t *) &iccm_code2_end) {
            printf("at %x: %x\n", (uintptr_t) code_word, *code_word);
            *iccm_dest++ = *code_word++;
        }

        // Sleep
        __asm__ volatile ("nop");

        // Check Interrupt Count (Die if 0)
        if ((intr_count == 0) || (*soc_ifc_error_iccm_blocked_ctr == 0)) {
            printf("ERROR: Did not receive expected error interrupts while writing to Locked ICCM!\n");
            printf("%c", 0x1);
        }

        // Execute code from ICCM again (should be the original subroutine)
        iccm_fn();

        // TODO: Reset the firmware
        //   1. Check if this is the first or Nth pass through main (by reading from a non-reset location e.g. in Mailbox)
        //   2. If 1st:
        //     a. Write a non-zero value to some non-reset location (in the Mailbox)
        //     b. Trigger core reset
        //   3. Else:
        //     a. End simulation with success message
        if (persistent_is_second_pass) {
            printf("Success! Reached end of ICCM lock firmware during second iteration\n");
        } else {
            persistent_is_second_pass = 1;
            *soc_ifc_fw_update_reset = SOC_IFC_REG_FW_UPDATE_RESET_CORE_RST_MASK;
        }

        return;
}

void execute_first_pass_from_iccm (void) {
    printf("First pass through ICCM LOCK test!\n");
    persistent_exec_cnt++;
}

void execute_second_pass_from_iccm (void) {
    printf("Second pass through ICCM LOCK test!\n");
}

void execute_fatal_from_iccm (void) {
    printf("Error! Fatal subroutine is executing from ICCM even though locked when written!\n");
    printf("%c", 0x1); // Kills simulation with error
}
