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
#include "ifc_reg.h"
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "printf.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>

volatile char* stdout = (char *)STDOUT;
volatile uint32_t  intr_count = 0;
volatile int error_count __attribute__((section(".dccm.persistent"))) = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define TB_CMD_TEST_PASS 0xFF
#define TB_CMD_TEST_FAIL 0x01

uint32_t error_masks [] = {
    SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_MASK,
    SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INV_DEV_TRIG_MASK,
    SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_CMD_FAIL_TRIG_MASK,
    SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_BAD_FUSE_TRIG_MASK,
    SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_ICCM_BLOCKED_TRIG_MASK,
    SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_MBOX_ECC_UNC_TRIG_MASK,
    SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_MASK,
    SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_MASK
};
uint32_t notif_masks [] = {
    SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_AVAIL_TRIG_MASK,
    SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_MBOX_ECC_COR_TRIG_MASK,
    SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_DEBUG_LOCKED_TRIG_MASK,
    SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_SCAN_MODE_TRIG_MASK,
    SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_SOC_REQ_LOCK_TRIG_MASK,
    SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_GEN_IN_TOGGLE_TRIG_MASK
};

void main(void) {

    VPRINTF_LOW("==================\nIFC Interrupt Test\n==================\n\n");

    // Disable intr reporting
    lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R, 0);
    lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, 0);
    // Set interrupts
    for (int i=0; i < sizeof(error_masks)/sizeof(uint32_t); ++i) {
        lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R, error_masks[i]);
        if(lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & error_masks[i] == 0) {
            VPRINTF_LOW("Error interrupt %d not set!\n", i);
            error_count += 1;
            continue;
        }
        // Write 0 should not clear interrupt
        lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R, ~error_masks[i]);
        if(lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & error_masks[i] == 0) {
            VPRINTF_LOW("Error interrupt %d cleared by writing 0!\n", i);
            error_count += 1;
            continue;
        }
        // Write 1 should clear interrupt
        lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R, error_masks[i]);
        if(lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & error_masks[i] != 0) {
            VPRINTF_LOW("Error interrupt %d not cleared by writing 1!\n", i);
            error_count += 1;
            continue;
        }
    }
    for (int i=0; i < sizeof(notif_masks)/sizeof(uint32_t); ++i) {
        lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R, notif_masks[i]);
        if(lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R) & notif_masks[i] == 0) {
            VPRINTF_LOW("Notif interrupt %d not set!\n", i);
            error_count += 1;
            continue;
        }
        // Write 0 should not clear interrupt
        lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R, ~notif_masks[i]);
        if(lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R) & notif_masks[i] == 0) {
            VPRINTF_LOW("Notif interrupt %d cleared by writing 0!\n", i);
            error_count += 1;
            continue;
        }
        // Write 1 should clear interrupt
        lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R, notif_masks[i]);
        if(lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R) & notif_masks[i] != 0) {
            VPRINTF_LOW("Notif interrupt %d not cleared by writing 1!\n", i);
            error_count += 1;
            continue;
        }
    }

    VPRINTF_LOW("\nIFC Register Access Tests Completed\n");

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (error_count == 0 ) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
}
