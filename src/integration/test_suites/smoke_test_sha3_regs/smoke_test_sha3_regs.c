// Copyright lowRISC contributors (OpenTitan project).
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

#include "caliptra_isr.h"
#include "printf.h"
#include "sha3.h"
#include <string.h>

#ifdef CPT_VERBOSITY
  enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
  enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {

    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " SHA3 smoke test for registers!\n"   );
    VPRINTF(LOW, "----------------------------------\n");

    // Call interrupt init
    init_interrupts();

    uint32_t read_val;

    ///////////////////////////
    // KMAC register message //
    ///////////////////////////
    VPRINTF(LOW, "Starting with the KMAC registers.\n");

    // Interrupt state.
    read_val = lsu_read_32(CLP_KMAC_INTR_STATE);
    if (read_val != 0) {
        VPRINTF(ERROR, "Interrupt state should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Interrupt enable.
    read_val = lsu_read_32(CLP_KMAC_INTR_ENABLE);
    if (read_val != 0) {
        VPRINTF(ERROR, "Interrupt enable should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Interrupt test.
    lsu_write_32(CLP_KMAC_INTR_TEST, 0);

    // Alert test.
    lsu_write_32(CLP_KMAC_ALERT_TEST, 0);

    // Config regwen.
    read_val = lsu_read_32(CLP_KMAC_CFG_REGWEN);
    if (read_val != 1) {
        VPRINTF(ERROR, "KMAC should be enabled.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Config regwen.
    read_val = lsu_read_32(CLP_KMAC_CFG_SHADOWED);
    if (read_val != 0) {
        VPRINTF(ERROR, "Shadowed configuration register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Command register.
    read_val = lsu_read_32(CLP_KMAC_CMD);
    if (read_val != 0) {
        VPRINTF(ERROR, "Command register should read zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Status register.
    read_val = lsu_read_32(CLP_KMAC_STATUS);
    if (read_val != 0x4001) {
        VPRINTF(ERROR, "Status register should be 0x4001.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // PREFIX 0.
    read_val = lsu_read_32(CLP_KMAC_PREFIX_0);
    if (read_val != 0) {
        VPRINTF(ERROR, "Prefix 0 register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // PREFIX 1.
    read_val = lsu_read_32(CLP_KMAC_PREFIX_1);
    if (read_val != 0) {
        VPRINTF(ERROR, "Prefix 1 register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // PREFIX 2.
    read_val = lsu_read_32(CLP_KMAC_PREFIX_2);
    if (read_val != 0) {
        VPRINTF(ERROR, "Prefix 2 register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // PREFIX 3.
    read_val = lsu_read_32(CLP_KMAC_PREFIX_3);
    if (read_val != 0) {
        VPRINTF(ERROR, "Prefix 3 register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // PREFIX 4.
    read_val = lsu_read_32(CLP_KMAC_PREFIX_4);
    if (read_val != 0) {
        VPRINTF(ERROR, "Prefix 4 register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // PREFIX 5.
    read_val = lsu_read_32(CLP_KMAC_PREFIX_5);
    if (read_val != 0) {
        VPRINTF(ERROR, "Prefix 5 register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // PREFIX 6.
    read_val = lsu_read_32(CLP_KMAC_PREFIX_6);
    if (read_val != 0) {
        VPRINTF(ERROR, "Prefix 6 register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // PREFIX 7.
    read_val = lsu_read_32(CLP_KMAC_PREFIX_7);
    if (read_val != 0) {
        VPRINTF(ERROR, "Prefix 7 register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // PREFIX 8.
    read_val = lsu_read_32(CLP_KMAC_PREFIX_8);
    if (read_val != 0) {
        VPRINTF(ERROR, "Prefix 8 register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // PREFIX 9.
    read_val = lsu_read_32(CLP_KMAC_PREFIX_9);
    if (read_val != 0) {
        VPRINTF(ERROR, "Prefix 9 register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // PREFIX 10.
    read_val = lsu_read_32(CLP_KMAC_PREFIX_10);
    if (read_val != 0) {
        VPRINTF(ERROR, "Prefix 10 register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Error code.
    read_val = lsu_read_32(CLP_KMAC_ERR_CODE);
    if (read_val != 0) {
        VPRINTF(ERROR, "Error code register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Reading from CLP_KMAC_STATE_BASE_ADDR has side effects.

    // Writing to CLP_KMAC_MSG_FIFO_BASE_ADDRESS has side effects.

    ///////////////////////////
    // SHA3 register message //
    ///////////////////////////
    VPRINTF(LOW, "Moving on to the SHA3 registers.\n");

    // SHA3 name.
    read_val = lsu_read_32(CLP_SHA3_SHA3_NAME_0);
    if (read_val != 0x61337368) {
        VPRINTF(ERROR, "SHA3 name should be 'sha3'.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }
    read_val = lsu_read_32(CLP_SHA3_SHA3_NAME_1);
    if (read_val != 0) {
        VPRINTF(ERROR, "SHA3 name 1 should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // SHA3 version.
    read_val = lsu_read_32(CLP_SHA3_SHA3_VERSION_0);
    if (read_val != 0x3030312e) {
        VPRINTF(ERROR, "SHA3 version should be '2.0'.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }
    read_val = lsu_read_32(CLP_SHA3_SHA3_VERSION_1);
    if (read_val != 0) {
        VPRINTF(ERROR, "SHA3 version 1 should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Alert test.
    lsu_write_32(CLP_SHA3_ALERT_TEST, 0);

    // Config regwen.
    read_val = lsu_read_32(CLP_SHA3_CFG_REGWEN);
    if (read_val != 0) {
        VPRINTF(ERROR, "SHA3 config regwen is set to zero in sha3_ctrl.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Config regwen.
    read_val = lsu_read_32(CLP_SHA3_CFG_SHADOWED);
    if (read_val != 0) {
        VPRINTF(ERROR, "Shadowed configuration register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Command register.
    read_val = lsu_read_32(CLP_SHA3_CMD);
    if (read_val != 0) {
        VPRINTF(ERROR, "Command register should read zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Status register.
    read_val = lsu_read_32(CLP_SHA3_STATUS);
    if (read_val != 0) {
        VPRINTF(ERROR, "Status register is set to zero in sha3_ctrl.sv.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Error code.
    read_val = lsu_read_32(CLP_SHA3_ERR_CODE);
    if (read_val != 0) {
        VPRINTF(ERROR, "Error code register should be zero.\n");
        SEND_STDOUT_CTRL(0x1); // Terminate test with failure.
        while (1);
    }

    // Reading from CLP_SHA3_STATE_BASE_ADDR has side effects.

    // Writing to CLP_SHA3_MSG_FIFO_BASE_ADDRESS has side effects.

    // All interrupt registers should be readable but they don't have a defined reset value.
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_GLOBAL_INTR_EN_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_ERROR_INTR_EN_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_ERROR_INTR_TRIG_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_SHA3_ERROR_INTR_COUNT_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_SHA3_ERROR_INTR_COUNT_INCR_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R);
    read_val = lsu_read_32(CLP_SHA3_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R);

    // Write 0xff to STDOUT for TB to terminate test.
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
