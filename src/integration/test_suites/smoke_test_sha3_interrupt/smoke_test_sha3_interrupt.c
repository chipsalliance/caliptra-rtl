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
    dif_kmac_operation_state_t operation_state;
    uint32_t digest;

    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " SHA3 smoke test for interrupts!\n"   );
    VPRINTF(LOW, "----------------------------------\n");

    // Call interrupt init.
    init_interrupts();

    ////////////////////////////////////
    // Enable command done interrupt. //
    ////////////////////////////////////
    lsu_write_32(CLP_KMAC_INTR_ENABLE, KMAC_INTR_ENABLE_KMAC_DONE_MASK);

    // Get the SHA3 block to finish the absorbing state.
    dif_kmac_mode_sha3_start(CLP_KMAC_BASE_ADDR, &operation_state, kDifKmacModeSha3Len224);
    dif_kmac_absorb(CLP_KMAC_BASE_ADDR, &operation_state, "OpenTitan", 9, NULL);
    dif_kmac_squeeze(CLP_KMAC_BASE_ADDR, &operation_state, &digest, sizeof(uint32_t), /*processed=*/NULL, /*capacity=*/NULL);
    dif_kmac_end(CLP_KMAC_BASE_ADDR, &operation_state);

    if (cptra_intr_rcv.sha3_notif | KMAC_INTR_STATE_KMAC_DONE_MASK) {
        VPRINTF(LOW, "Successfully received command done interrupt.\n");
    } else {
        VPRINTF(LOW, "ERROR: expected KMAC DONE interrupt.\n");
        // Write 0x1 to STDOUT for TB to fail test.
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    //////////////////////////////////
    // Enable FIFO empty interrupt. //
    //////////////////////////////////
    lsu_write_32(CLP_KMAC_INTR_ENABLE, KMAC_INTR_ENABLE_FIFO_EMPTY_MASK);

    // Get SHA3 block into the absorbing state.
    dif_kmac_mode_sha3_start(CLP_KMAC_BASE_ADDR, &operation_state, kDifKmacModeSha3Len224);
    // Fill up message FIFO.
    for (int i = 0; i < 2*KMAC_PARAM_NUM_ENTRIES_MSG_FIFO*KMAC_PARAM_NUM_BYTES_MSG_FIFO_ENTRY; ++i) {
        lsu_write_32(CLP_KMAC_MSG_FIFO_BASE_ADDR, 0);
    }
    // Hopefully this will trigger the empty FIFO when it happens.
    while ((cptra_intr_rcv.sha3_notif | KMAC_INTR_STATE_FIFO_EMPTY_MASK) == 0) {
    }
    VPRINTF(LOW, "Successfully received message FIFO empty interrupt.\n");
    dif_kmac_squeeze(CLP_KMAC_BASE_ADDR, &operation_state, &digest, sizeof(uint32_t), /*processed=*/NULL, /*capacity=*/NULL);
    dif_kmac_end(CLP_KMAC_BASE_ADDR, &operation_state);

    /////////////////////////////
    // Enable error interrupt. //
    /////////////////////////////
    lsu_write_32(CLP_KMAC_INTR_ENABLE, KMAC_INTR_ENABLE_FIFO_EMPTY_MASK);

    // Send process command before start, which should cause an error.
    lsu_write_32(CLP_KMAC_CMD, KMAC_CMD_CMD_VALUE_PROCESS << KMAC_CMD_CMD_LOW);

    if (cptra_intr_rcv.sha3_error | KMAC_INTR_ENABLE_KMAC_ERR_MASK) {
        VPRINTF(LOW, "Successfully received KMAC error.\n");
    } else {
        VPRINTF(LOW, "ERROR: expected KMAC error interrupt.\n");
        // Write 0x1 to STDOUT for TB to fail test.
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    // Write 0xff to STDOUT for TB to terminate test.
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
