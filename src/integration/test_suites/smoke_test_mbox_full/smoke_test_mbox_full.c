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
// Test behavior when transfers reach Mailbox capacity.

#include "caliptra_defines.h"
#include "riscv_hw_if.h"
#include "soc_access.h"
#include "soc_ifc.h"
#include <stdint.h>
#include "printf.h"
#include "caliptra_isr.h"
#include "clk_gate.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity             verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity             verbosity_g = LOW;
#endif

#define MBOX_DLEN_VAL             0xFFFFFFFF

#define MBOX_PTR_RST_OVERRIDE     0xFFFFFFF0
#define MBOX_VALID_USER           0xFFFFFFFF

#define TB_CMD_FORCE_MBOX_PTR     0x1D7F
#define TB_CMD_RELEASE_MBOX_PTR   0x1E7F
#define TB_CMD_FAIL               0x01
#define TB_CMD_PASS               0xFF


volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main () {
    uint32_t mbox_data[] = { 0x5a5a5a5a,
                             0xa5a5a5a5,
                             0x000FF1CE,
                             0x8BADF00D,
                             0xABADBABE,
                             0xD15EA5ED,
                             0xACE0FBA5,
                             0xB000DEAD,
                             0xDABBAD00,
                             0xDEADBEAF,
                             0xFEE1DEAD,
                             0x0D15EA5E,
                             0x420FADED,
                             0xBAADC0DE,
                             0xC0FFEEEE,
                             0xCAFEC0DE,
                           };
    axi_resp_t axi_resp;
    enum mbox_fsm_e state;
    uint32_t mbox_data_readback, mbox_status, mbox_dlen;

    // Set mailbox pointer reset value override
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, MBOX_PTR_RST_OVERRIDE);
    // Force the mailbox pointers to reset to MBOX_PTR_RST_OVERRIDE as opposed to 0
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, TB_CMD_FORCE_MBOX_PTR);

    // Register interrupts
    init_interrupts();

    // Message
    VPRINTF(LOW, "-----------------------------------\n");
    VPRINTF(LOW, " Caliptra Mailbox Full Smoke Test!!\n");
    VPRINTF(LOW, "-----------------------------------\n");

    VPRINTF(LOW, "FW: Test 1 - Overflow mailbox DATAIN and DATAOUT\n");
    // SoC: Poll for mbox lock
    VPRINTF(LOW, "FW (SoC): Poll for mailbox lock\n");
    do {
        axi_resp = soc_read_user_32(CLP_MBOX_CSR_MBOX_LOCK, MBOX_VALID_USER);
    } while ((axi_resp.rdata & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 1);

    // SoC: Write mailbox command, data and length
    VPRINTF(LOW, "FW (SoC): Write request to mailbox\n");
    soc_write_user_32(CLP_MBOX_CSR_MBOX_CMD,  0x0,           MBOX_VALID_USER);
    soc_write_user_32(CLP_MBOX_CSR_MBOX_DLEN, MBOX_DLEN_VAL, MBOX_VALID_USER);
    for (uint32_t i = 0; i <= MBOX_DLEN_VAL - MBOX_PTR_RST_OVERRIDE; i++) {
      soc_write_user_32(CLP_MBOX_CSR_MBOX_DATAIN, mbox_data[i % 16],  MBOX_VALID_USER);
    }

    // SoC: Try to write more data than the MBOX capacity
    VPRINTF(LOW, "FW (SoC): Overflow mailbox data in\n");
    soc_write_user_32(CLP_MBOX_CSR_MBOX_DATAIN, 0x0FACE0FF, MBOX_VALID_USER);

    // Mailbox should ignore the write overflow
    if (cptra_intr_rcv.soc_ifc_error != 0) {
      VPRINTF(ERROR, "ERROR: Mailbox reported and error after mailbox write overflow!\n");
      SEND_STDOUT_CTRL(TB_CMD_FAIL);
      while(1);
    }
    if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SOC_REQ_LOCK_STS_MASK != 0) {
      VPRINTF(ERROR, "ERROR: Mailbox notified after mailbox write overflow!\n");
      SEND_STDOUT_CTRL(TB_CMD_FAIL);
      while(1);
    }

    // UC: Read status register & expect it to be in progress
    VPRINTF(LOW, "FW: Ensure mailbox is not idle\n");
    mbox_status = lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK;
    if (mbox_status != CMD_BUSY) {
      VPRINTF(ERROR, "ERROR: Mailbox status changed before SoC finished writing the command! Expected 0x%x got 0x%x\n", CMD_BUSY, mbox_status);
      SEND_STDOUT_CTRL(TB_CMD_FAIL);
      while(1);
    }

    // SoC Set mailbox execute
    VPRINTF(LOW, "FW (SoC): Set mailbox execute\n");
    soc_write_user_32(CLP_MBOX_CSR_MBOX_EXECUTE, 1, MBOX_VALID_USER);

    // UC: Poll for execute from SoC
    VPRINTF(LOW, "FW: Poll for mailbox execute\n");
    mbox_status = lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK;
    while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) != 1) {
      mbox_status = lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK;
    }

    // UC: Read DLEN CLP_MBOX_CSR_MBOX_DLEN
    VPRINTF(LOW, "FW: Read mailbox data length\n");
    mbox_dlen = lsu_read_32(CLP_MBOX_CSR_MBOX_DLEN);
    if (mbox_dlen !=  MBOX_DLEN_VAL) {
      VPRINTF(ERROR, "ERROR: Mailbox DLEN mismatch! Expected 0x%x got 0x%x\n", MBOX_DLEN_VAL, mbox_dlen);
      SEND_STDOUT_CTRL(TB_CMD_FAIL);
      while(1);
    }

    // UC: Read Mailbox
    VPRINTF(LOW, "FW: Read mailbox data\n");
    for (uint32_t i = 0; i <= MBOX_DLEN_VAL - MBOX_PTR_RST_OVERRIDE; i++) {
      if ((mbox_data_readback = lsu_read_32(CLP_MBOX_CSR_MBOX_DATAOUT)) != mbox_data[i % 16]) {
        VPRINTF(ERROR, "ERROR: Mailbox read mismatch! Expected 0x%x got 0x%x\n", mbox_data[i % 16], mbox_data_readback);
        SEND_STDOUT_CTRL(TB_CMD_FAIL);
        while(1);
      }
    }

    // UC: Read overflow mailbox
    VPRINTF(LOW, "FW: Overflow mailbox data out\n");
    if ((mbox_data_readback = lsu_read_32(CLP_MBOX_CSR_MBOX_DATAOUT)) != 0) {
      VPRINTF(ERROR, "ERROR: Mailbox read data on overflow mismatch! Expected 0x%x got 0x%x\n", 0, mbox_data_readback);
      SEND_STDOUT_CTRL(TB_CMD_FAIL);
      while(1);
    }

    // UC: Set status register
    VPRINTF(LOW, "FW: Set mailbox status to CMD_COMPLETE\n");
    lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (CMD_COMPLETE << MBOX_CSR_MBOX_STATUS_STATUS_LOW) & MBOX_CSR_MBOX_STATUS_STATUS_MASK);

    // SoC: Poll on status register
    VPRINTF(LOW, "FW: Wait for mailbox status to be cleared\n");
    while ((mbox_status = lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK) != CMD_COMPLETE);

    // SoC: Clear execute
    VPRINTF(LOW, "FW (SoC): Clear mailbox execute\n");
    soc_write_user_32(CLP_MBOX_CSR_MBOX_EXECUTE, 0, MBOX_VALID_USER);

    // Assert no errors are reported after the transaction
    if (cptra_intr_rcv.soc_ifc_error != 0) {
      VPRINTF(ERROR, "ERROR: Error reported after mailbox full test!\n");
      SEND_STDOUT_CTRL(TB_CMD_FAIL);
      while(1);
    }

    VPRINTF(LOW, "FW: Test 2 - Lock mailbox from SoC when FW unlocks\n");

    VPRINTF(LOW, "FW: Poll for mailbox lock\n");
    if (soc_ifc_mbox_acquire_lock(100)) {
      VPRINTF(ERROR, "ERROR: Failed to aquire mailbox lock!\n");
      SEND_STDOUT_CTRL(TB_CMD_FAIL);
      while(1);
    }

    VPRINTF(LOW, "FW: Enable injection of SoC mailbox lock on FW mailbox unlock\n");
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x5A7F);

    VPRINTF(LOW, "FW: Force mailbox unlock\n");
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

    VPRINTF(LOW, "FW: Disable injection of SoC mailbox lock on FW mailbox unlock\n");
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x5B7F);

    VPRINTF(LOW, "FW: Ensure mailbox was locked by SoC\n");
    if (!soc_ifc_mbox_acquire_lock(100)) {
      VPRINTF(ERROR, "ERROR: Mailbox is not locked by SoC immediately after unlock!\n");
      SEND_STDOUT_CTRL(TB_CMD_FAIL);
      while(1);
    }

    VPRINTF(LOW, "FW: Test 3 - Unlock mailbox on direct mailbox SRAM access\n");

    VPRINTF(LOW, "FW: Force mailbox unlock\n");
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

    VPRINTF(LOW, "FW: Poll for mailbox lock\n");
    if (soc_ifc_mbox_acquire_lock(100)) {
      VPRINTF(ERROR, "ERROR: Failed to aquire mailbox lock!\n");
      SEND_STDOUT_CTRL(TB_CMD_FAIL);
      while(1);
    }

    VPRINTF(LOW, "FW: Enable injection of SoC mailbox unlock on FW mailbox direct access\n");
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x5C7F);

    // Write data into mailbox using direct-mode
    VPRINTF(LOW, "FW: Access mailbox SRAM directly\n");
    lsu_write_32(CLP_MBOX_SRAM_BASE_ADDR, mbox_data[0]);

    VPRINTF(LOW, "FW: Disable injection of SoC mailbox unlock on FW mailbox direct access\n");
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x5D7F);

    VPRINTF(LOW, "FW: Wait for mailbox to enter IDLE state\n");
    if (soc_ifc_poll_mbox_state(100, MBOX_IDLE)) {
      VPRINTF(ERROR, "ERROR: Mailbox is not unlocked after unlock injection!\n");
      SEND_STDOUT_CTRL(TB_CMD_FAIL);
      while(1);
    }

    SEND_STDOUT_CTRL(TB_CMD_PASS);
}
