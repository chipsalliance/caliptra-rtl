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
#include "riscv_hw_if.h"
#include "soc_access.h"
#include "soc_ifc.h"
#include <stdint.h>
#include "printf.h"
#include "caliptra_isr.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
volatile int rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity             verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity             verbosity_g = LOW;
#endif

#define MBOX_DLEN_VAL             0x00000020
#define MBOX_VALID_USER           0xFFFFFFFF

#define TB_CMD_COLD_RESET         0xF5
#define TB_CMD_TEST_PASS          0xFF
#define TB_CMD_TEST_FAIL          0x01

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main () {
    rst_count++;

    mbox_op_s op;
    uint32_t ii;
    uint32_t data;
    enum mbox_fsm_e state;
    uint32_t mbox_data[] = { 0x00000000,
                             0x11111111,
                             0x22222222,
                             0x33333333,
                             0x44444444,
                             0x55555555,
                             0x66666666,
                             0x77777777,
                             0x5a5a5a5a,
                             0xa5a5a5a5,
                             0x000FF1CE,
                             0x8BADF00D,
                             0xABADBABE,
                             0xD15EA5ED,
                             0xACE0FBA5,
                             0xB000DEAD
    };
    uint32_t read_data;

    // Test case info
    if (rst_count == 1) {
        VPRINTF(LOW, "----------------------------------\n");
        VPRINTF(LOW, " Caliptra Mailbox Smoke Test!!\n"    );
        VPRINTF(LOW, "----------------------------------\n");
        VPRINTF(LOW, "* Caliptra Mailbox SoC-UC regular flow\n");
    } else if (rst_count == 2) {
        VPRINTF(LOW, "* Caliptra Mailbox SoC-UC flow w/ tap mode\n");
    } else if (rst_count == 3) {
        VPRINTF(LOW, "* Caliptra Mailbox Force Unlock\n");
    }

    if (rst_count == 1 | rst_count == 2) {
        //set ready for FW so tb will push FW
        soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);

        // Sleep
        for (uint16_t slp = 0; slp < 33; slp++);

        //wait for mailbox data avail
        VPRINTF(LOW, "FW: Wait\n");
        while((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) != MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);

        if (rst_count == 2) {
            // Put mailbox in TAP mode, mailbox will be stuck in EXECUTE_UC
            // until it's unlocked or TAP mode is disabled
            lsu_write_32(CLP_MBOX_CSR_TAP_MODE, MBOX_CSR_TAP_MODE_ENABLED_MASK);
        }

        //read mbox command
        op = soc_ifc_read_mbox_cmd();

        //read from mbox
        VPRINTF(LOW, "FW: Reading %d bytes from mailbox\n", op.dlen);
        while(op.dlen) {
            data = soc_ifc_mbox_read_dataout_single();
            VPRINTF(HIGH, "  dataout: 0x%x\n", data);
            if (op.dlen < 4) {
                op.dlen=0;
            } else {
                op.dlen-=4;//sizeof(uint32_t);
            }
        }

        //push new data in like a response
        VPRINTF(LOW, "FW: Writing %d bytes to mailbox\n", MBOX_DLEN_VAL);
        for (ii = 0; ii < MBOX_DLEN_VAL/4; ii++) {
            VPRINTF(HIGH, "  datain: 0x%x\n", mbox_data[ii]);
            lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN,mbox_data[ii]);
        }

        //set data ready status
        VPRINTF(LOW, "FW: Set data ready status\n");
        lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS,DATA_READY);

        if (rst_count == 2) {
            // Disable TAP mode to unstuck the mailbox
            lsu_write_32(CLP_MBOX_CSR_TAP_MODE, 0);
        }

        //check FSM state, should be in EXECUTE_SOC
        state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
        if (state != MBOX_EXECUTE_SOC) {
            VPRINTF(ERROR, "ERROR: mailbox in unexpected state (%x) when expecting MBOX_EXECUTE_SOC (0x%x)\n", state, MBOX_EXECUTE_SOC);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
            while(1);
        } else {
            VPRINTF(LOW, "FW: Mailbox in expected state, MBOX_EXECUTE_SOC, ending test with success\n");
        }

        if (rst_count == 2) {
            // Put mailbox in TAP mode, it shouldn't influence its operation in this state
            lsu_write_32(CLP_MBOX_CSR_TAP_MODE, MBOX_CSR_TAP_MODE_ENABLED_MASK);
        }

        //Wait for SoC to reset execute reg
        VPRINTF(LOW, "FW: Wait for SoC to reset execute register\n");
        while((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 1);

        if (rst_count == 2) {
            // Disable TAP mode to not interfere later in the test
            lsu_write_32(CLP_MBOX_CSR_TAP_MODE, 0);
        }

        //Force unlock
        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

        //poll for mbox lock
        while((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 1);

        //write command
        lsu_write_32(CLP_MBOX_CSR_MBOX_CMD,0x12345678);

        //write dlen
        lsu_write_32(CLP_MBOX_CSR_MBOX_DLEN,MBOX_DLEN_VAL);

        //write datain
        VPRINTF(LOW, "FW: Writing %d bytes to mailbox\n", MBOX_DLEN_VAL);
        for (ii = 0; ii < MBOX_DLEN_VAL/4; ii++) {
            VPRINTF(HIGH, "  datain: 0x%x\n", mbox_data[ii]);
            lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN,mbox_data[ii]);
        }

        //set execute
        lsu_write_32(CLP_MBOX_CSR_MBOX_EXECUTE, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);

        if (rst_count == 2) {
            // Put mailbox in TAP mode to hit corner condition
            lsu_write_32(CLP_MBOX_CSR_TAP_MODE, MBOX_CSR_TAP_MODE_ENABLED_MASK);
        }

        //Poll status until data ready is set
        while((lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK) != DATA_READY);

        if (rst_count == 2) {
            // Disable TAP mode to not interfere later in the test
            lsu_write_32(CLP_MBOX_CSR_TAP_MODE, 0);
        }

        //check data
        VPRINTF(LOW, "FW: Checking %d bytes from mailbox as if return data\n", MBOX_DLEN_VAL);
        for (ii = 0; ii < MBOX_DLEN_VAL/4; ii++) {
            VPRINTF(HIGH, "  datain: 0x%x\n", mbox_data[ii]);
            read_data = lsu_read_32(CLP_MBOX_CSR_MBOX_DATAOUT);
            if (read_data != mbox_data[ii]) {
                VPRINTF(ERROR, "ERROR: mailbox data mismatch actual (0x%x) expected (0x%x)\n", read_data, mbox_data[ii]);
                SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
                while(1);
            }
        }

        // Issue cold reset
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        while(1);
    } else if (rst_count == 3) {
        axi_resp_t axi_resp, mbox_execute_unlock, mbox_dlen_unlock;
        uint32_t mbox_data_readback, mbox_status, mbox_dlen, mbox_execute;

        // Register interrupts
        init_interrupts();

        // SoC: Poll for mbox lock
        do {
            axi_resp = soc_read_user_32(CLP_MBOX_CSR_MBOX_LOCK, MBOX_VALID_USER);
        } while ((axi_resp.rdata & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 1);

        // Attempt direct write access in MBOX_WAIT_FOR_CMD state when SoC has a lock (should be rejected)
        lsu_write_32(CLP_MBOX_SRAM_BASE_ADDR + 0x1000, 0xDEADBEEF);
        if ((read_data = lsu_read_32(CLP_MBOX_SRAM_BASE_ADDR + 0x1000)) != 0) {
            VPRINTF(ERROR, "ERROR: mailbox read %x after direct write in MBOX_EXECUTE_SOC state. Expected: (0x%x)\n", read_data, 0);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
            while(1);
        }

        // SoC: Write mailbox command, data and length
        soc_write_user_32(CLP_MBOX_CSR_MBOX_CMD,  0x0,           MBOX_VALID_USER);
        soc_write_user_32(CLP_MBOX_CSR_MBOX_DLEN, MBOX_DLEN_VAL, MBOX_VALID_USER);
        for (uint32_t i = 0; i <= MBOX_DLEN_VAL / 4; i++) {
            soc_write_user_32(CLP_MBOX_CSR_MBOX_DATAIN, mbox_data[i % 16],  MBOX_VALID_USER);
        }

        // SoC Set mailbox execute
        soc_write_user_32(CLP_MBOX_CSR_MBOX_EXECUTE, 1, MBOX_VALID_USER);

        // UC: Poll for execute from SoC
        mbox_status = lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK;
        while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) != 1) {
            mbox_status = lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK;
        }

        // UC: Read DLEN CLP_MBOX_CSR_MBOX_DLEN
        mbox_dlen = lsu_read_32(CLP_MBOX_CSR_MBOX_DLEN);
        if (mbox_dlen !=  MBOX_DLEN_VAL) {
            VPRINTF(ERROR, "ERROR: Mailbox DLEN mismatch! Expected 0x%x got 0x%x\n", MBOX_DLEN_VAL, mbox_dlen);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
            while(1);
        }

        // UC: Read Mailbox (not fully)
        for (uint32_t i = 0; i < MBOX_DLEN_VAL/8; i++) {
            if ((mbox_data_readback = lsu_read_32(CLP_MBOX_CSR_MBOX_DATAOUT)) != mbox_data[i % 16]) {
                VPRINTF(ERROR, "ERROR: Mailbox read mismatch! Expected 0x%x got 0x%x\n", mbox_data[i % 16], mbox_data_readback);
                SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
                while(1);
            }
        }

        // UC: Force unlock
        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

        // SoC: Read execute after force unlock (should be 0)
        mbox_execute_unlock = soc_read_user_32(CLP_MBOX_CSR_MBOX_EXECUTE, MBOX_VALID_USER);
        if (mbox_execute_unlock.rdata !=  0) {
            VPRINTF(ERROR, "ERROR: Execute should be clear after forced unlock!\n", 0, mbox_execute_unlock.rdata);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
            while(1);
        }

        // Re-try the transaction

        // SoC: Poll for mbox lock
        do {
            axi_resp = soc_read_user_32(CLP_MBOX_CSR_MBOX_LOCK, MBOX_VALID_USER);
        } while ((axi_resp.rdata & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 1);

        // SoC: Write mailbox command, data and length
        soc_write_user_32(CLP_MBOX_CSR_MBOX_CMD,  0x0,           MBOX_VALID_USER);
        soc_write_user_32(CLP_MBOX_CSR_MBOX_DLEN, MBOX_DLEN_VAL, MBOX_VALID_USER);
        for (uint32_t i = 0; i < MBOX_DLEN_VAL / 4; i++) {
            soc_write_user_32(CLP_MBOX_CSR_MBOX_DATAIN, mbox_data[i % 16],  MBOX_VALID_USER);
        }

        // SoC Set mailbox execute
        soc_write_user_32(CLP_MBOX_CSR_MBOX_EXECUTE, 1, MBOX_VALID_USER);

        // UC: Poll for execute from SoC
        mbox_status = lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK;
        while ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) != 1) {
            mbox_status = lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK;
        }

        // UC: Read DLEN CLP_MBOX_CSR_MBOX_DLEN
        mbox_dlen = lsu_read_32(CLP_MBOX_CSR_MBOX_DLEN);
        if (mbox_dlen !=  MBOX_DLEN_VAL) {
            VPRINTF(ERROR, "ERROR: Mailbox DLEN mismatch! Expected 0x%x got 0x%x\n", MBOX_DLEN_VAL, mbox_dlen);
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
            while(1);
        }

        // UC: Read Mailbox
        for (uint32_t i = 0; i < MBOX_DLEN_VAL / 4; i++) {
            if ((mbox_data_readback = lsu_read_32(CLP_MBOX_CSR_MBOX_DATAOUT)) != mbox_data[i % 16]) {
                VPRINTF(ERROR, "ERROR: Mailbox read mismatch! Expected 0x%x got 0x%x\n", mbox_data[i % 16], mbox_data_readback);
                SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
                while(1);
            }
        }

        // UC: Set status register
        lsu_write_32(CLP_MBOX_CSR_MBOX_STATUS, (CMD_COMPLETE << MBOX_CSR_MBOX_STATUS_STATUS_LOW) & MBOX_CSR_MBOX_STATUS_STATUS_MASK);

        // SoC: Poll on status register
        while ((mbox_status = lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK) != CMD_COMPLETE);

        // SoC: Clear execute
        soc_write_user_32(CLP_MBOX_CSR_MBOX_EXECUTE, 0, MBOX_VALID_USER);

        // Assert no errors are reported after the transaction
        if (cptra_intr_rcv.soc_ifc_error != 0) {
          VPRINTF(ERROR, "ERROR: Error reported after mailbox full test!\n");
          SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
          while(1);
        }
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    }
}
