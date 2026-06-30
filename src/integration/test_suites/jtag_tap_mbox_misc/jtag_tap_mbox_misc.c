// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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
#include "soc_ifc.h"
#include "soc_access.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define FAIL(...) do { VPRINTF(ERROR, __VA_ARGS__); SEND_STDOUT_CTRL(0x1); for(;;); } while(0);

#define TB_CMD_TEST_PASS          0xFF
#define MBOX_DLEN_VAL             0x00000020
#define MBOX_VALID_USER           0xFFFFFFFF

/* --------------- Function Definitions --------------- */
static void mbox_wait_for_tap_dataout_steal() {
    for (int i = 0; i < 1000; i++)
        if (soc_ifc_mbox_read_rdptr() > 1)
            return;
    FAIL("ERROR: TAP did not steal the value from MBOX after 1000 iterations\n");
}

void main() {

    // Production mode
    lsu_write_32(STDOUT, 0x157F);
    // Enable debug intent
    lsu_write_32(STDOUT, 0x167F);
    lsu_write_32(STDOUT, 0x127F);
    // Enter debug unlocked
    lsu_write_32(STDOUT, 0x187F);

    // Initialize interrupts (if any)
    init_interrupts();

    mbox_op_s op;
    uint32_t ii;
    uint32_t data;
    enum mbox_fsm_e state;
    enum mbox_status_e status;
    uint32_t mbox_data[] = { 0x00000000,
                             0x11111111,
                             0x22222222,
                             0x33333333,
                             0x44444444,
                             0x55555555,
                             0x66666666,
                             0x77777777 };

    uint32_t exp_mbox_data[] = { 0x77777777,
                                 0x66666666,
                                 0x55555555,
                                 0x44444444,
                                 0x33333333,
                                 0x22222222,
                                 0x11111111,
                                 0x00000000 };
    uint32_t mbox_cmd = 0xaface0ff;
    uint32_t exp_mbox_cmd = 0x4e110df7;
    uint32_t read_data;

    VPRINTF(LOW, "-------------------------------\n");
    VPRINTF(LOW, " Mailbox coverage corner cases\n" );
    VPRINTF(LOW, "-------------------------------\n");

    VPRINTF(LOW, "FW: Test 1 - SoC mailbox access request while TAP locks the mailbox\n");

    // Enable injection of SoC mailbox access request
    VPRINTF(LOW, "FW: Enable injection of SoC mailbox access request\n");
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x507F);

    // Make tap mailbox available
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK);

    // Put mailbox in tap mode
    lsu_write_32(CLP_MBOX_CSR_TAP_MODE, MBOX_CSR_TAP_MODE_ENABLED_MASK);

    // Poll status until TAP locks it
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_TAP_HAS_LOCK_MASK) == 0);

    // Disable injection of SoC mailbox access request
    VPRINTF(LOW, "FW: Disable injection of SoC mailbox access request\n");
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x517F);

    // Force unlock
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);


    VPRINTF(LOW, "FW: Test 2 - Send to mailbox from JTAG with TAP enabled\n");

    // Poll status until fsm is in EXECUTE UC
    VPRINTF(LOW, "FW: Wait for mailbox to enter EXECUTE_UC state\n");
    state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    while (state != MBOX_EXECUTE_UC) {
      state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    }

    // Check cmd
    VPRINTF(LOW, "FW: Checking cmd from tap\n");
    read_data = lsu_read_32(CLP_MBOX_CSR_MBOX_CMD);
    if (read_data != mbox_cmd)
      FAIL("ERROR: mailbox cmd mismatch actual (0x%x) expected (0x%x)\n", read_data, mbox_cmd);

    // Check data
    VPRINTF(LOW, "FW: Checking %d bytes from tap\n", MBOX_DLEN_VAL);
    for (ii = 0; ii < MBOX_DLEN_VAL/4; ii++) {
        VPRINTF(HIGH, "  datain: 0x%x\n", mbox_data[ii]);
        read_data = soc_ifc_mbox_read_dataout_single();
        if (read_data != mbox_data[ii])
            FAIL("ERROR: mailbox data mismatch actual (0x%x) expected (0x%x)\n", read_data, mbox_data[ii]);
    }

    // Write command
    lsu_write_32(CLP_MBOX_CSR_MBOX_CMD, exp_mbox_cmd);

    // Write dlen
    lsu_write_32(CLP_MBOX_CSR_MBOX_DLEN, MBOX_DLEN_VAL);

    // Write datain
    VPRINTF(LOW, "FW: Writing %d bytes to mailbox\n", MBOX_DLEN_VAL);
    for (ii = 0; ii < MBOX_DLEN_VAL/4; ii++) {
        VPRINTF(HIGH, "  datain: 0x%x\n", exp_mbox_data[ii]);
        lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN, exp_mbox_data[ii]);
    }

    status = DATA_READY;

    soc_ifc_set_mbox_status_field(status);


    VPRINTF(LOW, "FW: Test 3 - TAP disable in EXECUTE_TAP\n");

    // Poll status until fsm is in IDLE state
    VPRINTF(LOW, "FW: Wait for mailbox to enter IDLE state\n");
    do {
      state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    } while (state != MBOX_IDLE);

    VPRINTF(LOW, "FW: Locking mailbox\n");
    //poll for mbox lock
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 1);

    VPRINTF(LOW, "FW: Writing request to mailbox\n");
    // Write command
    lsu_write_32(CLP_MBOX_CSR_MBOX_CMD,0xaface0ff);

    // Write dlen
    lsu_write_32(CLP_MBOX_CSR_MBOX_DLEN,MBOX_DLEN_VAL);

    // Write datain
    VPRINTF(LOW, "FW: Writing %d bytes to mailbox\n", MBOX_DLEN_VAL);
    for (ii = 0; ii < MBOX_DLEN_VAL/4; ii++) {
        VPRINTF(HIGH, "  datain: 0x%x\n", mbox_data[ii]);
        lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN,mbox_data[ii]);
    }

    // Set execute
    VPRINTF(LOW, "FW: Setting mailbox to execute\n");
    lsu_write_32(CLP_MBOX_CSR_MBOX_EXECUTE, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);

    VPRINTF(LOW, "FW: Waiting for mailbox to enter EXECUTE_TAP state\n");
    // Poll status until fsm is in EXECUTE TAP state
    do  {
        state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    } while (state != MBOX_EXECUTE_TAP);

    // Disable TAP_MODE to hit missing cond
    VPRINTF(LOW, "FW: Disabling TAP mode\n");
    lsu_write_32(CLP_MBOX_CSR_TAP_MODE, 0);

    // Poll status until TAP notifies it is ready for data
    VPRINTF(LOW, "FW: Waiting for mailbox to be ready for data \n");
    do  {
        status = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK) >> MBOX_CSR_MBOX_STATUS_STATUS_LOW;
    } while (status == CMD_BUSY);

    // Enable TAP_MODE to finish the test gracefully
    VPRINTF(LOW, "FW: Enabling TAP mode\n");
    lsu_write_32(CLP_MBOX_CSR_TAP_MODE, MBOX_CSR_TAP_MODE_ENABLED_MASK);

    // Poll status until data ready is set
    VPRINTF(LOW, "FW: Waiting for mailbox to be ready for data \n");
    do  {
        status = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK) >> MBOX_CSR_MBOX_STATUS_STATUS_LOW;
    } while (status != DATA_READY);

    // Check cmd
    VPRINTF(LOW, "FW: Checking CMD from TAP\n");
    read_data = lsu_read_32(CLP_MBOX_CSR_MBOX_CMD);
    if (read_data != exp_mbox_cmd)
      FAIL("ERROR: mailbox cmd mismatch actual (0x%x) expected (0x%x)\n", read_data, exp_mbox_cmd);

    // Check data
    VPRINTF(LOW, "FW: Checking %d bytes from TAP\n", MBOX_DLEN_VAL);
    for (ii = 0; ii < MBOX_DLEN_VAL/4; ii++) {
        VPRINTF(HIGH, "  datain: 0x%x\n", exp_mbox_data[ii]);
        read_data = soc_ifc_mbox_read_dataout_single();
        if (read_data != exp_mbox_data[ii])
            FAIL("ERROR: mailbox data mismatch actual (0x%x) expected (0x%x)\n", read_data, exp_mbox_data[ii]);
    }

    // Clear execute
    lsu_write_32(CLP_MBOX_CSR_MBOX_EXECUTE, 0);


    VPRINTF(LOW, "FW: Test 4 - TAP mbox lock read during FW lock\n");

    // Enable injection of TAP mailbox lock request
    VPRINTF(LOW, "FW: Enable injection of TAP mailbox lock request\n");
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x587F);

    VPRINTF(LOW, "FW: Locking mailbox\n");
    // Poll for mbox lock
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 1);

    // Disable injection of TAP mailbox lock request
    VPRINTF(LOW, "FW: Disable injection of TAP mailbox lock request\n");
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x597F);

    // Force unlock
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);


    // This covers the condition of TAP stealing data from an MBOX
    // transaction (SoC -> uC -> SoC) by issuing a dataout read
    // when mbox is in EXECUTE_UC or EXECUTE_SOC state
    VPRINTF(LOW, "FW: Test 5 - SoC to uC mbox flow with TAP dataout stealing\n");

    // ensure disabled TAP mode
    lsu_write_32(CLP_MBOX_CSR_TAP_MODE, 0);

    // let SoC lock MBOX
    lsu_write_32(CLP_MBOX_CSR_MBOX_LOCK, MBOX_CSR_MBOX_LOCK_LOCK_MASK);
    while((soc_read_user_32(CLP_MBOX_CSR_MBOX_LOCK, MBOX_VALID_USER).rdata & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 1);

    VPRINTF(LOW, "FW: Issuing MBOX request from SoC\n");
    exp_mbox_cmd = 0x00dad5ad;
    soc_write_user_32(CLP_MBOX_CSR_MBOX_CMD, exp_mbox_cmd, MBOX_VALID_USER);
    soc_write_user_32(CLP_MBOX_CSR_MBOX_DLEN, MBOX_DLEN_VAL, MBOX_VALID_USER);
    for (int i = 0; i < MBOX_DLEN_VAL/4; i++)
        soc_write_user_32(CLP_MBOX_CSR_MBOX_DATAIN, mbox_data[i], MBOX_VALID_USER);
    soc_write_user_32(CLP_MBOX_CSR_MBOX_EXECUTE, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK, MBOX_VALID_USER);

    mbox_wait_for_tap_dataout_steal();

    // handle the request as uC
    uint32_t rd_cmd = lsu_read_32(CLP_MBOX_CSR_MBOX_CMD);
    uint32_t rd_dlen = lsu_read_32(CLP_MBOX_CSR_MBOX_DLEN);
    if (rd_cmd != exp_mbox_cmd)
        FAIL("ERROR: mailbox cmd mismatch actual (0x%x) expected (0x%x)\n", rd_cmd, exp_mbox_cmd);
    if (rd_dlen != MBOX_DLEN_VAL)
        FAIL("ERROR: mailbox dlen mismatch actual (0x%x) expected (0x%x)\n", rd_dlen, MBOX_DLEN_VAL);
    for (int i = 0; i < (MBOX_DLEN_VAL-1)/4; i++) {
        read_data = soc_ifc_mbox_read_dataout_single();
        if (read_data != mbox_data[i+1])
            FAIL("ERROR: mailbox data mismatch, expected 0x%x, actual 0x%x\n", mbox_data[i+1], read_data);
    }

    VPRINTF(LOW, "FW: Sending MBOX response to SoC\n");
    lsu_write_32(CLP_MBOX_CSR_MBOX_DLEN, MBOX_DLEN_VAL);
    for (int i = (MBOX_DLEN_VAL-1)/4; i >= 0; i--) // send response in reverse
        lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN, mbox_data[i]);
    soc_ifc_set_mbox_status_field(DATA_READY);

    mbox_wait_for_tap_dataout_steal();

    // Coverage case: MBOX in EXECUTE_SOC state, waiting for SoC to read uC response.
    // Meanwhile another valid MBOX user, other than the one who started the request
    // tries to read DATAOUT. Checks if the data was masked correctly.
    {
        // Introduce another valid AXI user in the third slot
        uint32_t new_axi_user = 0x223344ff;
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3, new_axi_user);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3, 1);

        uint32_t rdptr = soc_ifc_mbox_read_rdptr();
        uint32_t dataout = soc_read_user_32(CLP_MBOX_CSR_MBOX_DATAOUT, new_axi_user).rdata;
        if (soc_ifc_mbox_read_rdptr() != rdptr)
            FAIL("ERROR: DATAOUT access as a valid MBOX user other than the requester increased the rdptr and returned a value: 0x%x\n", dataout);
    }

    VPRINTF(LOW, "FW: Verifying MBOX response\n");
    uint32_t rdata[MBOX_DLEN_VAL/4] = {};
    if(soc_access_32((axi_req_t) {
        .addr = CLP_MBOX_CSR_MBOX_DATAOUT,
        .burst = AXI_BURST_FIXED,
        .axuser = MBOX_VALID_USER,
        .len = MBOX_DLEN_VAL/4,
        .rdata = rdata,
        .read = true
    }).resp)
        FAIL("ERROR: mailbox dataout SoC AXI read burst failed\n");

    for (int i = 0; i < (MBOX_DLEN_VAL-1)/4; i++)
        if (rdata[i] != exp_mbox_data[i+1])
            FAIL("ERROR: mailbox data mismatch, expected 0x%x, actual 0x%x\n", exp_mbox_data[i+1], rdata[i]);

    // finalize request, clear EXECUTE register
    soc_write_user_32(CLP_MBOX_CSR_MBOX_EXECUTE, 0, MBOX_VALID_USER);

    VPRINTF(LOW, "FW: Assure mbox is in the idle state\n");
    state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    while (state != MBOX_IDLE) {
      state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    }

    VPRINTF(LOW, "FW: Test 6 - Access mbox from TAP with mbox TAP set to unavailable\n");

    // Poll status until TAP locks it
    VPRINTF(LOW, "FW: Wait for TAP to lock\n");
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_TAP_HAS_LOCK_MASK) == 0);

    // Make tap mailbox unavailable
    VPRINTF(LOW, "FW: Make mbox TAP unavailable\n");
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP, 0);

    // Let JTAG finish the test
    while(1);
}
