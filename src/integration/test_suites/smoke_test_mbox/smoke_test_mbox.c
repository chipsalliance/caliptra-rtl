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
#include "soc_ifc.h"
#include <stdint.h>
#include "printf.h"
#include "caliptra_isr.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity             verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity             verbosity_g = LOW;
#endif

#define MBOX_DLEN_VAL             0x00000020

volatile caliptra_intr_received_s cptra_intr_rcv = {
    .doe_error        = 0,
    .doe_notif        = 0,
    .ecc_error        = 0,
    .ecc_notif        = 0,
    .hmac_error       = 0,
    .hmac_notif       = 0,
    .kv_error         = 0,
    .kv_notif         = 0,
    .sha512_error     = 0,
    .sha512_notif     = 0,
    .sha256_error     = 0,
    .sha256_notif     = 0,
    .qspi_error       = 0,
    .qspi_notif       = 0,
    .uart_error       = 0,
    .uart_notif       = 0,
    .i3c_error        = 0,
    .i3c_notif        = 0,
    .soc_ifc_error    = 0,
    .soc_ifc_notif    = 0,
    .sha512_acc_error = 0,
    .sha512_acc_notif = 0,
};

void main () {

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
                             0x77777777 };
    uint32_t read_data;

    // Message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Caliptra Mailbox Smoke Test!!\n"    );
    VPRINTF(LOW, "----------------------------------\n");

    //set ready for FW so tb will push FW
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FW_MASK);

    // Sleep
    for (uint16_t slp = 0; slp < 33; slp++);

    //wait for mailbox data avail
    VPRINTF(LOW, "FW: Wait\n");
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) != MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);

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

    //check FSM state, should be in EXECUTE_SOC
    state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    if (state != MBOX_EXECUTE_SOC) {
        VPRINTF(ERROR, "ERROR: mailbox in unexpected state (%x) when expecting MBOX_EXECUTE_SOC (0x%x)\n", state, MBOX_EXECUTE_SOC);
        SEND_STDOUT_CTRL( 0x1);
        while(1);
    } else {
        VPRINTF(LOW, "FW: Mailbox in expected state, MBOX_EXECUTE_SOC, ending test with success\n");
    }

    //Wait for SoC to reset execute reg
    VPRINTF(LOW, "FW: Wait for SoC to reset execute register\n");
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 1);

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

    //Poll status until data ready is set
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK) != DATA_READY);

    //check data 
    VPRINTF(LOW, "FW: Checking %d bytes from mailbox as if return data\n", MBOX_DLEN_VAL);
    for (ii = 0; ii < MBOX_DLEN_VAL/4; ii++) {
        VPRINTF(HIGH, "  datain: 0x%x\n", mbox_data[ii]);
        read_data = lsu_read_32(CLP_MBOX_CSR_MBOX_DATAOUT);
        if (read_data != mbox_data[ii]) {
            VPRINTF(ERROR, "ERROR: mailbox data mismatch actual (0x%x) expected (0x%x)\n", read_data, mbox_data[ii]);
            SEND_STDOUT_CTRL( 0x1);
            while(1);
        };
    }
}
