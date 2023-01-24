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
#include <stdint.h>
#include "printf.h"
#include "riscv_hw_if.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count       = 0;

#define MBOX_DLEN_VAL             0x00000020

enum mbox_status_e {
    CMD_BUSY     = 0,
    DATA_READY   = 1,
    CMD_COMPLETE = 2,
    CMD_FAILURE  = 3,
};
enum mbox_fsm_e {
    MBOX_IDLE         = 0x0,
    MBOX_RDY_FOR_CMD  = 0x1,
    MBOX_RDY_FOR_DLEN = 0x3,
    MBOX_RDY_FOR_DATA = 0x2,
    MBOX_EXECUTE_UC   = 0x6,
    MBOX_EXECUTE_SOC  = 0x4,
};

void main () {

    uint32_t cmd;
    uint32_t dlen;
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

    // Message
    printf("----------------------------------\n");
    printf(" Caliptra Mailbox Smoke Test!!\n"    );
    printf("----------------------------------\n");

    //set ready for FW so tb will push FW
    printf("FW: Set ready for FW\n");
    lsu_write_32((uint32_t*) CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS,SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FW_MASK);

    // Sleep
    for (uint16_t slp = 0; slp < 33; slp++);

    //wait for mailbox data avail
    printf("FW: Wait\n");
    while((lsu_read_32((uint32_t*) CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) != MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);

    //read mbox command
    cmd = lsu_read_32((uint32_t*) CLP_MBOX_CSR_MBOX_CMD);
    printf("FW: CMD from mailbox: 0x%x\n", cmd);

    //read mbox dlen
    dlen = lsu_read_32((uint32_t*) CLP_MBOX_CSR_MBOX_DLEN);
    printf("FW: DLEN from mailbox: 0x%x\n", dlen);

    //read from mbox
    printf("FW: Reading %d bytes from mailbox\n", dlen);
    while(dlen) {
        data = lsu_read_32((uint32_t*) CLP_MBOX_CSR_MBOX_DATAOUT);
        printf("  dataout: 0x%x\n", data);
        if (dlen < 4) {
            dlen=0;
        } else {
            dlen-=4;//sizeof(uint32_t);
        }
    }

    //push new data in like a response
    printf("FW: Writing %d bytes to mailbox\n", MBOX_DLEN_VAL);
    for (dlen = 0; dlen < MBOX_DLEN_VAL/4; dlen++) {
        printf("  datain: 0x%x\n", mbox_data[dlen]);
        lsu_write_32((uint32_t*) CLP_MBOX_CSR_MBOX_DATAIN,mbox_data[dlen]);
    }

    //set data ready status
    printf("FW: Set data ready status\n");
    lsu_write_32((uint32_t*) CLP_MBOX_CSR_MBOX_STATUS,DATA_READY);

    //check FSM state, should be in EXECUTE_SOC
    state = (lsu_read_32((uint32_t*) CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    if (state != MBOX_EXECUTE_SOC) {
        printf("ERROR: mailbox in unexpected state (%x) when expecting MBOX_EXECUTE_SOC (0x%x)\n", state, MBOX_EXECUTE_SOC);
        printf("%c", 0x1);
        while(1);
    } else {
        printf("FW: Mailbox in expected state, MBOX_EXECUTE_SOC, ending test with success\n");
    }

}
