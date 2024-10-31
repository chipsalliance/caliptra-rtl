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
#include "clk_gate.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity             verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity             verbosity_g = LOW;
#endif

#define MBOX_DLEN_VAL             0x00000100

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
    .mldsa_error      = 0,
    .mldsa_notif      = 0,
    .axi_dma_error    = 0,
    .axi_dma_notif    = 0,
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
                             0x77777777,
                             0x88888888,
                             0x99999999,
                             0xaaaaaaaa,
                             0xbbbbbbbb,
                             0xcccccccc,
                             0xdddddddd,
                             0xeeeeeeee,
                             0xffffffff,
                             0x00001111,
                             0x11112222,
                             0x22223333,
                             0x33334444,
                             0x44445555,
                             0x55556666,
                             0x66667777,
                             0x77778888,
                             0x88889999,
                             0x9999aaaa,
                             0xaaaabbbb,
                             0xbbbbcccc,
                             0xccccdddd,
                             0xddddeeee,
                             0xeeeeffff,
                             0xffff0000,
                             0x00001122,
                             0x11112233,
                             0x22223344,
                             0x33334455,
                             0x44445566,
                             0x55556677,
                             0x66667788,
                             0x77778899,
                             0x888899aa,
                             0x9999aabb,
                             0xaaaabbcc,
                             0xbbbbccdd,
                             0xccccddee,
                             0xddddeeff,
                             0xeeeeff00,
                             0xffff0011,
                             0x00001123,
                             0x11112234,
                             0x22223345,
                             0x33334456,
                             0x44445567,
                             0x55556678,
                             0x66667789,
                             0x7777889a,
                             0x888899ab,
                             0x9999aabc,
                             0xaaaabbcd,
                             0xbbbbccde,
                             0xccccddef,
                             0xddddeef0,
                             0xeeeeff01,
                             0xffff0012 };
    uint32_t read_data;

    uint32_t mitb0 = 0x000000F0;
    uint32_t mie_timer0_ext_int_en = 0x20000800;

    // Message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Caliptra Mailbox Smoke Test!!\n"    );
    VPRINTF(LOW, "----------------------------------\n");

    // Call interrupt init
    init_interrupts();

    //Enable clk gating
    SEND_STDOUT_CTRL(0xf2);

    //set ready for FW so tb will push FW
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FW_MASK);

    set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

    //wait for mailbox data avail
    VPRINTF(LOW, "FW: Wait\n");
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) != MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);

    set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

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

    //Halt core while SoC is executing mbox flow
    set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

    //check FSM state, should be in EXECUTE_SOC
    state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
    if (state != MBOX_EXECUTE_SOC && ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 1)) {
        VPRINTF(ERROR, "ERROR: mailbox in unexpected state (%x) when expecting MBOX_EXECUTE_SOC (0x%x)\n", state, MBOX_EXECUTE_SOC);
        SEND_STDOUT_CTRL( 0x1);
        while(1);
    } else if ((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 0) {
        VPRINTF(LOW, "FW: Mailbox operation has ended, execute cleared to 0. Ending test with success\n");
    } else {
        VPRINTF(LOW, "FW: Mailbox in expected state, MBOX_EXECUTE_SOC. Ending test with success\n");
    }

//--------------------------------------------------------------------------------------------
    //Wait for SoC to reset execute reg
    VPRINTF(LOW, "FW: Wait for SoC to reset execute register\n");
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 1);

    set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

    //poll for mbox lock
    VPRINTF(LOW, "FW: Acquire lock to send mbox cmd\n");
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_LOCK) & MBOX_CSR_MBOX_LOCK_LOCK_MASK) == 1);

    set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

    //write command
    lsu_write_32(CLP_MBOX_CSR_MBOX_CMD,0x12345678);

    set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

    //write dlen
    lsu_write_32(CLP_MBOX_CSR_MBOX_DLEN,MBOX_DLEN_VAL);

    set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

    //write datain
    VPRINTF(LOW, "FW: Writing %d bytes to mailbox\n", MBOX_DLEN_VAL);
    for (ii = 0; ii < MBOX_DLEN_VAL/4; ii++) {
        VPRINTF(HIGH, "  datain: 0x%x\n", mbox_data[ii]);
        lsu_write_32(CLP_MBOX_CSR_MBOX_DATAIN,mbox_data[ii]);
    }

    set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

    //set execute
    lsu_write_32(CLP_MBOX_CSR_MBOX_EXECUTE, MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK);

    set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

    //Poll status until data ready is set
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_STATUS_MASK) != DATA_READY);

    set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);

    //check data 
    VPRINTF(LOW, "FW: Checking %d bytes from mailbox as if return data\n", MBOX_DLEN_VAL);
    for (ii = 0; ii < MBOX_DLEN_VAL/4; ii++) {
        if (ii % 4 == 0){
            set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);
        }
        VPRINTF(HIGH, "  datain: 0x%x\n", mbox_data[ii]);
        read_data = lsu_read_32(CLP_MBOX_CSR_MBOX_DATAOUT);
        if (read_data != mbox_data[ii]) {
            VPRINTF(ERROR, "ERROR: mailbox data mismatch actual (0x%x) expected (0x%x)\n", read_data, mbox_data[ii]);
            SEND_STDOUT_CTRL( 0x1);
            while(1);
        };
    }

    set_mit0_and_halt_core(mitb0, mie_timer0_ext_int_en);
}
