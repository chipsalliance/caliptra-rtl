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

// Assembly code for Hello World
// Not using only ALU ops for creating the string


#include "../includes/caliptra_defines.h"

#define MBOX_DLEN_VAL             0x0000001C

// Code to execute
.section .text
.global _start
_start:

    // Clear minstret
    csrw minstret, zero
    csrw minstreth, zero

    // Set up MTVEC - not expecting to use it though
    li x1, RV_ICCM_SADR
    csrw mtvec, x1

    // Enable Caches in MRAC
    li x1, 0xaaaaaaaa
    csrw 0x7c0, x1

    //set ready for FW so tb will push FW
    li x3, CLP_SOC_IFC_REG_FLOW_STATUS
    li x4, SOC_IFC_REG_FLOW_STATUS_READY_FOR_FW_MASK
    sw x4, 0(x3)

.rept 99
    nop
.endr
    //wait for mailbox data avail
    li x3, CLP_MBOX_CSR_MBOX_EXECUTE
    li x1, 0x00000001
    fw_avail_loop:
        lw x5, 0(x3)
        and x5, x5, x1
        bne x5, x1, fw_avail_loop

    //read mbox command
    li x3, CLP_MBOX_CSR_MBOX_CMD
    lw x5, 0(x3)

    //read mbox dlen
    li x3, CLP_MBOX_CSR_MBOX_DLEN
    lw x6, 0(x3)

    //read from mbox
    li x3, CLP_MBOX_CSR_MBOX_DATAOUT
    li x7, 0x00000001
    read_mbox_loop0:
        lw x8, 0(x3)
        addi x7, x7, 4
        ble x7, x6, read_mbox_loop0

    //push new data in like a response
    li x3, CLP_MBOX_CSR_MBOX_DATAIN
    li x6, MBOX_DLEN_VAL
    li x7, 0x00000000
    la x4, mbox_data
    write_mbox_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x7, x7, 4
        ble x7, x6, write_mbox_loop

    //set data ready status
    li x3, CLP_MBOX_CSR_MBOX_STATUS
    li x4, 0x1
    sw x4, 0(x3)

    //check FSM state, should be in EXECUTE_SOC
    li x3, CLP_MBOX_CSR_MBOX_STATUS
    lw x4, 0(x3)
    li x5, 0x00000040
    and x4, x4, x5
    bne x5, x4, _finish_fail

    // Load string from hw_data
    // and write to stdout address
    li x3, STDOUT
    la x4, hello_world

loop:
    lb x5, 0(x4)
    sb x5, 0(x3)
    addi x4, x4, 1
    bnez x5, loop

    beq x0, x0, _finish_pass

// Write 0x01 to STDOUT for TB to terminate test with fail.
_finish_fail:
    li x3, STDOUT
    addi x5, x0, 0x01
    sb x5, 0(x3)
    beq x0, x0, _finish_fail

// Write 0xff to STDOUT for TB to terminate test with pass.
_finish_pass:
    li x3, STDOUT
    addi x5, x0, 0xff
    sb x5, 0(x3)
    beq x0, x0, _finish_pass
.rept 99
    nop
.endr

.align 4
mbox_data:
.word 0x00000000    
.word 0x11111111
.word 0x22222222
.word 0x33333333
.word 0x44444444
.word 0x55555555
.word 0x66666666
.word 0x77777777
hello_world:
.ascii "----------------------------------\n"
.ascii "Hello World from SweRV EL2 @WDC !!\n"
.ascii "----------------------------------\n"
.word 0
.word 0
.word 0
