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


#include "../includes/defines.h"

#define STDOUT 0xd0580000
#define DCCM_SADR                   0xf0040000

#define MBOX_ADDR_BASE            0x30000000
#define MBOX_ADDR_LOCK            0x30000000
#define MBOX_ADDR_CMD             0x30000008
#define MBOX_ADDR_DLEN            0x3000000C
#define MBOX_ADDR_DATAIN          0x30000010
#define MBOX_ADDR_DATAOUT         0x30000014
#define MBOX_ADDR_EXECUTE         0x30000018

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
    li x1, 0x5f5555A5
    csrw 0x7c0, x1

    //poll for lock register
    li x3, MBOX_ADDR_LOCK
    li x1, 0x00000001
    lock_poll_loop:
        lw x5, 0(x3)
        and x5, x5, x1
        bne x5, x0, lock_poll_loop

    //write to MBOX_ADDR_CMD
    li x3, MBOX_ADDR_CMD
    li x5, 0xDEADBEEF
    sw x5, 0(x3)

    //write to MBOX_ADDR_DLEN
    li x3, MBOX_ADDR_DLEN
    li x5, MBOX_DLEN_VAL
    sw x5, 0(x3)

    //write to MBOX_ADDR_DATAIN
    li x3, MBOX_ADDR_DATAIN
    li x6, MBOX_DLEN_VAL
    li x7, 0x00000000
    la x4, mbox_data
    write_mbox_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x7, x7, 4
        ble x7, x6, write_mbox_loop

    //write to MBOX_ADDR_EXECUTE
    li x3, MBOX_ADDR_EXECUTE
    li x5, 0x00000001
    sw x5, 0(x3)

    //read from MBOX_ADDR_DATAOUT
    li x3, MBOX_ADDR_DATAOUT
    li x6, MBOX_DLEN_VAL
    li x7, 0x00000000
    la x4, mbox_data
    read_mbox_loop:
        lw x5, 0(x3)
        lw x8, 0(x4)
        bne x5, x8, _finish_fail
        addi x4, x4, 4
        addi x7, x7, 4
        ble x7, x6, read_mbox_loop

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

.data
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
.byte 0
