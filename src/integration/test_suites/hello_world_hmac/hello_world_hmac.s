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

#define DCCM_SADR                   0xf0040000

#define HMAC_ADDR_NAME            0x10010000
#define HMAC_ADDR_VER             0x10010008
#define HMAC_ADDR_CNTRL           0x10010010
#define HMAC_ADDR_STATUS          0x10010018
#define HMAC_ADDR_KEY_START       0x10010040
#define HMAC_ADDR_KEY_END         0x1001006c
#define HMAC_ADDR_BLOCK_START     0x10010080
#define HMAC_ADDR_BLOCK_END       0x100100fc
#define HMAC_ADDR_TAG_START       0x10010100
#define HMAC_ADDR_TAG_END         0x1001012c

#define HMAC_INIT                 0x00000001
#define HMAC_NEXT                 0x00000002
#define HMAC_VALID                0x00000003

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


    // Load key from hw_data and write to HMAC core
    li x3, HMAC_ADDR_KEY_START
    li x1, HMAC_ADDR_KEY_END
    la x4, hw_data
    write_key_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        ble x3, x1, write_key_loop

    // Load block from hw_data and write to HMAC core
    li x3, HMAC_ADDR_BLOCK_START
    li x1, HMAC_ADDR_BLOCK_END
    la x4, hw_data
    addi x4, x4, 48
    write_block_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        ble x3, x1, write_block_loop

    // Enable HMAC core
    li x3, HMAC_ADDR_CNTRL
    li x4, HMAC_INIT
    sw x4, 0(x3)

    // wait for HMAC process
    li x3, HMAC_ADDR_STATUS
    li x1, HMAC_VALID
    ready_loop:
        lw x5, 0(x3)
        bne x5, x1, ready_loop

    // Read the data back from HMAC register
    li x3, HMAC_ADDR_TAG_START
    li x1, HMAC_ADDR_TAG_END
    read_result_loop:
        lw x5, 0(x3)
        addi x3, x3, 4
        ble x3, x1, read_result_loop
        

// Write 0xff to STDOUT for TB to termiate test.
_finish:
    li x3, STDOUT
    addi x5, x0, 0xff
    sb x5, 0(x3)
    beq x0, x0, _finish
.rept 99
    nop
.endr

.data
hw_data:
//this is the key 384-bit
.word 0x0b0b0b0b
.word 0x0b0b0b0b
.word 0x0b0b0b0b
.word 0x0b0b0b0b
.word 0x0b0b0b0b
.word 0x0b0b0b0b
.word 0x0b0b0b0b
.word 0x0b0b0b0b
.word 0x0b0b0b0b
.word 0x0b0b0b0b
.word 0x0b0b0b0b
.word 0x0b0b0b0b
//this is the block 1024-bit
.word 0x48692054
.word 0x68657265
.word 0x80000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000440
.ascii "----------------------------------\n"
.ascii "Hello World from VeeR EL2  !!\n"
.ascii "----------------------------------\n"
.byte 0
