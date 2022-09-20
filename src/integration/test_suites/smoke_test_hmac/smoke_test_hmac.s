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
    la x4, key_data
    write_key_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        ble x3, x1, write_key_loop

    // Load block from hw_data and write to HMAC core
    li x3, HMAC_ADDR_BLOCK_START
    li x1, HMAC_ADDR_BLOCK_END
    la x4, block_data
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
    la x4, expected_data
    read_result_loop:
        lw x5, 0(x3)
        lw x2, 0(x4)
        beq x5, x2, equal
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        beq x0, x0, _terminate
        equal:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_result_loop
        

// Write 0xff to STDOUT for TB to termiate test.
_finish:
    li x3, STDOUT
    addi x5, x0, 0xff
    sb x5, 0(x3)
    beq x0, x0, _finish
_terminate:
.rept 99
    nop
.endr

.data
key_data:
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
block_data:
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
expected_data:
.word 0xb6a8d563
.word 0x6f5c6a72
.word 0x24f9977d
.word 0xcf7ee6c7
.word 0xfb6d0c48
.word 0xcbdee973
.word 0x7a959796
.word 0x489bddbc
.word 0x4c5df61d
.word 0x5b3297b4
.word 0xfb68dab9
.word 0xf1b582c2
print_data:
.ascii "----------------------------------\n"
.ascii " HMAC smoke test !!\n"
.ascii "----------------------------------\n"
.byte 0
