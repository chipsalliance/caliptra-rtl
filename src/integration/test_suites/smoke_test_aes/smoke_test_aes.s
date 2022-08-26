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
#include "./smoke_test_aes_vectors.s"

#define DCCM_SADR                   0xf0040000

#define AES_ADDR_NAME0            0x60000000
#define AES_ADDR_NAME1            0x60000004
#define AES_ADDR_VER0             0x60000008
#define AES_ADDR_VER1             0x6000000c
#define AES_ADDR_CNTRL            0x60000010
#define AES_ADDR_STATUS           0x60000018
#define AES_ADDR_KEY_START        0x60000040
#define AES_ADDR_KEY_END          0x6000005f
#define AES_ADDR_BLOCK_START      0x60000080
#define AES_ADDR_BLOCK_END        0x6000008f
#define AES_ADDR_RESULT_START     0x60000100
#define AES_ADDR_RESULT_END       0x6000010f
#define AES_ADDR_CONFIG           0x60000020
#define AES_ADDR_IV_START         0x60000110
#define AES_ADDR_IV_END           0x6000011f

#define AES_INIT                  0x0000000D
#define AES_NEXT                  0x0000000E
#define AES_VALID                 0x00000003

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

    // read info
    la x4, CBCMMT256
    // key length and operation mode
    lw t3, 0(x4)
    addi x4, x4, 4
    // message length
    lw t4, 0(x4)

    // Load the key and write to AES core
    li x3, AES_ADDR_KEY_START
    li x1, AES_ADDR_KEY_END
    la x4, CBCMMT256
    addi x4, x4, 8
    write_key_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        ble x3, x1, write_key_loop

    // indicate key length
    //************* select one for 128/256bit key *************//
    // 256bit key
    // li x4, 0x02     
    // 128bit key
    // li x4, 0x00     
    li x4, 0x02
    and x4, t3, x4
    li x3, AES_ADDR_CONFIG
    sw x4, 0(x3)

    // Enable AES initialization
    li x3, AES_ADDR_CNTRL
    li x4, 0x01
    sw x4, 0(x3)

    // wait 8 cycles for ADDR_STATUS to set to 0x0
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    // wait for initialization get finished
    li x3, AES_ADDR_STATUS
    li x1, 0x00
    ready_int_loop:
        lw x5, 0(x3)
        beq x5, x1, ready_int_loop

    // Write IV
    li x3, AES_ADDR_IV_START
    li x1, AES_ADDR_IV_END
    la x4, CBCMMT256
    addi x4, x4, 40
    write_IV_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        ble x3, x1, write_IV_loop

    // multi-block message loop
    li x8, 0

    multi_block_loop:
        addi x8, x8, 1

        // Load message and write to AES core
        li x3, AES_ADDR_BLOCK_START
        li x1, AES_ADDR_BLOCK_END
        la x4, CBCMMT256
        addi x4, x4, 56
        write_block_loop1:
            lw x5, 0(x4)
            sw x5, 0(x3)
            addi x4, x4, 4
            addi x3, x3, 4
            ble x3, x1, write_block_loop1

        // configure to encoder
        li x3, AES_ADDR_CONFIG    
        sw t3, 0(x3)

        // Enable AES core
        li x3, AES_ADDR_CNTRL
        li x4, 0x02
        sw x4, 0(x3)

        // wait for AES process
        li x3, AES_ADDR_STATUS
        li x1, AES_VALID
        ready_loop1:
            lw x5, 0(x3)
            bne x5, x1, ready_loop1

        // Read the data back from AES register
        li x3, AES_ADDR_RESULT_START
        li x1, AES_ADDR_RESULT_END
        la x4, CBCMMT256
        addi x4, x4, 72
        read_result_loop1:
            lw x5, 0(x3)
            lw x2, 0(x4)
            beq x5, x2, equal1
            li x6, STDOUT
            li x7, 0x01
            sb x7, 0(x6)
            equal1:
                addi x3, x3, 4
                addi x4, x4, 4
                ble x3, x1, read_result_loop1

        // check if finished
        bne x8, t4, multi_block_loop

// Write 0xff to STDOUT for TB to termiate test.
_finish:
    li x3, STDOUT
    addi x5, x0, 0xff
    sb x5, 0(x3)
    beq x0, x0, _finish
.rept 99
    nop
.endr
