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

#define DCCM_SADR                   0xf0040000

<<<<<<< HEAD
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

#define HMAC_INIT                 0x0000000D
#define HMAC_NEXT                 0x0000000E
#define HMAC_VALID                0x00000003
=======
#define SHA512_ADDR_NAME            0x40000000
#define SHA512_ADDR_VER             0x40000008
#define SHA512_ADDR_CNTRL           0x40000010
#define SHA512_ADDR_STATUS          0x40000018
#define SHA512_ADDR_BLOCK_START     0x40000080
#define SHA512_ADDR_BLOCK_END       0x400000ff
#define SHA512_ADDR_DIGEST_START    0x40000100
#define SHA512_ADDR_DIGEST_END      0x4000013f

#define SHA512_INIT                 0x0000000D
#define SHA512_NEXT                 0x0000000E
#define SHA512_VALID                0x00000003
>>>>>>> master

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
<<<<<<< HEAD
    li x1, 0x5f555555
    li x1, 0xafaaaaaa
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
=======
    li x1, 0xaaaaaaaa
    csrw 0x7c0, x1

    // Load block from hw_data and write to SHA512 core
    li x3, SHA512_ADDR_BLOCK_START
    li x1, SHA512_ADDR_BLOCK_END
    la x4, hw_data
>>>>>>> master
    write_block_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        ble x3, x1, write_block_loop

<<<<<<< HEAD
    // Enable HMAC core
    li x3, HMAC_ADDR_CNTRL
    li x4, HMAC_INIT
    sw x4, 0(x3)

    // wait for HMAC process
    li x3, HMAC_ADDR_STATUS
    li x1, HMAC_VALID
=======
    // Enable SHA512 core
    li x3, SHA512_ADDR_CNTRL
    li x4, SHA512_INIT
    sw x4, 0(x3)

    // wait for SHA512 process
    li x3, SHA512_ADDR_STATUS
    li x1, SHA512_VALID
>>>>>>> master
    ready_loop:
        lw x5, 0(x3)
        bne x5, x1, ready_loop

<<<<<<< HEAD
    // Read the data back from HMAC register
    li x3, HMAC_ADDR_TAG_START
    li x1, HMAC_ADDR_TAG_END
    la x4, hw_data
    addi x4, x4, 176
    read_result_loop:
        lw x5, 0(x3)
        lw x2, 0(x4)
        beq x5, x2, equal
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal:
=======
    // Read the data back from SHA512 register
    li x3, SHA512_ADDR_DIGEST_START
    li x1, SHA512_ADDR_DIGEST_END
    la x4, hw_data
    addi x4, x4, 32
    read_result_loop:
        lw x5, 0(x3)
        lw x2, 0(x4)
        beq x5, x2, equal4
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal4:
>>>>>>> master
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_result_loop
        

// Write 0xff to STDOUT for TB to termiate test.
_finish:
    li x3, STDOUT
    addi x5, x0, 0xff
    sb x5, 0(x3)
    beq x0, x0, _finish
<<<<<<< HEAD
.rept 99
=======
.rept 100
>>>>>>> master
    nop
.endr

.data
hw_data:
<<<<<<< HEAD
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
=======
// start of input message
.word 0x61626380
.word 0x00000000
.word 0x00000000
>>>>>>> master
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
<<<<<<< HEAD
.word 0x00000440
// expected value
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
.ascii "----------------------------------\n"
.ascii " HMAC smoke test !!\n"
=======
.word 0x00000018
// expected value
.word 0xDDAF35A1
.word 0x93617ABA
.word 0xCC417349
.word 0xAE204131
.word 0x12E6FA4E
.word 0x89A97EA2
.word 0x0A9EEEE6
.word 0x4B55D39A
.word 0x2192992A
.word 0x274FC1A8
.word 0x36BA3C23
.word 0xA3FEEBBD
.word 0x454D4423
.word 0x643CE80E
.word 0x2A9AC94F
.word 0xA54CA49F
.ascii "----------------------------------\n"
.ascii "SHA512 test !!\n"
>>>>>>> master
.ascii "----------------------------------\n"
.byte 0
