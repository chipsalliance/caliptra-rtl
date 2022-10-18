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


    // Load the key and write to AES core
    li x3, AES_ADDR_KEY_START
    li x1, AES_ADDR_KEY_END
    la x4, hw_data      // 128bit key
    //************* uncomment for 256bit key *************//
    // please add the256bit key after the 128bit key//
    // addi x4, x4, 32
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
    li x4, 0x00
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
    la x4, hw_data
    addi x4, x4, 32
    write_IV_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        ble x3, x1, write_IV_loop

    //************* 1st block *************//
    // Load block from hw_data and write to AES core
    li x3, AES_ADDR_BLOCK_START
    li x1, AES_ADDR_BLOCK_END
    la x4, hw_data
    addi x4, x4, 48
    write_block_loop1:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        ble x3, x1, write_block_loop1

    // configure to encoder
    li x3, AES_ADDR_CONFIG
    // 128bit key, encode
    li x4, 0x01
    // 256bit key, encode
    // li x4, 0x03
    // 128bit key, decode
    // li x4, 0x00
    // 256bit key, decode
    // li x4, 0x02
    sw x4, 0(x3)

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
    la x4, hw_data
    addi x4, x4, 112
    read_result_loop1:
        lw x5, 0(x3)
        lw t3, 0(x4)
        beq x5, t3, equal1
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal1:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_result_loop1


    //************* 2nd block *************//
    // Load block from hw_data and write to AES core
    li x3, AES_ADDR_BLOCK_START
    li x1, AES_ADDR_BLOCK_END
    la x4, hw_data
    addi x4, x4, 64
    write_block_loop2:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        ble x3, x1, write_block_loop2

    // configure to encoder
    li x3, AES_ADDR_CONFIG
    // 128bit key, encode
    li x4, 0x01
    // 256bit key, encode
    // li x4, 0x03
    // 128bit key, decode
    // li x4, 0x00
    // 256bit key, decode
    // li x4, 0x02
    sw x4, 0(x3)

    // Enable AES core
    li x3, AES_ADDR_CNTRL
    li x4, 0x02
    sw x4, 0(x3)

    // wait for AES process
    li x3, AES_ADDR_STATUS
    li x1, AES_VALID
    ready_loop2:
        lw x5, 0(x3)
        bne x5, x1, ready_loop2

    // Read the data back from AES register
    li x3, AES_ADDR_RESULT_START
    li x1, AES_ADDR_RESULT_END
    la x4, hw_data
    addi x4, x4, 128
    read_result_loop2:
        lw x5, 0(x3)
        lw t3, 0(x4)
        beq x5, t3, equal2
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal2:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_result_loop2


    //************* 3rd block *************//
    // Load block from hw_data and write to AES core
    li x3, AES_ADDR_BLOCK_START
    li x1, AES_ADDR_BLOCK_END
    la x4, hw_data
    addi x4, x4, 80
    write_block_loop3:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        ble x3, x1, write_block_loop3

    // configure to encoder
    li x3, AES_ADDR_CONFIG
    // 128bit key, encode
    li x4, 0x01
    // 256bit key, encode
    // li x4, 0x03
    // 128bit key, decode
    // li x4, 0x00
    // 256bit key, decode
    // li x4, 0x02
    sw x4, 0(x3)

    // Enable AES core
    li x3, AES_ADDR_CNTRL
    li x4, 0x02
    sw x4, 0(x3)

    // wait for AES process
    li x3, AES_ADDR_STATUS
    li x1, AES_VALID
    ready_loop3:
        lw x5, 0(x3)
        bne x5, x1, ready_loop3

    // Read the data back from AES register
    li x3, AES_ADDR_RESULT_START
    li x1, AES_ADDR_RESULT_END
    la x4, hw_data
    addi x4, x4, 144
    read_result_loop3:
        lw x5, 0(x3)
        lw t3, 0(x4)
        beq x5, t3, equal3
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal3:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_result_loop3

    //************* 4th block *************//
    // Load block from hw_data and write to AES core
    li x3, AES_ADDR_BLOCK_START
    li x1, AES_ADDR_BLOCK_END
    la x4, hw_data
    addi x4, x4, 96
    write_block_loop4:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        ble x3, x1, write_block_loop4

    // configure to encoder
    li x3, AES_ADDR_CONFIG
    // 128bit key, encode
    li x4, 0x01
    // 256bit key, encode
    // li x4, 0x03
    // 128bit key, decode
    // li x4, 0x00
    // 256bit key, decode
    // li x4, 0x02
    sw x4, 0(x3)

    // Enable AES core
    li x3, AES_ADDR_CNTRL
    li x4, 0x02
    sw x4, 0(x3)

    // wait for AES process
    li x3, AES_ADDR_STATUS
    li x1, AES_VALID
    ready_loop4:
        lw x5, 0(x3)
        bne x5, x1, ready_loop4

    // Read the data back from AES register
    li x3, AES_ADDR_RESULT_START
    li x1, AES_ADDR_RESULT_END
    la x4, hw_data
    addi x4, x4, 160
    read_result_loop4:
        lw x5, 0(x3)
        lw t3, 0(x4)
        beq x5, t3, equal4
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal4:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_result_loop4

// Write 0xff to STDOUT for TB to termiate test.
_finish:
    li x3, STDOUT
    addi x5, x0, 0xff
    sb x5, 0(x3)
    beq x0, x0, _finish
.rept 99
    nop
.endr
