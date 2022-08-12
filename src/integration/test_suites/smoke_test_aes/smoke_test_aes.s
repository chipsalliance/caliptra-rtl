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
        lw x2, 0(x4)
        beq x5, x2, equal1
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
        lw x2, 0(x4)
        beq x5, x2, equal2
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
        lw x2, 0(x4)
        beq x5, x2, equal3
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
        lw x2, 0(x4)
        beq x5, x2, equal4
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

.data
hw_data:
// start of 128bit key
.word 0x56e47a38  
.word 0xc5598974
.word 0xbc46903d
.word 0xba290349
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
// start of IV input
.word 0x8ce82eef   
.word 0xbea0da3c
.word 0x44699ed7
.word 0xdb51b7d9 
// start of 1st text
.word 0xa0a1a2a3   
.word 0xa4a5a6a7
.word 0xa8a9aaab
.word 0xacadaeaf
// start of 2nd text
.word 0xb0b1b2b3  
.word 0xb4b5b6b7
.word 0xb8b9babb
.word 0xbcbdbebf 
// start of 3rd text
.word 0xc0c1c2c3
.word 0xc4c5c6c7  
.word 0xc8c9cacb
.word 0xcccdcecf 
// start of 4th text
.word 0xd0d1d2d3
.word 0xd4d5d6d7 
.word 0xd8d9dadb
.word 0xdcdddedf 
// start of 1st expected
.word 0xc30e32ff
.word 0xedc0774e
.word 0x6aff6af0
.word 0x869f71aa
// start of 2nd expected
.word 0x0f3af07a
.word 0x9a31a9c6
.word 0x84db207e
.word 0xb0ef8e4e
// start of 3rd expected
.word 0x35907aa6
.word 0x32c3ffdf
.word 0x868bb7b2
.word 0x9d3d46ad
// start of 4th expected
.word 0x83ce9f9a
.word 0x102ee99d
.word 0x49a53e87
.word 0xf4c3da55
.ascii "----------------------------------\n"
.ascii "AES CBC mode Quadratic Blocks Test !!\n"
.ascii "----------------------------------\n"
.byte 0
string1: 
.ascii "1st block successful"
string2: 
.ascii "2nd block successful"
string3: 
.ascii "3rd block successful"
string4: 
.ascii "4th block successful"
