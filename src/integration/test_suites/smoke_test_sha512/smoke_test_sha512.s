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
#include "./smoke_test_sha512_vectors.s"

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

    li t4, 0
    li t5, 1

    write_msg_loop:
        // loop cnt, indicate whether it's the first block
        addi t4, t4, 1

        // Load block from hw_data and write to SHA512 core
        li x3, SHA512_ADDR_BLOCK_START
        li x1, SHA512_ADDR_BLOCK_END
        // set t3 to constantly tracking current ptr
        la t3, SHA512ShortMsg
        // set x7 as last word check
        lw x7, 0(t3)
        addi t3, t3, 4
        write_block_loop:
            lw x5, 0(t3) 
            
            sw x5, 0(x3)
            addi t3, t3, 4
            addi x3, x3, 4
            ble x3, x1, write_block_loop

        // store the last word for further checking
        mv x6, x5

        // Enable SHA512 core
        li x3, SHA512_ADDR_CNTRL
        li x4, SHA512_NEXT
        bne t4, t5, indicate_next
        li x4, SHA512_INIT
        indicate_next:
            sw x4, 0(x3)

        // wait for SHA512 process
        li x3, SHA512_ADDR_STATUS
        li x1, SHA512_VALID
        ready_loop:
            lw x5, 0(x3)
            bne x5, x1, ready_loop

        // check if reaches the last block of message
        bne x6, x7, write_msg_loop

    // Read the data back from SHA512 register
    li x3, SHA512_ADDR_DIGEST_START
    li x1, SHA512_ADDR_DIGEST_END
    la x4, SHA512ShortMsg
    addi x4, x4, 132
    read_result_loop:
        lw x5, 0(x3)
        lw x2, 0(x4)
        beq x5, x2, equal
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
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
.rept 100
    nop
.endr
