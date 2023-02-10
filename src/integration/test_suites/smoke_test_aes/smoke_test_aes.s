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
#include "./smoke_test_aes_vectors.s"

// Code to execute
.section .text
.global _start
_start:

    // Clear minstret
    csrw minstret, zero
    csrw minstreth, zero

    // Enable Caches in MRAC
    li x1, 0xaaaaaaaa
    csrw 0x7c0, x1

    // Initialize MTVEC to point to a dummy interrupt handler prior to entering
    // main and subsequent (more complex) initialization procedure
    la t0, early_trap_vector
    csrw mtvec, t0

    // Init. the stack
    la sp, STACK

    // Entry message
    call print_startup

    // Call interrupt init
    call init_interrupts

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
    ready_int_loop:
        lw x5, 0(x3)
        beqz x5, ready_int_loop

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
        la x3, aes_intr_status
        ready_loop1:
            lw x5, 0(x3)
            beqz x5, ready_loop1
        sw x0, 0(x3) // clear status variable

        // Read the data back from AES register
        li x3, AES_ADDR_RESULT_START
        li x1, AES_ADDR_RESULT_END
        la x4, CBCMMT256
        addi x4, x4, 72
        read_result_loop1:
            lw x5, 0(x3)
            lw t5, 0(x4)
            beq x5, t5, equal1
            li x6, STDOUT
            li x7, 0x01
            sb x7, 0(x6)
            equal1:
                addi x3, x3, 4
                addi x4, x4, 4
                ble x3, x1, read_result_loop1

        // Print a message each iteration
        call print_loop

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

print_startup:
    li x3, STDOUT
    la x4, print_data
    j loop

print_loop:
    li x3, STDOUT
    la x4, loop_data
    j loop

loop:
   lb x5, 0(x4)
   sb x5, 0(x3)
   addi x4, x4, 1
   bnez x5, loop
   ret

.section .dccm
.global stdout
stdout: .word STDOUT
.global intr_count
intr_count: .word 0
// FW polls this variable instead of the AES reg....
.global aes_intr_status
aes_intr_status: .word 0
print_data:
.ascii "----------------------------------------\n"
.ascii "Running AES Smoke Test                !!\n"
.ascii "----------------------------------------\n"
.byte 0
loop_data:
.ascii "End of block loop\n"
.byte 0

// From SiFive Interrupt Cookbook:
// https://sifive.cdn.prismic.io/sifive/0d163928-2128-42be-a75a-464df65e04e0_sifive-interrupt-cookbook.pdf
//
/* For sanity's sake we set up an early trap vector that just does nothing. If
* you end up here then there's a bug in the early boot code somewhere. */
.section .text.metal.init.trapvec
.align 2 /* Aligns to 4-bytes (log2(4) = 2) */
.global early_trap_vector
early_trap_vector:
.cfi_startproc
csrr t0, mcause
csrr t1, mepc
csrr t2, mtval
j early_trap_vector
.cfi_endproc
