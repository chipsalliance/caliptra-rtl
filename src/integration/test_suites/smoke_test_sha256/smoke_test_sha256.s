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
#include "./smoke_test_sha256_vectors.s"

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

    li t4, 0
    li t5, 1

    write_msg_loop:
        // loop cnt, indicate whether it's the first block
        addi t4, t4, 1

        // Load block from hw_data and write to SHA256 core
        li x3, CLP_SHA256_REG_SHA256_BLOCK_0
        li x1, CLP_SHA256_REG_SHA256_BLOCK_15
        // set t3 to constantly tracking current ptr
        la t3, SHA256ShortMsg
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

        // Enable SHA256 core
        li x3, CLP_SHA256_REG_SHA256_CTRL
        li x4, SHA256_NEXT
        bne t4, t5, indicate_next
        li x4, SHA256_INIT
        indicate_next:
            sw x4, 0(x3)

        // wait for SHA256 process
        la x3, sha256_intr_status
        li x1, SHA256_VALID
        ready_loop:
            lw x5, 0(x3)
            bne x5, x1, ready_loop
        sw x0, 0(x3) // clear status variable

        // check if reaches the last block of message
        // bne x6, x7, write_msg_loop

    // Read the data back from SHA256 register
    li x3, CLP_SHA256_REG_SHA256_DIGEST_0
    li x1, CLP_SHA256_REG_SHA256_DIGEST_7
    la x4, SHA256ShortMsg
    addi x4, x4, 68
    read_result_loop:
        lw x5, 0(x3)
        lw t2, 0(x4)
        beq x5, t2, equal
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
.global verbosity_g
verbosity_g: .word 2
// FW polls this variable instead of the SHA256 reg....
.global sha256_intr_status
sha256_intr_status: .word 0
print_data:
.ascii "----------------------------------------\n"
.ascii "Running SHA256 Smoke Test             !!\n"
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
