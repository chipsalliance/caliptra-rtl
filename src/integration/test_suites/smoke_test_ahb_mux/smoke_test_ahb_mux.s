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


#include "../includes/caliptra_defines.h"

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

    // Read from ROM
    la x4, rom
    la x3, rom
    la x2, rom
    la x1, rom

.rept 50
    nop
.endr

    lw x8, 0(x1)
    lw x9, 32(x2)
    nop
    nop
    nop

    lw x8, 0(x1)
    lw x9, 32(x2)
    nop
    nop
    nop

    lw x8, 0(x1)
    lw x9, 32(x2)
    nop
    nop
    nop

    lw x8, 0(x1)
    lw x9, 32(x2)
    nop
    nop
    nop

    lw x8, 0(x1)
    lw x9, 32(x2)
    nop
    nop
    nop

    lw x8, 0(x1)
    lw x9, 32(x2)
    nop
    nop
    nop

    lw x8, 0(x1)
    lw x9, 32(x2)
    nop
    nop
    nop

    lw x8, 0(x1)
    lw x9, 32(x2)
    nop
    nop
    nop

// Write 0xff to STDOUT for TB to terminate test.
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

.align 4
rom:
.word 0x11111111
.word 0x22222222
.word 0x33333333
.word 0x44444444
.word 0x55555555
.word 0x66666666
.word 0x77777777
.word 0x88888888
.word 0x99999999
.word 0xaaaaaaaa
.word 0xbbbbbbbb
.word 0xcccccccc
.word 0xdddddddd
.word 0xeeeeeeee
.word 0xffffffff
.word 0x11111111
.word 0x22222222
.word 0x33333333
.word 0x44444444
.word 0x55555555
.word 0x66666666
.word 0x77777777
.word 0x88888888
.word 0x99999999
.word 0xaaaaaaaa
.word 0xbbbbbbbb
.word 0xcccccccc
.word 0xdddddddd
.word 0xeeeeeeee
.word 0xffffffff
.word 0x11111111
.word 0x22222222
.word 0x33333333
.word 0x44444444
.word 0x55555555
.word 0x66666666
.word 0x77777777
.word 0x88888888
.word 0x99999999
.word 0xaaaaaaaa
.word 0xbbbbbbbb
.word 0xcccccccc
.word 0xdddddddd
.word 0xeeeeeeee
.word 0xffffffff
.word 0x11111111
.word 0x22222222
.word 0x33333333
.word 0x44444444
.word 0x55555555
.word 0x66666666
.word 0x77777777
.word 0x88888888
.word 0x99999999
.word 0xaaaaaaaa
.word 0xbbbbbbbb
.word 0xcccccccc
.word 0xdddddddd
.word 0xeeeeeeee
.word 0xffffffff

my_print:
.ascii "-"

.section .dccm
.global stdout
stdout: .word STDOUT
// FW polls this variable for intr
.global intr_count
intr_count: .word 0
.global cptra_intr_rcv
cptra_intr_rcv: .word 0
.global verbosity_g
verbosity_g: .word 2
print_data:
.ascii "----------------------------------------\n"
.ascii "Running AHB MUX Smoke Test    !!\n"
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
