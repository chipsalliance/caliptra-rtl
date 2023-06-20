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


#include "caliptra_defines.h"

    .set    mfdc, 0x7f9
.extern iccm_code0_start, iccm_code0_end
// Code to execute
.section .text
.global _start
_start:



    // Enable Caches in MRAC
    li x1, 0xaaaaaaaa
    csrw 0x7c0, x1

    // Call interrupt init
    call init_interrupts

    li  x3, 4
    csrw    mfdc, x3     // disable store merging
    li  x3, RV_ICCM_SADR // desired destination (ICCM) for printf subroutine (i.e. VMA)
    la  x4, iccm_code0_start // This is an address in .data_iccm0 (Mailbox) where
                             // printf executable code is loaded (i.e. LMA)
    la  x5, iccm_code0_end


// move the print data from Mailbox to ICCM
load:
    lw  x6, 0 (x4)
    sw  x6, 0 (x3)
    addi    x4,x4,4
    addi    x3,x3,4
    bltu x4, x5, load

    fence.i
    call printf // Execute printf from ICCM (i.e. VMA)

// Write 0xff to STDOUT for TB to termiate test.
_finish:
    li x3, STDOUT
    addi x5, x0, 0xff
    sb x5, 0(x3)
    beq x0, x0, _finish
.rept 100
    nop
.endr

.section .dccm
.global stdout
stdout: .word STDOUT
.global verbosity_g
verbosity_g: .word 2
// FW polls this variable for intr
.global intr_count
intr_count: .word 0
.global cptra_intr_rcv
cptra_intr_rcv: .word 0
hw_data:
.ascii "----------------------------------------\n"
.ascii "Hello World from VeeR EL2 ICCM   !!\n"
.ascii "----------------------------------------\n"
.byte 0

.section .data_iccm0, "ax"
    // Load string from hw_data
    // and write to stdout address

printf:
    li x3, STDOUT
    la x4, hw_data

loop:
   lb x5, 0(x4)
   sb x5, 0(x3)
   addi x4, x4, 1
   bnez x5, loop
   ret
.long   0,1,2,3,4
