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

// Assembly code for ICCM Lock Test
// Not using only ALU ops for creating the string


#include "caliptra_defines.h"

    .set    mfdc, 0x7f9
.extern printf_start, printf_end
// Code to execute
.section .text
.global _start
_start:



    // Enable Caches in MRAC
    li x1, 0xaaaaaaaa
    csrw 0x7c0, x1

    // Initialize MTVEC to point to a dummy interrupt handler prior to entering
    // main and subsequent (more complex) initialization procedure
    // This vector will just print a short message and kill the sim
    la t0, early_trap_vector
    csrw mtvec, t0

    li  x3, 4
    csrw    mfdc, x3     // disable store merging
    li  x3, RV_ICCM_SADR // desired destination (ICCM) for printf subroutine (i.e. VMA)
    la  x4, printf_start // This is an address in .data_iccm (Mailbox) where printf
                         // executable code is loaded (i.e. LMA)
    la  x5, printf_end


// move the print data from Mailbox to ICCM
load:
    lw  x6, 0 (x4)
    sw  x6, 0 (x3)
    addi    x4,x4,4
    addi    x3,x3,4
    bltu x4, x5, load

    fence.i
    call printf // Execute printf from ICCM (i.e. VMA)

// Set ICCM Lock
    li t0, CLP_SOC_IFC_REG_ICCM_LOCK
    li t1, SOC_IFC_REG_ICCM_LOCK_LOCK_MASK
    sw t1, 0(t0)

// Write data to ICCM
    li t0, RV_ICCM_SADR
    li t1, 0xdeadbeef
    sw t1, 0(t0)

// Read back
    lw t2, 0(t0)

// Confirm data does not match
// If data differs, ICCM write was blocked (as expected) and testcase passes
    bne t1, t2, _finish

// End sim with fail
_fail:
    li x3, STDOUT
    addi x5, x0, 0x1
    sb x5, 0(x3)
    beq x0, x0, _fail



// Write 0xff to STDOUT for TB to terminate test with Success status
_finish:
    li x3, STDOUT
    addi x5, x0, 0xff
    sb x5, 0(x3)
    beq x0, x0, _finish
.rept 100
    nop
.endr

/* ----------------------- Data -------------------- */
.data
hw_data:
.ascii "----------------------------------------\n"
.ascii "Hello World from SweRV EL2 ICCM  @WDC !!\n"
.ascii "----------------------------------------\n"
.byte 0
success_msg:
.ascii "----------------------------------------\n"
.ascii " ICCM Lock Test Passed!                 \n"
.ascii "----------------------------------------\n"
.byte 0xFF // Triggers test to end with success
.byte 0
trap_msg:
.ascii "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n"
.ascii "   TRAP VECTOR EXECUTING! KILL SIM!!!   \n"
.ascii "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n"
.byte 0

/* ----------------------- ICCM -------------------- */
.section .data_iccm, "ax"
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


/* ----------------------- Exception Vectors -------------------- */
// This trap vector executes if the core hits an exception
.section .text.metal.init.trapvec
.align 2 /* Aligns to 4-bytes (log2(4) = 2) */
.global early_trap_vector
early_trap_vector:
.cfi_startproc
csrr t0, mcause
csrr t1, mepc
csrr t2, mtval
li x3, STDOUT
la x4, trap_msg
trap_print_loop:
   lb t0, 0(x4)
   sb t0, 0(x3)
   addi x4, x4, 1
   bnez t0, trap_print_loop
j _finish
.cfi_endproc
