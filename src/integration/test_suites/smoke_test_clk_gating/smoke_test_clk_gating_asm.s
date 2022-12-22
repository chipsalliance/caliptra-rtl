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
//#include "../smoke_test_sha512/smoke_test_sha512_vectors.s"


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

    la sp, STACK

    call init_interrupts

    // Enable Caches in MRAC
    li x1, 0xaaaaaaaa
    csrw 0x7c0, x1

    
    
   

//----------------------------------------------------
//Wake up using internal timer0
//----------------------------------------------------
    //Internal timer 0 counter 
    li x1, 0x00000000
    csrw 0x7d2,x1

    //Internal timer 0 upper bound
    li x1, 0x00000020
    csrw 0x7d3,x1

    //Internal timer 0 control (halt_en = 1, enable = 1)
    li x1, 0x00000003
    csrw 0x7d4, x1

    //Machine intr enable reg (mie) - enable internal timer 0 intr
    li x1, 0x20000000
    csrw 0x304, x1

    //mstatus - mie enable
    li x1, 0x00000008
    csrw 0x300, x1

    //FW halt (mpmc) - halt, haltie
    li x1,0x00000003
    csrw 0x7c6,x1

//------------------------------------------------------
//Set STDOUT to F8 until all cases below finish running
//------------------------------------------------------
    li x3, STDOUT
    li x5, 0xf8
    sb x5, 0(x3) //write F8 to STDOUT to cause NMI event
//------------------------------------------------------
//Wake up using software int
//------------------------------------------------------
    //Machine intr enable reg (mie) - enable software int
    li x1, 0x00000008
    csrw 0x304, x1

    //FW halt (mpmc) - halt, haltie
    li x1,0x00000003
    csrw 0x7c6,x1
//------------------------------------------------------
//Wake up using timer int
//------------------------------------------------------
    //Machine intr enable reg (mie) - enable timer int
    li x1, 0x00000080
    csrw 0x304, x1

    //FW halt (mpmc) - halt, haltie
    li x1,0x00000003
    csrw 0x7c6,x1
//------------------------------------------------------
//Wake up using external int - TODO
//------------------------------------------------------
    //Machine intr enable reg (mie) - enable timer int
    //li x1, 0x00000800
    //csrw 0x304, x1


    //FW halt (mpmc) - halt, haltie
    //li x1,0x00000003
    //csrw 0x7c6,x1
//------------------------------------------------------
//Wake up using generic input wires
//------------------------------------------------------
    //FW halt (mpmc) - halt, haltie
    li x1,0x00000003
    csrw 0x7c6,x1
//------------------------------------------------------
//Wake up using APB tx int and exit halt using NMI - TODO
//------------------------------------------------------

    //TODO: how to write a dword in asm
    //Trigger APB tx
    li x3, CLP_SOC_IFC_REG_FLOW_STATUS
    li x4, SOC_IFC_REG_FLOW_STATUS_READY_FOR_FW_MASK
    //sb x5, 0(x3)
    
    loop1:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        bnez x5, loop1

    //FW halt (mpmc) - halt, haltie
    li x1,0x00000003
    csrw 0x7c6,x1


//------------------------------------------------------
//End test
//------------------------------------------------------
    // Load string from hw_data
    // and write to stdout address

    li x3, STDOUT
    la x4, hw_data_out

loop:
   lb x5, 0(x4)
   sb x5, 0(x3)
   addi x4, x4, 1
   bnez x5, loop

// Write 0xff to STDOUT for TB to termiate test.
_finish:
    li x3, STDOUT
    addi x5, x0, 0xff
    sb x5, 0(x3)
    beq x0, x0, _finish
.rept 100
    nop
.endr

.data
hw_data_out:
.ascii "----------------------------------\n"
.ascii "Running clk gating test\n"
.ascii "----------------------------------\n"
.byte 0

//.data
//key_data:
////this is the key 384-bit
//.word 0x0b0b0b0b
//.word 0x0b0b0b0b
//.word 0x0b0b0b0b
//.word 0x0b0b0b0b
//.word 0x0b0b0b0b
//.word 0x0b0b0b0b
//.word 0x0b0b0b0b
//.word 0x0b0b0b0b
//.word 0x0b0b0b0b
//.word 0x0b0b0b0b
//.word 0x0b0b0b0b
//.word 0x0b0b0b0b
//block_data:
//.word 0x48692054
//.word 0x68657265
//.word 0x80000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000000
//.word 0x00000440
//expected_data:
//.word 0xb6a8d563
//.word 0x6f5c6a72
//.word 0x24f9977d
//.word 0xcf7ee6c7
//.word 0xfb6d0c48
//.word 0xcbdee973
//.word 0x7a959796
//.word 0x489bddbc
//.word 0x4c5df61d
//.word 0x5b3297b4
//.word 0xfb68dab9
//.word 0xf1b582c2

.align 4
.global stdout
stdout: .word STDOUT

.global intr_count
intr_count: .word 0
