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
#include "./smoke_test_ecc_vectors.s"

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

    // ECC KEYGEN TEST 
    // wait_ready before initialization
    li x3, CLP_ECC_REG_ECC_STATUS
    li x1, 0x00
    wait_ready_loop1:
        lw x5, 0(x3)
        beq x5, x1, wait_ready_loop1

    // Load the seed and write to ECC core
    li x3, CLP_ECC_REG_ECC_SEED_0
    // 12 words or 384-bit seed
    li x1, 0xc
    li t3, 0x1
    la x4, TEST_VECTOR
    addi x4, x4, 192
    write_seed0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, t3
        bne x1, x0, write_seed0_loop

    // Load the nonce and write to ECC core
    li x3, CLP_ECC_REG_ECC_NONCE_0
    // 12 words or 384-bit nonce
    li x1, 0xc
    li t3, 0x1
    la x4, TEST_VECTOR
    addi x4, x4, 240
    write_nonce0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, t3
        bne x1, x0, write_nonce0_loop

    // Load IV0 and write to ECC core
    li x3, CLP_ECC_REG_ECC_IV_0 
    // 12 words or 384-bit IV0   
    li x1, 0xc
    li t3, 0x1
    la x4, TEST_VECTOR
    addi x4, x4, 384
    write_IV0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, t3
        bne x1, x0, write_IV0_loop

    // Load and write ECC_CMD_KEYGEN to ECC_CORE
    li x3, CLP_ECC_REG_ECC_CTRL
    li x4, ECC_CMD_KEYGEN
    sw x4, 0(x3)

    // wait for ECC process
    la x3, ecc_intr_status
    li x1, 0x00
    wait_ready_loop2:
        lw x5, 0(x3)
        beq x5, x1, wait_ready_loop2
    sw x0, 0(x3) // clear status variable

    // Read privkey back from ECC Register
    li x3, CLP_ECC_REG_ECC_PRIVKEY_0 
    la x4, TEST_VECTOR
    addi x4, x4, 48
    read_privkey_loop:
        lw x5, 0(x3)
        lw t3, 0(x4)
        beq x5, t3, equal1
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal1:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_privkey_loop

    // Read public key x from ECC register
    li x3, CLP_ECC_REG_ECC_PUBKEY_X_0
    la x4, TEST_VECTOR
    addi x4, x4, 96
    read_pubkeyx_loop:
        lw x5, 0(x3)
        lw t3, 0(x4)
        beq x5, t3, equal2
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal2:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_pubkeyx_loop

    // Read public key y from ECC register
    li x3, CLP_ECC_REG_ECC_PUBKEY_Y_0
    la x4, TEST_VECTOR
    addi x4, x4, 144
    read_pubkeyy_loop:
        lw x5, 0(x3)
        lw t3, 0(x4)
        beq x5, t3, equal3
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal3:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_pubkeyy_loop

    // ECC SIGNING TEST
    // wait_ready
    li x3, CLP_ECC_REG_ECC_STATUS
    li x1, 0x00
    wait_ready_loop3:
        lw x5, 0(x3)
        beq x5, x1, wait_ready_loop3

    // Load the message and write to ECC core
    li x3, CLP_ECC_REG_ECC_MSG_0 
    // 12 words or 384-bit seed
    li x1, 0xc
    li t3, 0x1
    la x4, TEST_VECTOR
    write_msg0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, t3
        bne x1, x0, write_msg0_loop

    // Load private key and write to ECC core
    li x3, CLP_ECC_REG_ECC_PRIVKEY_0 
    // 12 words or 384-bit seed
    li x1, 0xc
    li t3, 0x1
    la x4, TEST_VECTOR
    addi x4, x4, 48
    write_privkey0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, t3
        bne x1, x0, write_privkey0_loop

    // Load IV and write to ECC core
    li x3, CLP_ECC_REG_ECC_IV_0 
    // 12 words or 384-bit IV0   
    li x1, 0xc
    li t3, 0x1
    la x4, TEST_VECTOR
    addi x4, x4, 384
    write_IV0_loop1:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, t3
        bne x1, x0, write_IV0_loop1

    // Load and write ECC_CMD_SIGNING to ECC_CORE
    li x3, CLP_ECC_REG_ECC_CTRL
    li x4, ECC_CMD_SIGNING
    sw x4, 0(x3)

    // wait for ECC process
    la x3, ecc_intr_status
    li x1, 0x00
    wait_ready_loop4:
        lw x5, 0(x3)
        beq x5, x1, wait_ready_loop4
    sw x0, 0(x3) // clear status variable

    // Read R0 back from ECC Register
    li x3, CLP_ECC_REG_ECC_SIGN_R_0 
    la x4, TEST_VECTOR
    addi x4, x4, 288
    read_signr0_loop:
        lw x5, 0(x3)
        lw t3, 0(x4)
        beq x5, t3, equal4
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal4:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_signr0_loop

    // Read S0 back from ECC Register
    li x3, CLP_ECC_REG_ECC_SIGN_S_0 
    la x4, TEST_VECTOR
    addi x4, x4, 336
    read_signs0_loop:
        lw x5, 0(x3)
        lw t3, 0(x4)
        beq x5, t3, equal5
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal5:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_signs0_loop

    // ECC KEY VERIFY TEST
    // wait_ready
    li x3, CLP_ECC_REG_ECC_STATUS
    li x1, 0x00
    wait_ready_loop5:
        lw x5, 0(x3)
        beq x5, x1, wait_ready_loop5

    // Load the message and write to ECC core
    li x3, CLP_ECC_REG_ECC_MSG_0 
    // 12 words or 384-bit seed
    li x1, 0xc
    li t3, 0x1
    la x4, TEST_VECTOR
    write_msg0_loop1:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, t3
        bne x1, x0, write_msg0_loop1

    //Load public key x and write to ECC core
    li x3, CLP_ECC_REG_ECC_PUBKEY_X_0 
    // 12 words or 384-bit seed
    li x1, 0xc
    li t3, 0x1
    la x4, TEST_VECTOR
    addi x4, x4, 96
    write_pubkeyx0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, t3
        bne x1, x0, write_pubkeyx0_loop

    //Load public key y and write to ECC core
    li x3, CLP_ECC_REG_ECC_PUBKEY_Y_0 
    // 12 words or 384-bit seed
    li x1, 0xc
    li t3, 0x1
    la x4, TEST_VECTOR
    addi x4, x4, 144
    write_pubkeyy0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, t3
        bne x1, x0, write_pubkeyy0_loop

    //Load sign R0 and write to ECC core
    li x3, CLP_ECC_REG_ECC_SIGN_R_0 
    // 12 words or 384-bit seed
    li x1, 0xc
    li t3, 0x1
    la x4, TEST_VECTOR
    addi x4, x4, 288
    write_signr0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, t3
        bne x1, x0, write_signr0_loop

    //Load sign S0 and write to ECC core
    li x3, CLP_ECC_REG_ECC_SIGN_S_0 
    // 12 words or 384-bit seed
    li x1, 0xc
    li t3, 0x1
    la x4, TEST_VECTOR
    addi x4, x4, 336
    write_signs0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, t3
        bne x1, x0, write_signs0_loop

    // Load and write ECC_CMD_VERIFYING to ECC_CORE
    li x3, CLP_ECC_REG_ECC_CTRL
    li x4, ECC_CMD_VERIFYING
    sw x4, 0(x3)

    // wait for ECC process
    la x3, ecc_intr_status
    li x1, 0x00
    wait_ready_loop6:
        lw x5, 0(x3)
        beq x5, x1, wait_ready_loop6
    sw x0, 0(x3) // clear status variable

    // Read VERIFYR0 back from ECC Register
    li x3, CLP_ECC_REG_ECC_VERIFY_R_0 
    la x4, TEST_VECTOR
    addi x4, x4, 288
    read_verifyr0_loop:
        lw x5, 0(x3)
        lw t3, 0(x4)
        beq x5, t3, equal6
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal6:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_verifyr0_loop
 
// Write 0xff to STDOUT for TB to terminate test.
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

loop:
   lb x5, 0(x4)
   sb x5, 0(x3)
   addi x4, x4, 1
   bnez x5, loop
   ret

.section .dccm
.align 4
.global stdout
stdout: .word STDOUT
.global intr_count
intr_count: .word 0
.global verbosity_g
verbosity_g: .word 2
// FW polls this variable instead of the ECC reg....
.global ecc_intr_status
ecc_intr_status: .word 0
print_data:
.ascii "----------------------------------------\n"
.ascii "Running ECC Smoke Test                !!\n"
.ascii "----------------------------------------\n"
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
