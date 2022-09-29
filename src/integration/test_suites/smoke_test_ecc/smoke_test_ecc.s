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

    // Set up MTVEC - not expecting to use it though
    li x1, RV_ICCM_SADR
    csrw mtvec, x1  

    // Enable Caches in MRAC
    li x1, 0xaaaaaaaa
    csrw 0x7c0, x1

    // ECC KEYGEN TEST 
    // wait_ready
    li x3, ECC_ADDR_STATUS
    li x1, 0x00
    wait_ready_loop1:
        lw x5, 0(x3)
        beq x5, x1, wait_ready_loop1

    // Load the seed and write to ECC core
    li x3, ECC_ADDR_SEED0
    // 12 words or 384-bit seed
    li x1, 0xc
    li x2, 0x1
    la x4, TEST_VECTOR_KEYGEN
    addi x4, x4, 192
    write_seed0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, x2
        bne x1, x0, write_seed0_loop

    // Load lambda0 and write to ECC core
    li x3, ECC_ADDR_LAMBDA0
    // 12 words or 384-bit lambda0   
    li x1, 0xc
    li x2, 0x1
    la x4, TEST_VECTOR_KEYGEN
    addi x4, x4, 336
    write_lambda0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, x2
        bne x1, x0, write_lambda0_loop

    // Load and write ECC_CMD_KEYGEN to ECC_CORE
    li x3, ECC_ADDR_CTRL
    li x4, ECC_CMD_KEYGEN
    sw x4, 0(x3)

    //wait_ready
    li x3, ECC_ADDR_STATUS
    li x1, 0x00
    wait_ready_loop2:
        lw x5, 0(x3)
        beq x5, x1, wait_ready_loop2

    // Read privkey back from ECC Register
    li x3, ECC_ADDR_PRIVKEY0
    la x4, TEST_VECTOR_KEYGEN
    addi x4, x4, 48
    read_privkey_loop:
        lw x5, 0(x3)
        lw x2, 0(x4)
        beq x5, x2, equal1
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal1:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_privkey_loop

    // Read public key x from ECC register
    li x3, ECC_ADDR_PUBKEYX0
    la x4, TEST_VECTOR_KEYGEN
    addi x4, x4, 96
    read_pubkeyx_loop:
        lw x5, 0(x3)
        lw x2, 0(x4)
        beq x5, x2, equal2
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal2:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_pubkeyx_loop

    // Read public key y from ECC register
    li x3, ECC_ADDR_PUBKEYY0
    la x4, TEST_VECTOR_KEYGEN
    addi x4, x4, 144
    read_pubkeyy_loop:
        lw x5, 0(x3)
        lw x2, 0(x4)
        beq x5, x2, equal3
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal3:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_pubkeyy_loop

    // ECC KEY SIGN TEST
    // wait_ready
    li x3, ECC_ADDR_STATUS
    li x1, 0x00
    wait_ready_loop3:
        lw x5, 0(x3)
        beq x5, x1, wait_ready_loop3

    // Load the message and write to ECC core
    li x3, ECC_ADDR_MSG0
    // 12 words or 384-bit seed
    li x1, 0xc
    li x2, 0x1
    la x4, TEST_VECTOR_KEYSIGN_VERIFY
    write_msg0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, x2
        bne x1, x0, write_msg0_loop

    // Load private key and write to ECC core
    li x3, ECC_ADDR_PRIVKEY0
    // 12 words or 384-bit seed
    li x1, 0xc
    li x2, 0x1
    la x4, TEST_VECTOR_KEYSIGN_VERIFY
    addi x4, x4, 48
    write_privkey0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, x2
        bne x1, x0, write_privkey0_loop

    // Load lambda and write to ECC core
    li x3, ECC_ADDR_LAMBDA0
    // 12 words or 384-bit lambda0   
    li x1, 0xc
    li x2, 0x1
    la x4, TEST_VECTOR_KEYSIGN_VERIFY
    addi x4, x4, 336
    write_lambda0_loop1:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, x2
        bne x1, x0, write_lambda0_loop1

    // Load and write ECC_CMD_KEYSIGN to ECC_CORE
    li x3, ECC_ADDR_CTRL
    li x4, ECC_CMD_KEYSIGN
    sw x4, 0(x3)

    // wait_ready
    li x3, ECC_ADDR_STATUS
    li x1, 0x00
    wait_ready_loop4:
        lw x5, 0(x3)
        beq x5, x1, wait_ready_loop4

    // Read R0 back from ECC Register
    li x3, ECC_ADDR_SIGNR0
    la x4, TEST_VECTOR_KEYSIGN_VERIFY
    addi x4, x4, 240
    read_signr0_loop:
        lw x5, 0(x3)
        lw x2, 0(x4)
        beq x5, x2, equal4
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal4:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_signr0_loop

    // Read S0 back from ECC Register
    li x3, ECC_ADDR_SIGNS0
    la x4, TEST_VECTOR_KEYSIGN_VERIFY
    addi x4, x4, 288
    read_signs0_loop:
        lw x5, 0(x3)
        lw x2, 0(x4)
        beq x5, x2, equal5
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal5:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_signs0_loop

    // ECC KEY VERIFY TEST
    // wait_ready
    li x3, ECC_ADDR_STATUS
    li x1, 0x00
    wait_ready_loop5:
        lw x5, 0(x3)
        beq x5, x1, wait_ready_loop5

    // Load the message and write to ECC core
    li x3, ECC_ADDR_MSG0
    // 12 words or 384-bit seed
    li x1, 0xc
    li x2, 0x1
    la x4, TEST_VECTOR_KEYSIGN_VERIFY
    write_msg0_loop1:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, x2
        bne x1, x0, write_msg0_loop1
    
    //Load public key x and write to ECC core
    li x3, ECC_ADDR_PUBKEYX0
    // 12 words or 384-bit seed
    li x1, 0xc
    li x2, 0x1
    la x4, TEST_VECTOR_KEYSIGN_VERIFY
    addi x4, x4, 96
    write_pubkeyx0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, x2
        bne x1, x0, write_pubkeyx0_loop

    //Load public key y and write to ECC core
    li x3, ECC_ADDR_PUBKEYY0
    // 12 words or 384-bit seed
    li x1, 0xc
    li x2, 0x1
    la x4, TEST_VECTOR_KEYSIGN_VERIFY
    addi x4, x4, 144
    write_pubkeyy0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, x2
        bne x1, x0, write_pubkeyy0_loop

    //Load sign R0 and write to ECC core
    li x3, ECC_ADDR_SIGNR0
    // 12 words or 384-bit seed
    li x1, 0xc
    li x2, 0x1
    la x4, TEST_VECTOR_KEYSIGN_VERIFY
    addi x4, x4, 240
    write_signr0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, x2
        bne x1, x0, write_signr0_loop

    //Load sign S0 and write to ECC core
    li x3, ECC_ADDR_SIGNS0
    // 12 words or 384-bit seed
    li x1, 0xc
    li x2, 0x1
    la x4, TEST_VECTOR_KEYSIGN_VERIFY
    addi x4, x4, 288
    write_signs0_loop:
        lw x5, 0(x4)
        sw x5, 0(x3)
        addi x4, x4, 4
        addi x3, x3, 4
        sub x1, x1, x2
        bne x1, x0, write_signs0_loop

    // Load and write ECC_CMD_KEYVERIFY to ECC_CORE
    li x3, ECC_ADDR_CTRL
    li x4, ECC_CMD_KEYVERIFY
    sw x4, 0(x3)

    // wait_ready
    li x3, ECC_ADDR_STATUS
    li x1, 0x00
    wait_ready_loop6:
        lw x5, 0(x3)
        beq x5, x1, wait_ready_loop6
    
    // Read VERIFYR0 back from ECC Register
    li x3, ECC_ADDR_VERIFYR0
    la x4, TEST_VECTOR_KEYSIGN_VERIFY
    addi x4, x4, 240
    read_verifyr0_loop:
        lw x5, 0(x3)
        lw x2, 0(x4)
        beq x5, x2, equal6
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal6:
            addi x3, x3, 4
            addi x4, x4, 4
            ble x3, x1, read_verifyr0_loop
 
// Write 0xff to STDOUT for TB to termiate test.
_finish:
    li x3, STDOUT
    addi x5, x0, 0xff
    sb x5, 0(x3)
    beq x0, x0, _finish

.rept 99
    nop
.endr
