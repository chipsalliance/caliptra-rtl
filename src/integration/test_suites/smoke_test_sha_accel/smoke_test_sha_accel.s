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
#include "./smoke_test_sha_accel_vectors.s"

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

    
   //For FIPS, SHA starts of in a locked mode for uController
   //Release SHA lock - although this step is NOT explicitly required if uC wants to just go ahead and use it directly
   // Note that this case was also tested by commenting out the unlocking & relocking code below as a directed test case during the design
   li x3, CLP_SHA512_ACC_CSR_LOCK
   li x1, SHA512_ACC_CSR_LOCK_LOCK_MASK
   sw x1, 0(x3)

   //Acquire SHA lock
   li x3, CLP_SHA512_ACC_CSR_LOCK
   lock_poll_loop0:
       lw x5, 0(x3)
       andi x5, x5, SHA512_ACC_CSR_LOCK_LOCK_MASK
       bne x5, x0, lock_poll_loop0

    //Set to Streaming SHA512 Mode
    li x3, CLP_SHA512_ACC_CSR_MODE
    li x1, 0x00000001
    sw x1, 0(x3)

    // Load block from hw_data and write to SHA Accelerator
    li x3, CLP_SHA512_ACC_CSR_DATAIN
    li x4, CLP_SHA512_ACC_CSR_DLEN
    // set t3 to constantly tracking current ptr
    la t3, SHA512ShortMsg
    // x7 has the length in bits
    lw x7, 0(t3)
    // write the length in bytes to DLEN
    srli x7, x7, 3
    sw x7, 0(x4)
    li t4, 0
    addi t3, t3, 4
    write_block_loop0:
        lw x5, 0(t3) 
        sw x5, 0(x3)
        //increment address of data by a dword
        addi t3, t3, 4
        //increment data length counter by 4 bytes
        addi t4, t4, 4
        // check if reaches the last block of message
        blt t4, x7, write_block_loop0

    // set execute for stream Mode
    li x3, CLP_SHA512_ACC_CSR_EXECUTE
    li x1, SHA512_ACC_CSR_EXECUTE_EXECUTE_MASK
    sw x1, 0(x3)

    // wait for SHA512 process
    la x3, sha_intr_status
    li x1, SHA512_ACC_CSR_STATUS_VALID_MASK
    ready_loop0:
        lw x5, 0(x3)
        bne x5, x1, ready_loop0
    sw x0, 0(x3) // clear status variable

    // Read the data back from SHA Accelerator Digest register
    li x3, CLP_SHA512_ACC_CSR_DIGEST_0
    li x1, CLP_SHA512_ACC_CSR_DIGEST_15
    read_result_loop0:
        lw x5, 0(x3)
        lw x7, 0(t3)
        beq x5, x7, equal0
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal0:
            addi x3, x3, 4
            addi t3, t3, 4
            blt x3, x1, read_result_loop0
    
    //Release SHA lock
    li x3, CLP_SHA512_ACC_CSR_LOCK
    li x1, SHA512_ACC_CSR_LOCK_LOCK_MASK
    sw x1, 0(x3)

    //Acquire SHA lock
    li x3, CLP_SHA512_ACC_CSR_LOCK
    lock_poll_loop1:
        lw x5, 0(x3)
        andi x5, x5, SHA512_ACC_CSR_LOCK_LOCK_MASK
        bne x5, x0, lock_poll_loop1

    //Set to Streaming SHA512 Mode
    li x3, CLP_SHA512_ACC_CSR_MODE
    li x1, 0x00000001
    sw x1, 0(x3)

    // Load block from hw_data and write to SHA Accelerator
    li x3, CLP_SHA512_ACC_CSR_DATAIN
    li x4, CLP_SHA512_ACC_CSR_DLEN
    // set t3 to constantly tracking current ptr
    la t3, SHA512LongMsg
    // x7 has the length in bits
    lw x7, 0(t3)
    // write the length in bytes to DLEN
    srli x7, x7, 3
    sw x7, 0(x4)
    li t4, 0
    addi t3, t3, 4
    write_block_loop1:
        lw x5, 0(t3) 
        sw x5, 0(x3)
        //increment address of data by a dword
        addi t3, t3, 4
        //increment data length counter by 4 bytes
        addi t4, t4, 4
        // check if reaches the last block of message
        blt t4, x7, write_block_loop1

    // set execute for stream Mode
    li x3, CLP_SHA512_ACC_CSR_EXECUTE
    li x1, SHA512_ACC_CSR_EXECUTE_EXECUTE_MASK
    sw x1, 0(x3)

    // wait for SHA512 process
    la x3, sha_intr_status
    li x1, SHA512_ACC_CSR_STATUS_VALID_MASK
    ready_loop1:
        lw x5, 0(x3)
        bne x5, x1, ready_loop1
    sw x0, 0(x3) // clear status variable

    // Read the data back from SHA Accelerator Digest register
    li x3, CLP_SHA512_ACC_CSR_DIGEST_0
    li x1, CLP_SHA512_ACC_CSR_DIGEST_15
    read_result_loop1:
        lw x5, 0(x3)
        lw x7, 0(t3)
        beq x5, x7, equal1
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal1:
            addi x3, x3, 4
            addi t3, t3, 4
            blt x3, x1, read_result_loop1
    
    //Release SHA lock
    li x3, CLP_SHA512_ACC_CSR_LOCK
    li x1, SHA512_ACC_CSR_LOCK_LOCK_MASK
    sw x1, 0(x3)

    //Acquire SHA lock
    li x3, CLP_SHA512_ACC_CSR_LOCK
    lock_poll_loop2:
        lw x5, 0(x3)
        andi x5, x5, SHA512_ACC_CSR_LOCK_LOCK_MASK
        bne x5, x0, lock_poll_loop2

    //Set to Mailbox SHA512 Mode
    li x3, CLP_SHA512_ACC_CSR_MODE
    li x1, 0x00000007
    sw x1, 0(x3)


    // Submit task to SHA Accelerator, providing
    // mailbox start address where vector is located
    li x3, CLP_SHA512_ACC_CSR_START_ADDRESS
    li x4, CLP_SHA512_ACC_CSR_DLEN
    // set t3 to constantly tracking current ptr
    la t3, SHA512LongMsg
    // x7 has the length in bits
    lw x7, 0(t3)
    // write the length in bytes to DLEN
    srli x7, x7, 3
    sw x7, 0(x4)
    //round dlen up to nearest dword
    addi x7, x7, 3
    andi x7, x7, 0xFFFFFFFC
    // Increment pointer to start of test vector
    addi t3, t3, 4
    // Acquire lock before direct access to mailbox
    li x3, CLP_MBOX_CSR_MBOX_LOCK
    li x1, MBOX_CSR_MBOX_LOCK_LOCK_MASK
    acquire_lock_loop0:
        lw x5, 0(x3)
        and x5, x5, x1
        beq x5, x1, acquire_lock_loop0
    // Load test vector from hw_data and write to Mailbox
    li x8, MBOX_DIR_BASE_ADDR
    add x8, x8, x7 /* ending destination address of test vector */
    li x6, MBOX_DIR_BASE_ADDR /* destination address to write in mailbox */
    cp_to_mbox_loop0:
        lw x5, 0(t3)
        sw x5, 0(x6)
        addi t3, t3, 4
        addi x6, x6, 4
        bltu x6, x8, cp_to_mbox_loop0
    //store the start address of the test vector
    //first shift it into a dword address
    li x6, MBOX_DIR_BASE_ADDR
    srli x6, x6, 2
    sw x6, 0(x3)

    // set execute for stream Mode
    li x3, CLP_SHA512_ACC_CSR_EXECUTE
    li x1, SHA512_ACC_CSR_EXECUTE_EXECUTE_MASK
    sw x1, 0(x3)

    // wait for SHA512 process
    la x3, sha_intr_status
    li x1, SHA512_ACC_CSR_STATUS_VALID_MASK
    ready_loop2:
        lw x5, 0(x3)
        bne x5, x1, ready_loop2
    sw x0, 0(x3) // clear status variable

//    //add this gets us to the result
//    add t3, t3, x7

    // Read the data back from SHA Accelerator Digest register
    li x3, CLP_SHA512_ACC_CSR_DIGEST_0
    li x1, CLP_SHA512_ACC_CSR_DIGEST_15
    read_result_loop2:
        lw x5, 0(x3)
        lw x7, 0(t3)
        beq x5, x7, equal2
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal2:
            addi x3, x3, 4
            addi t3, t3, 4
            blt x3, x1, read_result_loop2
    
    //Release SHA lock
    li x3, CLP_SHA512_ACC_CSR_LOCK
    li x1, SHA512_ACC_CSR_LOCK_LOCK_MASK
    sw x1, 0(x3)

    //Release MBOX lock
    li x3, CLP_MBOX_CSR_MBOX_UNLOCK
    li x1, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK
    sw x1, 0(x3)
    
    //Acquire SHA lock
    li x3, CLP_SHA512_ACC_CSR_LOCK
    lock_poll_loop3:
        lw x5, 0(x3)
        andi x5, x5, SHA512_ACC_CSR_LOCK_LOCK_MASK
        bne x5, x0, lock_poll_loop3

    //Set to Mailbox SHA384 Mode
    li x3, CLP_SHA512_ACC_CSR_MODE
    li x1, 0x00000006
    sw x1, 0(x3)

    // Load block from hw_data and write to Mailbox
    li x3, CLP_SHA512_ACC_CSR_START_ADDRESS
    li x4, CLP_SHA512_ACC_CSR_DLEN
    // set t3 to constantly tracking current ptr
    la t3, SHA384LongMsg
    // x7 has the length in bits
    lw x7, 0(t3)
    // write the length in bytes to DLEN
    srli x7, x7, 3
    sw x7, 0(x4)
    //round dlen up to nearest dword
    addi x7, x7, 3
    andi x7, x7, 0xFFFFFFFC
    addi t3, t3, 4
    // Acquire lock before direct access to mailbox
    li x3, CLP_MBOX_CSR_MBOX_LOCK
    li x1, MBOX_CSR_MBOX_LOCK_LOCK_MASK
    acquire_lock_loop1:
        lw x5, 0(x3)
        and x5, x5, x1
        beq x5, x1, acquire_lock_loop1
    // Load test vector from hw_data and write to Mailbox
    li x8, MBOX_DIR_BASE_ADDR
    add x8, x8, x7 /* ending destination address of test vector */
    li x6, MBOX_DIR_BASE_ADDR /* destination address to write in mailbox */
    cp_to_mbox_loop1:
        lw x5, 0(t3)
        sw x5, 0(x6)
        addi t3, t3, 4
        addi x6, x6, 4
        bltu x6, x8, cp_to_mbox_loop1
    //store the start address of the test vector
    //first shift it into a dword address
    li x6, MBOX_DIR_BASE_ADDR
    srli x6, x6, 2
    sw x6, 0(x3)

    // set execute for stream Mode
    li x3, CLP_SHA512_ACC_CSR_EXECUTE
    li x1, SHA512_ACC_CSR_EXECUTE_EXECUTE_MASK
    sw x1, 0(x3)

    // wait for SHA384 process
    la x3, sha_intr_status
    li x1, SHA512_ACC_CSR_STATUS_VALID_MASK
    ready_loop3:
        lw x5, 0(x3)
        bne x5, x1, ready_loop3
    sw x0, 0(x3) // clear status variable

//    //add this to start gets us to the result
//    add t3, t3, x7

    // Read the data back from SHA Accelerator Digest register
    li x3, CLP_SHA512_ACC_CSR_DIGEST_0
    li x1, CLP_SHA512_ACC_CSR_DIGEST_11
    read_result_loop3:
        lw x5, 0(x3)
        lw x7, 0(t3)
        beq x5, x7, equal3
        li x6, STDOUT
        li x7, 0x01
        sb x7, 0(x6)
        equal3:
            addi x3, x3, 4
            addi t3, t3, 4
            blt x3, x1, read_result_loop3

    //Release SHA lock
    li x3, CLP_SHA512_ACC_CSR_LOCK
    li x1, SHA512_ACC_CSR_LOCK_LOCK_MASK
    sw x1, 0(x3)

    //Release MBOX lock
    li x3, CLP_MBOX_CSR_MBOX_UNLOCK
    li x1, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK
    sw x1, 0(x3)

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

.section .dccm
.global stdout
stdout: .word STDOUT
.global intr_count
intr_count: .word 0
.global verbosity_g
verbosity_g: .word 2
// FW polls this variable instead of the SHA reg....
.global sha_intr_status
sha_intr_status: .word 0
.global cptra_intr_rcv
cptra_intr_rcv: .word 0
print_data:
.ascii "----------------------------------------\n"
.ascii "Running SHA Accelerator Smoke Test    !!\n"
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
