# SPDX-License-Identifier: Apache-2.0
# Copyright 2020 Western Digital Corporation or its affiliates.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
// startup code to support HLL programs

#include "caliptra_defines.h"

.set    mfdc, 0x7f9
.set    mrac, 0x7c0
.extern _data_lma_start, _data_lma_end
.extern _bss_lma_start, _bss_lma_end
.extern _data_vma_start, _bss_vma_start
.section .text.init
.global _start
_start:

    // Clear minstret
    csrw minstret, zero
    csrw minstreth, zero

    // MRAC
    // Disable Caches on all regions except...
    //  - Set cacheable for ROM to improve perf
    // Set side-effects (SE) at peripheral address regions:
    //  - imem       @ 0x0000_0000: no SE
    //  - crypto     @ 0x1000_0000:    SE
    //  - [UNMAPPED] @ 0x2000_0000:    SE
    //  - soc_ifc    @ 0x3000_0000:    SE
    //  - ICCM       @ 0x4000_0000: no SE
    //  - DCCM       @ 0x5000_0000: no SE
    //  - PIC        @ 0x6000_0000:    SE
    //  - [UNMAPPED] @ 0x7000_0000:    SE
    //  - ...
    //  - [UNMAPPED] @ 0xF000_0000:    SE
    li t0, 0xAAAAA0A9
    csrw mrac, t0

    li  t0, 4
    fence.i
    csrw    mfdc, t0     // disable store merging
    fence.i

    // Initialize MTVEC to point to a dummy interrupt handler prior to entering
    // main and subsequent (more complex) initialization procedure
    la t0, early_trap_vector
    csrw mtvec, t0

    // Copy .data from ROM (imem) to DCCM
    la t0, _data_lma_start
    la t1, _data_lma_end
    la t2, _data_vma_start
data_cp_loop:
    lw t3, 0(t0)
    sw t3, 0(t2)
    addi t0, t0, 4
    addi t2, t2, 4
    bltu t0, t1, data_cp_loop

    // Copy .bss from ROM (imem) to DCCM
    la t0, _bss_lma_start
    la t1, _bss_lma_end
    la t2, _bss_vma_start
bss_cp_loop:
    lw t3, 0(t0)
    sw t3, 0(t2)
    addi t0, t0, 4
    addi t2, t2, 4
    bltu t0, t1, bss_cp_loop

    // Init. the stack and transfer operation to main
    la sp, STACK

    call main


.global _finish
// Write 0xff to STDOUT for TB to terminate test.
_finish:
    li t0, STDOUT
    addi t5, zero, 0xff
    sb t5, 0(t0)
    beq zero, zero, _finish
.rept 100
    nop
.endr

/* ----------------------- Data -------------------- */
.data
trap_msg:
.ascii "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n"
.ascii "   TRAP VECTOR EXECUTING! KILL SIM!!!   \n"
.ascii "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n"
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
li t3, STDOUT
la t4, trap_msg
trap_print_loop:
   lb t0, 0(t4)
   sb t0, 0(t3)
   addi t4, t4, 1
   bnez t0, trap_print_loop
addi t5, zero, 0x1
sb t5, 0(t3)
j early_trap_vector
.cfi_endproc
