// SPDX-License-Identifier: Apache-2.0
//
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

#include "caliptra_defines.h"

.set    mfdc, 0x7f9
.set    mfdht, 0x7ce
.set    mstatus, 0x300
.set    mitcnt0, 0x7d2
.set    mitb0, 0x7d3
.set    mitctl0, 0x7d4
.set    mie, 0x304
.set    mpmc, 0x7c6

// Code to execute
.section .text
.global _start
_start:

    // Enable Caches in MRAC
    li      x1, 0xaaaaaaaa
    csrw    0x7c0, x1

    li      x3, 4
    csrw    mfdc, x3        // disable store merging

    // Set some register values
    li      x1,  0x12345678
    li      x2,  0xABCDEF00
    li      x3,  0xCAFEBABA
    li      x4,  0xDEADBEEF
    li      x5,  0x05050505
    li      x6,  0xA0A0A0A0
    li      x7,  0x00FF00FF
    li      x8,  0xCC00CC00
    li      s1,  0xFEEDABED // Writing 0 to this register initiates CPU halt

    // Simple infinite loop program with inner and outer loop
    li      t3,  0
outer:
    addi    t3, t3, 1
    li      t4, 123
inner:
    beq     s1, zero, halt_cpu
    addi    t4, t4, -1
    bne     t4, zero, inner
    j       outer

halt_cpu:
    // Set mit0 and halt core
    li      t5, 0xf0
    li      t6, 0x20000800
    csrwi   mitcnt0, 0x00   // Internal timer 0 counter
    csrw    mitb0, t5       // Internal timer 0 boundary
    csrwi   mitctl0, 0x01   // Internal timer 0 enable
    csrw    mie, t6         // Internal timer 0 local interrupt enable
    csrwi   mstatus, 0x08   // Internal timer 0 global interrupt enable
    csrwi   mpmc, 0x03      // Initiate core halt with disable on mit0 interrupt
    li      s1, 0xFEEDABED  // Indicate halt init
    j       outer           // Return to infinite loop

.section .dccm
.global stdout
stdout: .word STDOUT
.global verbosity_g
verbosity_g: .word 2

.global intr_count
intr_count: .word 0
.global cptra_intr_rcv
cptra_intr_rcv: .word 0
