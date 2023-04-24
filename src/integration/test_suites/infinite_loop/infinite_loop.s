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

#include "caliptra_defines.h"

.set    mfdc, 0x7f9

// Code to execute
.section .text
.global _start
_start:

    // Enable Caches in MRAC
    li      x1, 0xaaaaaaaa
    csrw    0x7c0, x1

    li      x3, 4
    csrw    mfdc, x3        // disable store merging

loop:
    jal     x0, loop

// Write 0xff to STDOUT for TB to termiate test.
_finish:
    li      x3, STDOUT
    addi    x5, x0, 0xff
    sb      x5, 0(x3)
    beq     x0, x0, _finish
.rept 100
    nop
.endr

.section .dccm
.global stdout
stdout: .word STDOUT
.global verbosity_g
verbosity_g: .word 2

//.section .data_iccm0, "ax"
