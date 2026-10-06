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

// memCpy_ROM_to_dccm
// ------------------
// Directed pre-silicon test that exercises the ROM(imem) -> DCCM datapath.
//   1. A known 16-word source block lives in .text, i.e. it is loaded into
//      imem/ROM (VMA base 0x0) as part of program.hex. The block is read out
//      of ROM ONCE into registers x16..x31 (the only bus reads from ROM).
//   2. ONE fill pass tiles that block across the ENTIRE DCCM
//      (RV_DCCM_SADR .. RV_DCCM_EADR) via register->DCCM stores, so both the
//      low and high DCCM address boundaries get written.
//   3. ONE check pass reads every DCCM word back and compares it against the
//      cached source registers (no second ROM read).
// A '.' is emitted to the console every 16 KiB so the run is visibly alive;
// 'F' marks the fill phase and 'C' the check phase. Any miscompare (or an
// unexpected trap) ends the sim Failed (STDOUT=0x1); a fully matching readback
// ends Success (STDOUT=0xff).
//
// Rough cost: 64 KiB words, so ~4096 64-byte blocks per phase. The bulk traffic
// is DCCM-only (ROM is touched just 16 times), so expect very roughly
// ~0.3-0.5M core cycles of compute on top of boot. Give MAX_CYCLES margin
// (the TB default of 20,000,000 is plenty; ~1,000,000 is a safe lower bound).

#include "caliptra_defines.h"

#define PROG_BLKS 256          // 64-byte blocks between progress dots (16 KiB)

.section .text
.global _start
_start:

    // Clear minstret
    csrw minstret, zero
    csrw minstreth, zero

    // MRAC: imem (region 0) cacheable / no side-effects so ROM loads work,
    // DCCM (region 5) no side-effects. Same encoding crt0 uses.
    li   x1, 0xAAAAA0A9
    csrw 0x7c0, x1
    fence.i

    // Route any unexpected trap (e.g. access/ECC fault) to the fail handler
    // instead of hanging the sim.
    la   x1, fail
    csrw mtvec, x1

    li   x10, STDOUT             // console / TB control port

    // --- Cache the ROM source block (imem) into registers, one time ---
    la   x4, rom_src
    lw   x16, 0(x4)
    lw   x17, 4(x4)
    lw   x18, 8(x4)
    lw   x19, 12(x4)
    lw   x20, 16(x4)
    lw   x21, 20(x4)
    lw   x22, 24(x4)
    lw   x23, 28(x4)
    lw   x24, 32(x4)
    lw   x25, 36(x4)
    lw   x26, 40(x4)
    lw   x27, 44(x4)
    lw   x28, 48(x4)
    lw   x29, 52(x4)
    lw   x30, 56(x4)
    lw   x31, 60(x4)

    // dst end = one past the high DCCM boundary (0x50040000)
    li   x7, RV_DCCM_EADR
    addi x7, x7, 1

    // --- FILL: tile the cached block across the whole DCCM ---
    li   x5, 0x46               // 'F'
    sb   x5, 0(x10)
    li   x3, RV_DCCM_SADR       // dst = DCCM low boundary (0x50000000)
    li   x11, PROG_BLKS
fill_blk:
    sw   x16, 0(x3)
    sw   x17, 4(x3)
    sw   x18, 8(x3)
    sw   x19, 12(x3)
    sw   x20, 16(x3)
    sw   x21, 20(x3)
    sw   x22, 24(x3)
    sw   x23, 28(x3)
    sw   x24, 32(x3)
    sw   x25, 36(x3)
    sw   x26, 40(x3)
    sw   x27, 44(x3)
    sw   x28, 48(x3)
    sw   x29, 52(x3)
    sw   x30, 56(x3)
    sw   x31, 60(x3)
    addi x3, x3, 64
    addi x11, x11, -1
    bnez x11, .Lfill_noprog
    li   x5, 0x2E               // '.'
    sb   x5, 0(x10)
    li   x11, PROG_BLKS
.Lfill_noprog:
    bltu x3, x7, fill_blk

    li   x5, 0x0A               // '\n'
    sb   x5, 0(x10)

    // --- CHECK: read every DCCM word back, compare to cached source ---
    li   x5, 0x43               // 'C'
    sb   x5, 0(x10)
    li   x3, RV_DCCM_SADR
    li   x11, PROG_BLKS
chk_blk:
    lw   x5, 0(x3)
    bne  x5, x16, fail
    lw   x5, 4(x3)
    bne  x5, x17, fail
    lw   x5, 8(x3)
    bne  x5, x18, fail
    lw   x5, 12(x3)
    bne  x5, x19, fail
    lw   x5, 16(x3)
    bne  x5, x20, fail
    lw   x5, 20(x3)
    bne  x5, x21, fail
    lw   x5, 24(x3)
    bne  x5, x22, fail
    lw   x5, 28(x3)
    bne  x5, x23, fail
    lw   x5, 32(x3)
    bne  x5, x24, fail
    lw   x5, 36(x3)
    bne  x5, x25, fail
    lw   x5, 40(x3)
    bne  x5, x26, fail
    lw   x5, 44(x3)
    bne  x5, x27, fail
    lw   x5, 48(x3)
    bne  x5, x28, fail
    lw   x5, 52(x3)
    bne  x5, x29, fail
    lw   x5, 56(x3)
    bne  x5, x30, fail
    lw   x5, 60(x3)
    bne  x5, x31, fail
    addi x3, x3, 64
    addi x11, x11, -1
    bnez x11, .Lchk_noprog
    li   x5, 0x2E               // '.'
    sb   x5, 0(x10)
    li   x11, PROG_BLKS
.Lchk_noprog:
    bltu x3, x7, chk_blk

    li   x5, 0x0A               // '\n'
    sb   x5, 0(x10)

    // --- Pass: 0xff to STDOUT for TB to terminate with Success ---
    li   x5, 0xff
    sb   x5, 0(x10)
pass_spin:
    j    pass_spin

    // --- Fail: 0x1 to STDOUT for TB to terminate with Failed status ---
.align 2
fail:
    li   x10, STDOUT
    li   x5, 0x1
    sb   x5, 0(x10)
fail_spin:
    j    fail_spin

    // ROM-resident source data. It sits in .text (imem/ROM) and is reached
    // only by data loads, never by execution. Distinct, recognizable word
    // values make a miscompare easy to spot in waves.
.align 2
rom_src:
    .word 0xDEADBEEF
    .word 0xCAFEF00D
    .word 0x01234567
    .word 0x89ABCDEF
    .word 0xA5A5A5A5
    .word 0x5A5A5A5A
    .word 0xFFFFFFFF
    .word 0x00000000
    .word 0x0F0F0F0F
    .word 0xF0F0F0F0
    .word 0x13579BDF
    .word 0x2468ACE0
    .word 0xC0FFEE00
    .word 0xBADC0DE1
    .word 0xFEEDFACE
    .word 0x8BADF00D
rom_src_end:

// DCCM-resident globals required by the always-linked printf / ISR libs.
.section .dccm
.global stdout
stdout: .word STDOUT
.global verbosity_g
verbosity_g: .word 2
.global intr_count
intr_count: .word 0
.global cptra_intr_rcv
cptra_intr_rcv: .word 0
