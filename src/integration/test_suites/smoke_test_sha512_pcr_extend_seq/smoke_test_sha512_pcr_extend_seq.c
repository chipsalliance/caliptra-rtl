// SPDX-License-Identifier: Apache-2.0
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
// Checks SHA512 command sequencing during a PCR hash extend:
//   - single-block (INIT+LAST) and two-block (INIT, NEXT+LAST) extends
//     produce SHA-384(PCR || data) in the PCR
//   - a second INIT, a leading NEXT, RESTORE, and a PCR hash generation
//     start are ignored while the extend is in progress
//   - ZEROIZE abandons the extend without modifying the PCR
//   - outside a PCR hash extend, a second INIT or a PCR hash generation start
//     without an intervening ZEROIZE is ignored; the digest is cleared,
//     VALID stays low and NEXT is ignored until ZEROIZE
//   - the PCR hash extend target cannot be changed while the result is
//     being written back

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include <stdint.h>
#include "printf.h"
#include "riscv_hw_if.h"
#include "sha512.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define POLL_LIMIT      100000
#define SETTLE_LOOPS    200
#define GEN_HASH_POLLS  2000
#define PCR_ID          6
#define PCR_ID2         7
#define REARM_WRITES    120
#define REARM_OFFSETS   8
#define PCR_DWORDS      12
#define BLOCK_DWORDS    32
#define PCR_ENTRY_ADDR(id, dw) (CLP_PV_REG_PCR_ENTRY_0_0 + ((id) * PCR_DWORDS + (dw)) * 4)
#define PCR_CTRL_ADDR(id)      (CLP_PV_REG_PCR_CTRL_0 + (id) * 4)
#define MODE_384 ((SHA512_384_MODE << SHA512_REG_SHA512_CTRL_MODE_LOW) & SHA512_REG_SHA512_CTRL_MODE_MASK)
#define MODE_512 ((SHA512_512_MODE << SHA512_REG_SHA512_CTRL_MODE_LOW) & SHA512_REG_SHA512_CTRL_MODE_MASK)

static const uint32_t abc_block[BLOCK_DWORDS] = {
    0x61626380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x00000018
};

static const uint32_t abc_sha512_kat[16] = {
    0xDDAF35A1, 0x93617ABA, 0xCC417349, 0xAE204131,
    0x12E6FA4E, 0x89A97EA2, 0x0A9EEEE6, 0x4B55D39A,
    0x2192992A, 0x274FC1A8, 0x36BA3C23, 0xA3FEEBBD,
    0x454D4423, 0x643CE80E, 0x2A9AC94F, 0xA54CA49F
};

static const uint32_t abc_sha384_kat[PCR_DWORDS] = {
    0xCB00753F, 0x45A35E8B, 0xB5A03D69, 0x9AC65007,
    0x272C32AB, 0x0EDED163, 0x1A8B605A, 0x43FF5BED,
    0x8086072B, 0xA1E7CC23, 0x58BAECA1, 0x34C825A7
};

static void fail(const char *msg) {
    VPRINTF(ERROR, "FAIL: %s\n", msg);
    SEND_STDOUT_CTRL(0x1);
    while (1);
}

static void settle(void) {
    for (volatile int i = 0; i < SETTLE_LOOPS; i++);
}

static void poll_mask(uint32_t addr, uint32_t mask, uint32_t want, const char *what) {
    for (uint32_t i = 0; i < POLL_LIMIT; i++) {
        if ((lsu_read_32(addr) & mask) == want) return;
    }
    VPRINTF(ERROR, "Timeout waiting for %s (reg=0x%x)\n", what, lsu_read_32(addr));
    fail("poll timeout");
}

static void wait_sha_ready(void) {
    poll_mask(CLP_SHA512_REG_SHA512_STATUS, SHA512_REG_SHA512_STATUS_READY_MASK,
              SHA512_REG_SHA512_STATUS_READY_MASK, "SHA READY");
}

static void wait_sha_ready_valid(void) {
    poll_mask(CLP_SHA512_REG_SHA512_STATUS,
              SHA512_REG_SHA512_STATUS_READY_MASK | SHA512_REG_SHA512_STATUS_VALID_MASK,
              SHA512_REG_SHA512_STATUS_READY_MASK | SHA512_REG_SHA512_STATUS_VALID_MASK,
              "SHA READY&VALID");
}

static void zeroize_and_settle(void) {
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL, SHA512_REG_SHA512_CTRL_ZEROIZE_MASK);
    settle();
    wait_sha_ready();
}

static void write_block(const uint32_t *blk) {
    for (uint32_t i = 0; i < BLOCK_DWORDS; i++) {
        lsu_write_32(CLP_SHA512_REG_SHA512_BLOCK_0 + 4 * i, blk[i]);
    }
}

static void send_cmd(uint32_t cmd) {
    wait_sha_ready();
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL, cmd | MODE_384);
    settle();
}

static void read_pcr_id(uint32_t id, uint32_t *pcr) {
    for (uint32_t i = 0; i < PCR_DWORDS; i++) {
        pcr[i] = lsu_read_32(PCR_ENTRY_ADDR(id, i));
    }
}

static void read_pcr(uint32_t *pcr) {
    read_pcr_id(PCR_ID, pcr);
}

static uint32_t compare_words(const char *tag, const uint32_t *act, const uint32_t *exp, uint32_t n) {
    uint32_t mism = 0;
    for (uint32_t i = 0; i < n; i++) {
        if (act[i] != exp[i]) {
            VPRINTF(LOW, "[%s] dw[%d] actual=0x%x expected=0x%x\n", tag, i, act[i], exp[i]);
            mism++;
        }
    }
    return mism;
}

static void expect_pcr(const char *tag, const uint32_t *exp) {
    uint32_t pcr[PCR_DWORDS];
    read_pcr(pcr);
    if (compare_words(tag, pcr, exp, PCR_DWORDS)) fail(tag);
    VPRINTF(LOW, "[%s] PCR%d matches expected\n", tag, PCR_ID);
}

// Ordinary (non-PCR) SHA-384 over n blocks; returns the 384-bit digest.
static void ordinary_sha384(uint32_t blocks[][BLOCK_DWORDS], uint32_t n, uint32_t *digest) {
    zeroize_and_settle();
    for (uint32_t b = 0; b < n; b++) {
        wait_sha_ready();
        write_block(blocks[b]);
        lsu_write_32(CLP_SHA512_REG_SHA512_CTRL,
                     (b == 0 ? SHA512_REG_SHA512_CTRL_INIT_MASK : SHA512_REG_SHA512_CTRL_NEXT_MASK) | MODE_384);
        wait_sha_ready_valid();
    }
    for (uint32_t i = 0; i < PCR_DWORDS; i++) {
        digest[i] = lsu_read_32(CLP_SHA512_REG_SHA512_DIGEST_0 + 4 * i);
    }
}

static void ordinary_sha512_kat(const char *tag) {
    uint32_t digest[16];
    zeroize_and_settle();
    write_block(abc_block);
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL, SHA512_REG_SHA512_CTRL_INIT_MASK | MODE_512);
    wait_sha_ready_valid();
    for (uint32_t i = 0; i < 16; i++) {
        digest[i] = lsu_read_32(CLP_SHA512_REG_SHA512_DIGEST_0 + 4 * i);
    }
    if (compare_words(tag, digest, abc_sha512_kat, 16)) fail(tag);
}

// A rejected INIT clears the digest; VALID stays low and NEXT is ignored until ZEROIZE.
static void expect_rejected_init(const char *tag) {
    if (lsu_read_32(CLP_SHA512_REG_SHA512_STATUS) & SHA512_REG_SHA512_STATUS_VALID_MASK) {
        VPRINTF(ERROR, "[%s] VALID set after rejected INIT\n", tag);
        fail(tag);
    }
    for (uint32_t i = 0; i < 16; i++) {
        if (lsu_read_32(CLP_SHA512_REG_SHA512_DIGEST_0 + 4 * i) != 0) {
            VPRINTF(ERROR, "[%s] DIGEST[%d] not cleared after rejected INIT\n", tag, i);
            fail(tag);
        }
    }
    VPRINTF(LOW, "[%s] INIT rejected\n", tag);
}

static void arm_pcr_extend(void) {
    uint32_t rd_status;
    zeroize_and_settle();
    poll_mask(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS, SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK,
              SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK, "VAULT_RD READY");
    lsu_write_32(CLP_SHA512_REG_SHA512_VAULT_RD_CTRL,
                 SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_MASK |
                 ((PCR_ID << SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_LOW) & SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_MASK) |
                 SHA512_REG_SHA512_VAULT_RD_CTRL_PCR_HASH_EXTEND_MASK);
    poll_mask(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS,
              SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK | SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_MASK,
              SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK | SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_MASK,
              "VAULT_RD READY&VALID");
    rd_status = lsu_read_32(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);
    if (rd_status & SHA512_REG_SHA512_VAULT_RD_STATUS_ERROR_MASK) {
        VPRINTF(ERROR, "VAULT_RD_STATUS=0x%x\n", rd_status);
        fail("PCR read reported error");
    }
}

static void wait_pcr_writeback(void) {
    wait_sha_ready_valid();
    settle();
    poll_mask(CLP_SHA512_REG_SHA512_KV_WR_STATUS,
              SHA512_REG_SHA512_KV_WR_STATUS_READY_MASK | SHA512_REG_SHA512_KV_WR_STATUS_VALID_MASK,
              SHA512_REG_SHA512_KV_WR_STATUS_READY_MASK | SHA512_REG_SHA512_KV_WR_STATUS_VALID_MASK,
              "KV_WR READY&VALID");
}

// Message = PCR (12 dwords) || data (48 bytes), padded into one block.
static void build_one_block(const uint32_t *pcr, uint32_t seed, uint32_t *blk) {
    for (uint32_t i = 0; i < BLOCK_DWORDS; i++) blk[i] = 0;
    for (uint32_t i = 0; i < PCR_DWORDS; i++) blk[i] = pcr[i];
    for (uint32_t i = 0; i < 12; i++) blk[PCR_DWORDS + i] = seed ^ (0x01010101 * (i + 1));
    blk[24] = 0x80000000;
    blk[31] = 96 * 8;
}

// Message = PCR (12 dwords) || data (72 bytes), padded into two blocks.
static void build_two_blocks(const uint32_t *pcr, uint32_t seed, uint32_t blks[2][BLOCK_DWORDS]) {
    for (uint32_t b = 0; b < 2; b++)
        for (uint32_t i = 0; i < BLOCK_DWORDS; i++) blks[b][i] = 0;
    for (uint32_t i = 0; i < PCR_DWORDS; i++) blks[0][i] = pcr[i];
    for (uint32_t i = 0; i < 18; i++) blks[0][PCR_DWORDS + i] = seed ^ (0x00010203 * (i + 1));
    blks[0][30] = 0x80000000;
    blks[1][31] = 120 * 8;
}

void main() {
    uint32_t pcr[PCR_DWORDS];
    uint32_t now[PCR_DWORDS];
    uint32_t expected[PCR_DWORDS];
    uint32_t blk1[1][BLOCK_DWORDS];
    uint32_t blk2[2][BLOCK_DWORDS];

    VPRINTF(LOW, "----------------------------------------------------\n");
    VPRINTF(LOW, " SHA512 PCR hash extend command sequencing\n");
    VPRINTF(LOW, "----------------------------------------------------\n");

    // Lock the PCR so that only hash extend can modify it.
    lsu_write_32(PCR_CTRL_ADDR(PCR_ID), PV_REG_PCR_CTRL_0_LOCK_MASK);
    read_pcr(pcr);
    lsu_write_32(PCR_CTRL_ADDR(PCR_ID), PV_REG_PCR_CTRL_0_LOCK_MASK | PV_REG_PCR_CTRL_0_CLEAR_MASK);
    settle();
    expect_pcr("lock", pcr);

    VPRINTF(LOW, "Phase 1: single-block extend\n");
    read_pcr(pcr);
    build_one_block(pcr, 0x11111111, blk1[0]);
    ordinary_sha384(blk1, 1, expected);
    arm_pcr_extend();
    write_block(blk1[0]);
    send_cmd(SHA512_REG_SHA512_CTRL_INIT_MASK | SHA512_REG_SHA512_CTRL_LAST_MASK);
    wait_pcr_writeback();
    expect_pcr("phase1", expected);

    VPRINTF(LOW, "Phase 2: two-block extend\n");
    read_pcr(pcr);
    build_two_blocks(pcr, 0x22222222, blk2);
    ordinary_sha384(blk2, 2, expected);
    arm_pcr_extend();
    write_block(blk2[0]);
    send_cmd(SHA512_REG_SHA512_CTRL_INIT_MASK);
    wait_sha_ready_valid();
    write_block(blk2[1]);
    send_cmd(SHA512_REG_SHA512_CTRL_NEXT_MASK | SHA512_REG_SHA512_CTRL_LAST_MASK);
    wait_pcr_writeback();
    expect_pcr("phase2", expected);

    VPRINTF(LOW, "Phase 3: second INIT ignored, ZEROIZE abandons extend\n");
    read_pcr(pcr);
    build_one_block(pcr, 0x33333333, blk1[0]);
    arm_pcr_extend();
    write_block(blk1[0]);
    send_cmd(SHA512_REG_SHA512_CTRL_INIT_MASK);
    wait_sha_ready_valid();
    write_block(abc_block);
    send_cmd(SHA512_REG_SHA512_CTRL_INIT_MASK | SHA512_REG_SHA512_CTRL_LAST_MASK);
    wait_sha_ready();
    settle();
    read_pcr(now);
    if (compare_words("phase3-kat", now, abc_sha384_kat, PCR_DWORDS) == 0) fail("phase3-kat");
    expect_pcr("phase3-restart", pcr);
    zeroize_and_settle();
    expect_pcr("phase3-zeroize", pcr);
    if (!(lsu_read_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_STATUS) & SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_READY_MASK))
        fail("GEN_PCR_HASH not ready after ZEROIZE");
    ordinary_sha512_kat("phase3-kat512");

    VPRINTF(LOW, "Phase 4: leading NEXT ignored, then INIT completes extend\n");
    read_pcr(pcr);
    build_one_block(pcr, 0x44444444, blk1[0]);
    ordinary_sha384(blk1, 1, expected);
    arm_pcr_extend();
    write_block(blk1[0]);
    send_cmd(SHA512_REG_SHA512_CTRL_NEXT_MASK | SHA512_REG_SHA512_CTRL_LAST_MASK);
    wait_sha_ready();
    settle();
    expect_pcr("phase4-next", pcr);
    write_block(blk1[0]);
    send_cmd(SHA512_REG_SHA512_CTRL_INIT_MASK | SHA512_REG_SHA512_CTRL_LAST_MASK);
    wait_pcr_writeback();
    expect_pcr("phase4", expected);

    VPRINTF(LOW, "Phase 5: PCR hash generation start ignored during extend\n");
    read_pcr(pcr);
    build_one_block(pcr, 0x55555555, blk1[0]);
    ordinary_sha384(blk1, 1, expected);
    arm_pcr_extend();
    write_block(blk1[0]);
    wait_sha_ready();
    lsu_write_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_CTRL, SHA512_REG_SHA512_GEN_PCR_HASH_CTRL_START_MASK);
    for (uint32_t i = 0; i < GEN_HASH_POLLS; i++) {
        if (lsu_read_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_STATUS) & SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_VALID_MASK)
            fail("PCR hash generation ran during extend");
    }
    expect_pcr("phase5-start", pcr);
    write_block(blk1[0]);
    send_cmd(SHA512_REG_SHA512_CTRL_INIT_MASK | SHA512_REG_SHA512_CTRL_LAST_MASK);
    wait_pcr_writeback();
    expect_pcr("phase5", expected);

    VPRINTF(LOW, "Phase 6: RESTORE ignored during extend\n");
    read_pcr(pcr);
    build_two_blocks(pcr, 0x66666666, blk2);
    ordinary_sha384(blk2, 2, expected);
    arm_pcr_extend();
    write_block(blk2[0]);
    send_cmd(SHA512_REG_SHA512_CTRL_INIT_MASK);
    wait_sha_ready_valid();
    write_block(blk2[1]);
    send_cmd(SHA512_REG_SHA512_CTRL_NEXT_MASK | SHA512_REG_SHA512_CTRL_RESTORE_MASK | SHA512_REG_SHA512_CTRL_LAST_MASK);
    wait_pcr_writeback();
    expect_pcr("phase6", expected);

    VPRINTF(LOW, "Phase 7: ZEROIZE required between operations\n");
    ordinary_sha512_kat("phase7-first");
    write_block(abc_block);
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL, SHA512_REG_SHA512_CTRL_INIT_MASK | MODE_512);
    settle();
    wait_sha_ready();
    expect_rejected_init("phase7-init");
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL, SHA512_REG_SHA512_CTRL_NEXT_MASK | MODE_512);
    settle();
    wait_sha_ready();
    expect_rejected_init("phase7-next");
    lsu_write_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_CTRL, SHA512_REG_SHA512_GEN_PCR_HASH_CTRL_START_MASK);
    for (uint32_t i = 0; i < GEN_HASH_POLLS; i++) {
        if (lsu_read_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_STATUS) & SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_VALID_MASK)
            fail("PCR hash generation ran without ZEROIZE");
    }
    ordinary_sha512_kat("phase7-after-zeroize");
    zeroize_and_settle();
    lsu_write_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_CTRL, SHA512_REG_SHA512_GEN_PCR_HASH_CTRL_START_MASK);
    poll_mask(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_STATUS,
              SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_READY_MASK | SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_VALID_MASK,
              SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_READY_MASK | SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_VALID_MASK,
              "GEN_PCR_HASH READY&VALID");
    write_block(abc_block);
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL, SHA512_REG_SHA512_CTRL_INIT_MASK | MODE_512);
    settle();
    wait_sha_ready();
    expect_rejected_init("phase7-after-gen");
    ordinary_sha512_kat("phase7-final");
    zeroize_and_settle();

    VPRINTF(LOW, "Phase 8: extend target locked during write back\n");
    lsu_write_32(PCR_CTRL_ADDR(PCR_ID2), PV_REG_PCR_CTRL_0_LOCK_MASK);
    // Sweep the re-arm timing so that the write-back window is hit regardless of bus cadence.
    for (uint32_t off = 0; off < REARM_OFFSETS; off++) {
        uint32_t pcr2[PCR_DWORDS];
        uint32_t now2[PCR_DWORDS];
        read_pcr_id(PCR_ID2, pcr2);
        read_pcr(pcr);
        build_one_block(pcr, 0x88888888 ^ off, blk1[0]);
        ordinary_sha384(blk1, 1, expected);
        arm_pcr_extend();
        write_block(blk1[0]);
        wait_sha_ready();
        lsu_write_32(CLP_SHA512_REG_SHA512_CTRL,
                     SHA512_REG_SHA512_CTRL_INIT_MASK | SHA512_REG_SHA512_CTRL_LAST_MASK | MODE_384);
        for (uint32_t d = 0; d < off; d++) __asm__ volatile ("nop");
        for (uint32_t i = 0; i < REARM_WRITES; i++) {
            lsu_write_32(CLP_SHA512_REG_SHA512_VAULT_RD_CTRL,
                         SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_MASK |
                         ((PCR_ID2 << SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_LOW) & SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_MASK) |
                         SHA512_REG_SHA512_VAULT_RD_CTRL_PCR_HASH_EXTEND_MASK);
        }
        settle();
        poll_mask(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS, SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK,
                  SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK, "VAULT_RD READY");
        poll_mask(CLP_SHA512_REG_SHA512_KV_WR_STATUS, SHA512_REG_SHA512_KV_WR_STATUS_READY_MASK,
                  SHA512_REG_SHA512_KV_WR_STATUS_READY_MASK, "KV_WR READY");
        zeroize_and_settle();
        read_pcr_id(PCR_ID2, now2);
        if (compare_words("phase8-pcr7", now2, pcr2, PCR_DWORDS)) {
            VPRINTF(ERROR, "[phase8] offset %d\n", off);
            fail("phase8-pcr7");
        }
        expect_pcr("phase8", expected);
    }
    VPRINTF(LOW, "[phase8] PCR%d unchanged across %d offsets\n", PCR_ID2, REARM_OFFSETS);
    ordinary_sha512_kat("phase8-final");
    zeroize_and_settle();

    VPRINTF(LOW, "All phases passed\n");
    SEND_STDOUT_CTRL(0xff);
}
