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
// Functional smoke for HMAC-224/-256 save/restore: take a two-block
// op, save the intermediate TAG after the first block, run an unrelated
// op to scramble engine state, then resume the original op via
// CTRL.RESTORE|LAST and check the final TAG matches the single-shot
// reference.
//
// Vectors are reused from src/hmac256/tb/hmac256_ctrl_tb.sv's
// hmac256_tests()/hmac224_tests() so the references are pre-validated.
//
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "hmac256.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define HMAC256_MODE_SHA_256 1u
#define HMAC256_MODE_SHA_224 0u

// --- Two-block test vector (hmac256_ctrl_tb.sv key4/data4_0/data4_1) ---
static const uint32_t key_2blk[HMAC256_KEY_SIZE] = {
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,
    0x0b0b0b0b,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000};

static const uint32_t block_a0_2blk[HMAC256_BLOCK_SIZE] = {
    0x61626364,0x62636465,0x63646566,0x64656667,
    0x65666768,0x66676869,0x6768696a,0x68696a6b,
    0x696a6b6c,0x6a6b6c6d,0x6b6c6d6e,0x6c6d6e6f,
    0x6d6e6f70,0x6e6f7071,0x80000000,0x00000000};

static const uint32_t block_a1_2blk[HMAC256_BLOCK_SIZE] = {
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x000003c0};

static const uint32_t expected_tag_256[HMAC256_TAG_SIZE] = {
    0xcf86b015,0xaf9fadf1,0xec439642,0xbe2458fc,
    0x7da3c8e4,0xeffce404,0xa32ce41f,0xd0e213d3};

static const uint32_t expected_tag_224[HMAC224_TAG_SIZE] = {
    0x2f1b0d0c,0x449f8b67,0x3657684b,0xecd7e519,
    0x52328640,0x2f3aa9b8,0x379d63ef};

// --- Intervening single-block op (RFC 4231 #1) that must NOT affect op A ---
static const uint32_t key_b[HMAC256_KEY_SIZE] = {
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,
    0x0b0b0b0b,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000};

static const uint32_t block_b[HMAC256_BLOCK_SIZE] = {
    0x48692054,0x68657265,0x80000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000240};

static const uint32_t lfsr_seed_dwords[HMAC256_LFSR_SEED_SIZE] = {
    0xC8F518D4,0xF3AA1BD4,0x6ED56C1C,
    0x3C9E16FB,0x800AF504,0xC8F518D4};

static void read_dwords(uint32_t base, uint32_t *dst, int n) {
    volatile uint32_t *p = (uint32_t *)(uintptr_t)base;
    for (int i = 0; i < n; i++) dst[i] = p[i];
}

static void run_save_restore_flow(BOOL is_256) {
    uint32_t saved_tag[HMAC256_TAG_SIZE];
    uint32_t actual_tag[HMAC256_TAG_SIZE];
    uint8_t  tag_dwords = is_256 ? HMAC256_TAG_SIZE : HMAC224_TAG_SIZE;
    uint8_t  mode       = is_256 ? HMAC256_MODE_SHA_256 : HMAC256_MODE_SHA_224;
    const uint32_t *expected = is_256 ? expected_tag_256 : expected_tag_224;

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " save/restore: HMAC-SHA-%s\n", is_256 ? "256" : "224");
    VPRINTF(LOW, "----------------------------------\n");

    VPRINTF(LOW, "Step 1: INIT op A with block 0, snapshot intermediate TAG\n");
    hmac256_wait_ready();
    hmac256_load_inputs((uint32_t *)key_2blk, (uint32_t *)block_a0_2blk,
                        (uint32_t *)lfsr_seed_dwords);
    hmac256_ctrl_write(HMAC256_REG_HMAC256_CTRL_INIT_MASK, mode);
    hmac256_wait_valid();
    read_dwords(CLP_HMAC256_REG_HMAC256_TAG_0, saved_tag, HMAC256_TAG_SIZE);
    hmac256_zeroize();

    VPRINTF(LOW, "Step 2: run unrelated op B to scramble engine state\n");
    hmac256_wait_ready();
    hmac256_load_inputs((uint32_t *)key_b, (uint32_t *)block_b,
                        (uint32_t *)lfsr_seed_dwords);
    hmac256_ctrl_write(HMAC256_REG_HMAC256_CTRL_INIT_MASK |
                       HMAC256_REG_HMAC256_CTRL_LAST_MASK, mode);
    hmac256_wait_valid();
    hmac256_zeroize();

    VPRINTF(LOW, "Step 3: write saved TAG back, RESTORE|LAST with op A block 1\n");
    hmac256_wait_ready();
    hmac256_load_inputs((uint32_t *)key_2blk, (uint32_t *)block_a1_2blk,
                        (uint32_t *)lfsr_seed_dwords);
    write_hmac256_reg((volatile uint32_t *)CLP_HMAC256_REG_HMAC256_TAG_0,
                      saved_tag, HMAC256_TAG_SIZE);
    hmac256_ctrl_write(HMAC256_REG_HMAC256_CTRL_RESTORE_MASK |
                       HMAC256_REG_HMAC256_CTRL_LAST_MASK, mode);
    hmac256_wait_valid();
    read_dwords(CLP_HMAC256_REG_HMAC256_TAG_0, actual_tag, tag_dwords);

    VPRINTF(LOW, "Step 4: compare against single-shot reference\n");
    for (int i = 0; i < tag_dwords; i++) {
        if (actual_tag[i] != expected[i]) {
            VPRINTF(LOW, "FAIL: TAG[%d] = 0x%08x, expected 0x%08x\n",
                    i, actual_tag[i], expected[i]);
            SEND_STDOUT_CTRL(0x1);
            while (1);
        }
    }
    VPRINTF(LOW, "OK: HMAC-SHA-%s save/restore final TAG matches reference\n",
            is_256 ? "256" : "224");
    hmac256_zeroize();
}

void main(void) {
    init_interrupts();
    run_save_restore_flow(FALSE);
    run_save_restore_flow(TRUE);
    VPRINTF(LOW, "* TESTCASE PASSED\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
