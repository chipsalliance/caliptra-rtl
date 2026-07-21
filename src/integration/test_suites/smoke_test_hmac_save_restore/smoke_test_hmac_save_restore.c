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
// Functional smoke for HMAC-384/-512 save/restore: take a two-block
// op, save the intermediate TAG after the first block, run an unrelated
// op to scramble engine state, then resume the original op via
// CTRL.RESTORE|LAST and check the final TAG matches the single-shot
// reference.
//
// Vectors are reused from src/hmac/tb/hmac_ctrl_tb.sv's
// hmac_double_block_test() so the references are pre-validated.
//
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "hmac.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// --- HMAC-384 two-block test vector (hmac_ctrl_tb.sv key4/data40/41/expected4) ---
static const uint32_t key_384[16] = {
    0x1e6a3e89,0x98be7c36,0xc5a511c4,0xf03fcfba,
    0x543d678f,0x1000e2f6,0xa61c2a95,0xf79bb006,
    0xfc782a67,0x9a0b890e,0x3374b20d,0xf710f6c2,
    0x00000000,0x00000000,0x00000000,0x00000000};

static const uint32_t block_a0_384[32] = {
    0xdbf031b4,0x3f84bcf3,0xcc9339e6,0x5c365915,
    0x1d3061dd,0x2d5fb0b2,0xd37fbe4f,0xca4ea373,
    0xb567ae35,0x13ea0950,0x13efc7b1,0x9f6851ad,
    0x73c26176,0x03496499,0x9c2c3cf2,0xfd58561a,
    0x9f791839,0xa2199f2a,0x9405edd0,0x478ac64a,
    0x9557aec8,0x6940d465,0xd9036448,0x9e4d32f1,
    0x68ce2eef,0xec74eb7e,0x653f8da6,0x40308f72,
    0xf0bd7b1a,0x698c6838,0x70c74398,0x69b969ae};

static const uint32_t block_a1_384[32] = {
    0xbea9f4f6,0xbacdc04d,0x4ec4f6bc,0xc1787494,
    0x0336c789,0x95538000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x000008b0};

static const uint32_t expected_tag_384[12] = {
    0x8aba65c0,0x7793e1d8,0xa709fbda,0x35ae7180,
    0x4dc07411,0x66dda574,0x6fb3b1c0,0xe91957bb,
    0xd0d539a4,0x69c2ea35,0x77b75d5c,0x0f150ce7};

// --- HMAC-512 two-block test vector (hmac_ctrl_tb.sv hmac512_tests key4) ---
static const uint32_t key_512[16] = {
    0xe1b52c4f,0xf8ce9c4b,0x60bd8ec7,0x85ab7bf3,
    0xdffc7023,0xf7c51588,0xf96b94ee,0xba80ca3b,
    0x9b9ed05a,0xb2ac8797,0xbb7039d6,0x81f2e41f,
    0xcfe6ddda,0xb2e95122,0xd9c716c2,0xb8406bd4};

static const uint32_t block_a0_512[32] = {
    0x54686973,0x20697320,0x61207465,0x73742075,
    0x73696e67,0x2061206c,0x61726765,0x72207468,
    0x616e2062,0x6c6f636b,0x2d73697a,0x65206b65,
    0x7920616e,0x64206120,0x6c617267,0x65722074,
    0x68616e20,0x626c6f63,0x6b2d7369,0x7a652064,
    0x6174612e,0x20546865,0x206b6579,0x206e6565,
    0x64732074,0x6f206265,0x20686173,0x68656420,
    0x6265666f,0x72652062,0x65696e67,0x20757365};

static const uint32_t block_a1_512[32] = {
    0x64206279,0x20746865,0x20484d41,0x4320616c,
    0x676f7269,0x74686d2e,0x80000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x000008C0};

static const uint32_t expected_tag_512[16] = {
    0xe37b6a77,0x5dc87dba,0xa4dfa9f9,0x6e5e3ffd,
    0xdebd71f8,0x86728986,0x5df5a32d,0x20cdc944,
    0xb6022cac,0x3c4982b1,0x0d5eeb55,0xc3e4de15,
    0x134676fb,0x6de04460,0x65c97440,0xfa8c6a58};

// --- Intervening single-block op that must NOT affect op A ---
static const uint32_t key_b[16] = {
    0xdeadbeef,0xdeadbeef,0xdeadbeef,0xdeadbeef,
    0xdeadbeef,0xdeadbeef,0xdeadbeef,0xdeadbeef,
    0xdeadbeef,0xdeadbeef,0xdeadbeef,0xdeadbeef,
    0xdeadbeef,0xdeadbeef,0xdeadbeef,0xdeadbeef};

static const uint32_t block_b[32] = {
    0xaa55aa55,0xaa55aa55,0xaa55aa55,0xaa55aa55,
    0xaa55aa55,0xaa55aa55,0xaa55aa55,0xaa55aa55,
    0x80000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000400};

static const uint32_t lfsr_seed_dwords[6] = {
    0xfeedface,0xdeadbeef,0xcafef00d,0x12345678,0x9abcdef0,0x0badc0de};

static void read_dwords(uint32_t base, uint32_t *dst, int n) {
    volatile uint32_t *p = (uint32_t *)(uintptr_t)base;
    for (int i = 0; i < n; i++) dst[i] = p[i];
}

static void run_save_restore_flow(BOOL is_512) {
    uint32_t saved_tag[16];
    uint32_t actual_tag[16];
    uint8_t  tag_dwords = is_512 ? 16 : 12;
    uint8_t  mode       = is_512 ? HMAC512_MODE : HMAC384_MODE;
    uint32_t *key       = (uint32_t *)(is_512 ? key_512      : key_384);
    uint32_t *blk0      = (uint32_t *)(is_512 ? block_a0_512 : block_a0_384);
    uint32_t *blk1      = (uint32_t *)(is_512 ? block_a1_512 : block_a1_384);
    const uint32_t *expected = is_512 ? expected_tag_512 : expected_tag_384;

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " save/restore: HMAC-%s\n", is_512 ? "512" : "384");
    VPRINTF(LOW, "----------------------------------\n");

    VPRINTF(LOW, "Step 1: INIT op A with block 0, snapshot intermediate TAG\n");
    hmac_wait_ready();
    hmac_load_inputs(key, blk0, (uint32_t *)lfsr_seed_dwords);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_INIT_MASK, mode, FALSE);
    hmac_wait_valid();
    read_dwords(CLP_HMAC_REG_HMAC512_TAG_0, saved_tag, 16);
    hmac_zeroize();

    VPRINTF(LOW, "Step 2: run unrelated op B to scramble engine state\n");
    hmac_wait_ready();
    hmac_load_inputs((uint32_t *)key_b, (uint32_t *)block_b, (uint32_t *)lfsr_seed_dwords);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_INIT_MASK |
                    HMAC_REG_HMAC512_CTRL_LAST_MASK, mode, FALSE);
    hmac_wait_valid();
    hmac_zeroize();

    VPRINTF(LOW, "Step 3: write saved TAG back, RESTORE|LAST with op A block 1\n");
    hmac_wait_ready();
    hmac_load_inputs(key, blk1, (uint32_t *)lfsr_seed_dwords);
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_TAG_0, saved_tag, 16);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_RESTORE_MASK |
                    HMAC_REG_HMAC512_CTRL_LAST_MASK, mode, FALSE);
    hmac_wait_valid();
    read_dwords(CLP_HMAC_REG_HMAC512_TAG_0, actual_tag, tag_dwords);

    VPRINTF(LOW, "Step 4: compare against single-shot reference\n");
    for (int i = 0; i < tag_dwords; i++) {
        if (actual_tag[i] != expected[i]) {
            VPRINTF(LOW, "FAIL: TAG[%d] = 0x%08x, expected 0x%08x\n",
                    i, actual_tag[i], expected[i]);
            SEND_STDOUT_CTRL(0x1);
            while (1);
        }
    }
    VPRINTF(LOW, "OK: HMAC-%s save/restore final TAG matches reference\n",
            is_512 ? "512" : "384");
    hmac_zeroize();
}

void main(void) {
    run_save_restore_flow(FALSE);
    run_save_restore_flow(TRUE);
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
