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
// Verify CTRL.MODE is protected from mid-operation changes. The MODE
// field has swwe = ready_reg, so a CTRL write attempted while the
// engine is BUSY must NOT clobber the in-flight mode. The test starts
// an HMAC-384 multi-block op, attempts to flip CTRL.MODE to HMAC-512
// before the engine returns to READY, and confirms the final TAG
// still matches HMAC-384.
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

static uint32_t key_384[16] = {
    0x1e6a3e89,0x98be7c36,0xc5a511c4,0xf03fcfba,
    0x543d678f,0x1000e2f6,0xa61c2a95,0xf79bb006,
    0xfc782a67,0x9a0b890e,0x3374b20d,0xf710f6c2,
    0x00000000,0x00000000,0x00000000,0x00000000};

static uint32_t block_a0[32] = {
    0xdbf031b4,0x3f84bcf3,0xcc9339e6,0x5c365915,
    0x1d3061dd,0x2d5fb0b2,0xd37fbe4f,0xca4ea373,
    0xb567ae35,0x13ea0950,0x13efc7b1,0x9f6851ad,
    0x73c26176,0x03496499,0x9c2c3cf2,0xfd58561a,
    0x9f791839,0xa2199f2a,0x9405edd0,0x478ac64a,
    0x9557aec8,0x6940d465,0xd9036448,0x9e4d32f1,
    0x68ce2eef,0xec74eb7e,0x653f8da6,0x40308f72,
    0xf0bd7b1a,0x698c6838,0x70c74398,0x69b969ae};

static uint32_t block_a1[32] = {
    0xbea9f4f6,0xbacdc04d,0x4ec4f6bc,0xc1787494,
    0x0336c789,0x95538000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x000008b0};

static uint32_t expected_tag_384[12] = {
    0x8aba65c0,0x7793e1d8,0xa709fbda,0x35ae7180,
    0x4dc07411,0x66dda574,0x6fb3b1c0,0xe91957bb,
    0xd0d539a4,0x69c2ea35,0x77b75d5c,0x0f150ce7};

static uint32_t lfsr_seed_dwords[6] = {
    0xfeedface,0xdeadbeef,0xcafef00d,0x12345678,0x9abcdef0,0x0badc0de};

void main(void) {
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC mode-change mid-op test\n");
    VPRINTF(LOW, "----------------------------------\n");

    VPRINTF(LOW, "Step 1: load KEY/BLOCK/SEED and start INIT in HMAC-384 mode\n");
    hmac_wait_ready();
    hmac_load_inputs(key_384, block_a0, lfsr_seed_dwords);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_INIT_MASK, HMAC384_MODE, FALSE);

    VPRINTF(LOW, "Step 2: while engine is BUSY, attempt to flip MODE to HMAC-512 (must be rejected)\n");
    hmac_ctrl_write(0, HMAC512_MODE, FALSE);

    VPRINTF(LOW, "Step 3: wait_ready and drive block 1 with NEXT|LAST in HMAC-384 mode\n");
    hmac_wait_ready();
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, block_a1, 32);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_NEXT_MASK |
                    HMAC_REG_HMAC512_CTRL_LAST_MASK, HMAC384_MODE, FALSE);
    hmac_wait_valid();

    VPRINTF(LOW, "Step 4: compare final TAG against HMAC-384 reference\n");
    volatile uint32_t *p = (uint32_t *)CLP_HMAC_REG_HMAC512_TAG_0;
    for (int i = 0; i < 12; i++) {
        if (p[i] != expected_tag_384[i]) {
            VPRINTF(LOW, "FAIL: TAG[%d] = 0x%08x, expected 0x%08x\n",
                    i, p[i], expected_tag_384[i]);
            VPRINTF(LOW, "FAIL: mid-op MODE change was NOT rejected\n");
            SEND_STDOUT_CTRL(0x1);
            while (1);
        }
    }
    VPRINTF(LOW, "OK: mid-op MODE write rejected, HMAC-384 TAG matches\n");
    hmac_zeroize();

    SEND_STDOUT_CTRL(0xff);
    while (1);
}
