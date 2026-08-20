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
// Drive a CSR_MODE partial HMAC-512 INIT (no LAST). Verify that the
// SW-readable TAG stays at zero and that error3_sts
// asserts, then finalize with NEXT|LAST and confirm the SW-readable
// TAG is no longer masked.
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

static uint32_t block0[32] = {
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080};

static uint32_t block1[32] = {
    0x80000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00001400};

static uint32_t lfsr_seed_dwords[6] = {
    0xfeedface,0xdeadbeef,0xcafef00d,0x12345678,0x9abcdef0,0x0badc0de};

void main(void) {
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC CSR intermediate-tag-hidden test\n");
    VPRINTF(LOW, "----------------------------------\n");

    VPRINTF(LOW, "Step 1: INIT in CSR_MODE with block 0\n");
    hmac_wait_ready();
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, block0, 32);
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0, lfsr_seed_dwords, 6);
    hmac512_ctrl_write(HMAC_REG_HMAC512_CTRL_INIT_MASK, TRUE);
    hmac_wait_valid();

    VPRINTF(LOW, "Step 2: read TAG, expect 0 + error3_sts on the read\n");
    if (hmac_read_tag_or(16) != 0) {
        VPRINTF(LOW, "FAIL: CSR partial-op TAG leaked\n");
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
    hmac_check_error_intr(
        HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK,
        0x1);
    VPRINTF(LOW, "OK: CSR partial-op TAG masked, error3_sts fired on TAG read\n");

    VPRINTF(LOW, "Step 3: NEXT|LAST in CSR_MODE with block 1 -> final TAG must be visible\n");
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, block1, 32);
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0, lfsr_seed_dwords, 6);
    hmac512_ctrl_write(HMAC_REG_HMAC512_CTRL_NEXT_MASK |
                       HMAC_REG_HMAC512_CTRL_LAST_MASK, TRUE);
    hmac_wait_valid();

    if (hmac_read_tag_or(16) == 0) {
        VPRINTF(LOW, "FAIL: CSR final TAG is unexpectedly zero\n");
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
    VPRINTF(LOW, "OK: CSR final TAG visible to SW after LAST\n");
    hmac_zeroize();

    SEND_STDOUT_CTRL(0xff);
    while (1);
}
