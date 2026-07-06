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
// Verify that when an HMAC key or block is sourced from KeyVault, the
// SW-readable TAG register reads back zero for BOTH the intermediate
// completion (after INIT) and the final completion (after LAST). Per
// spec section "Key vault cryptographic functional block": when a key
// is read from KV, the API register is locked and the digest is not
// readable by firmware; the only legal sink is a KV slot via
// HMAC512_KV_WR_CTRL. Reading the masked TAG also raises error3_sts
// on the read cycle (consent-based notification).
//
// Three input combinations are exercised: KV key + SW block, SW key +
// KV block, and KV key + KV block.
//
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "hmac.h"
#include "caliptra_rtl_lib.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

static uint32_t block_msg[32] = {
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080,
    0x80808080,0x80808080,0x80808080,0x80808080};

static uint32_t sw_key[16] = {
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b};

static uint32_t lfsr_seed_dwords[6] = {
    0xfeedface,0xdeadbeef,0xcafef00d,0x12345678,0x9abcdef0,0x0badc0de};

static void run_subtest(const char *label, BOOL key_from_kv, BOOL block_from_kv, BOOL dest_to_kv) {
    const uint8_t KV_KEY_SLOT   = 0;
    const uint8_t KV_BLOCK_SLOT = 1;
    const uint8_t KV_DEST_SLOT  = 2;

    VPRINTF(LOW, "--- %s ---\n", label);
    hmac_wait_ready();

    if (key_from_kv) {
        lsu_write_32(STDOUT, (KV_KEY_SLOT << 8) | 0xa9);
        hmac_enable_kv_key(KV_KEY_SLOT);
    } else {
        write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_KEY_0, sw_key, 16);
    }

    if (block_from_kv) {
        lsu_write_32(STDOUT, (KV_BLOCK_SLOT << 8) | 0xb0);
        hmac_enable_kv_block(KV_BLOCK_SLOT);
    } else {
        write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, block_msg, 32);
    }

    if (dest_to_kv) {
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL,
            HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
            HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK   |
            HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK |
            ((KV_DEST_SLOT << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
             HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK));
    }

    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0, lfsr_seed_dwords, 6);
    hmac512_ctrl_write(HMAC_REG_HMAC512_CTRL_INIT_MASK, FALSE);
    hmac_wait_valid();

    if (hmac_read_tag_or(16) != 0) {
        VPRINTF(LOW, "FAIL: %s leaked intermediate TAG\n", label);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
    hmac_check_error_intr(
        HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK,
        0x1);

    if (key_from_kv) {
        lsu_write_32(STDOUT, (KV_KEY_SLOT << 8) | 0xa9);
        hmac_enable_kv_key(KV_KEY_SLOT);
    } else {
        write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_KEY_0, sw_key, 16);
    }
    if (block_from_kv) {
        lsu_write_32(STDOUT, (KV_BLOCK_SLOT << 8) | 0xb0);
        hmac_enable_kv_block(KV_BLOCK_SLOT);
    } else {
        write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, block_msg, 32);
    }
    if (dest_to_kv) {
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL,
            HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
            HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK   |
            HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK |
            ((KV_DEST_SLOT << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
             HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK));
    }
    hmac512_ctrl_write(HMAC_REG_HMAC512_CTRL_NEXT_MASK |
                       HMAC_REG_HMAC512_CTRL_LAST_MASK, FALSE);
    hmac_wait_valid();

    if (hmac_read_tag_or(16) != 0) {
        VPRINTF(LOW, "FAIL: %s leaked final TAG\n", label);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
    hmac_check_error_intr(
        HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK,
        0x1);
    hmac_zeroize();
}

void main(void) {
    VPRINTF(LOW, "HMAC KV tag-hidden test\n");

    run_subtest("KV key, SW block",          TRUE,  FALSE, FALSE);
    run_subtest("SW key, KV block",          FALSE, TRUE,  FALSE);
    run_subtest("KV key, KV block",          TRUE,  TRUE,  FALSE);
    run_subtest("SW key, SW block, KV dest", FALSE, FALSE, TRUE);

    SEND_STDOUT_CTRL(0xff);
    while (1);
}
