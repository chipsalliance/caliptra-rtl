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
// Multi-block HMAC512 with a KeyVault-sourced key must never expose the
// KV-keyed inner SHA-512 chaining state through the FW-readable TAG, and
// save/restore must not be usable with KV- or CSR-sourced keys.
//
//  1. KV key: INIT (no LAST), NEXT (no LAST) WITHOUT reloading the key,
//     then NEXT|LAST to a KV slot. Both intermediate TAG reads must be
//     zero and raise error3; the final result must land in KV.
//  2. KV key: RESTORE|NEXT must be rejected with error2.
//  3. KV key: NEXT|LAST without a preceding INIT must be rejected (error2).
//  4. FW key: INIT (no LAST) exposes the inner state (save path), a KV key
//     read requested mid-operation is refused, and NEXT|LAST still produces
//     the expected HMAC with the FW key.
//  5. CSR key: INIT (no LAST) with CSR_MODE, then NEXT (no LAST) written
//     with CSR_MODE=0 must not expose the CSR-keyed inner state.
//
// Expected values were generated with Python hashlib/hmac (HMAC-SHA512).
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

#define KV_KEY_SLOT  0
#define KV_DEST_SLOT 2

static uint32_t k_fw[16] = {
    0xdc40879b, 0x4b42694e, 0x351acffd, 0xb1bf7e77,
    0xb8c7ad45, 0x467a7644, 0x393c6562, 0xb08d704d,
    0x2f6e5de2, 0xc5fede67, 0xa1a28fc8, 0x4b37f1b2,
    0xa63c844e, 0x9a420589, 0xcabae261, 0x24084dbe};

static uint32_t b1[32] = {
    0xfa0b11c4, 0xa1bb792c, 0x83a40189, 0x7324a1b0,
    0x9b0dc00d, 0xa04d1769, 0x45775e55, 0x7f9b2071,
    0xcc442941, 0x43cc8740, 0xc274a2bb, 0xa16bcd25,
    0x4975a92a, 0x8d98f5fb, 0x60adaae7, 0x57af1bf7,
    0xedbbad57, 0x998cf8db, 0x1dffa5b3, 0xa2bbbef9,
    0x1937fb92, 0x78376b60, 0x40b19393, 0x8e5b4bce,
    0x8f48cf7a, 0x24364f67, 0xb6d046c8, 0x36462b24,
    0xaae36b9b, 0xaf088adc, 0x0e80f548, 0xda01dbee};

static uint32_t b2[32] = {
    0x01a2a0d1, 0xa2aac91e, 0x1aee89c1, 0x59a1be5b,
    0x690c342d, 0x2cabbb50, 0xe77e152f, 0x6327d58e,
    0x7fe144eb, 0xc59667c1, 0x35e55c02, 0x1a542c2f,
    0xf4ee7101, 0x4704bc5f, 0x6ea95094, 0x19635df3,
    0xe5367f0e, 0x2d965238, 0xf2db7ed3, 0xfd1582b9,
    0x58932ebe, 0xdec5b756, 0x19ac5f75, 0xb2ca02fd,
    0x44b7565b, 0x06bc22e3, 0x262ce623, 0x10dff6a5,
    0xa609798d, 0x44dc03b0, 0x57976b13, 0x6ab1555f};

static uint32_t b2f[32] = {
    0x83afd049, 0xee34195e, 0x1642f714, 0xea8f0156,
    0x24563ebe, 0x326bfa09, 0x61b461c5, 0xeabd8cbc,
    0x50742f38, 0x9effe9a1, 0x3e78f831, 0x4ac5d38e,
    0xf822d8f3, 0x901e820b, 0xaa86861f, 0x312100c7,
    0x119661cc, 0x6ec0a7d5, 0x3377d345, 0xe45c1805,
    0xe6e7ecd2, 0xc643df12, 0xe8d31df9, 0xa2a21a83,
    0x01729953, 0x80000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000b20};

static uint32_t h1_fw[16] = {
    0x994dcf40, 0x088f616d, 0xc94b2dfe, 0x2a47df02,
    0xe6032c32, 0x1841e2d1, 0x573a024e, 0x8d2c7b4b,
    0x9ec3eca8, 0x5a29944e, 0x033623b4, 0x5f8627b3,
    0xe85dae7e, 0xe548d3c9, 0x4dab31e4, 0x0b2d8deb};

static uint32_t t_fw[16] = {
    0xd78038aa, 0x85b09963, 0xf6db7bac, 0x0bccfd47,
    0x08a4582c, 0xf0241e64, 0xc561f760, 0x4284b2a2,
    0xd08ba4fd, 0x077f899b, 0x415ad6f7, 0x9a2db643,
    0x42bc8b35, 0x9bbdaea5, 0x22b6042c, 0x514a3111};

static uint32_t lfsr_seed_dwords[6] = {
    0xfeedface,0xdeadbeef,0xcafef00d,0x12345678,0x9abcdef0,0x0badc0de};

static void fail(const char *msg) {
    VPRINTF(LOW, "FAIL: %s\n", msg);
    SEND_STDOUT_CTRL(0x1);
    while (1);
}

static void expect_tag_hidden(const char *label) {
    if (hmac_read_tag_or(16) != 0) fail(label);
    hmac_check_error_intr(HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK, 0x1);
}

static void expect_tag(const uint32_t *exp, const char *label) {
    volatile uint32_t *p = (uint32_t *)CLP_HMAC_REG_HMAC512_TAG_0;
    for (int i = 0; i < 16; i++) {
        if (p[i] != exp[i]) {
            VPRINTF(LOW, "TAG[%d] act 0x%08x exp 0x%08x\n", i, p[i], exp[i]);
            fail(label);
        }
    }
}

static void load_kv_key(void) {
    lsu_write_32(STDOUT, (KV_KEY_SLOT << 8) | 0xa9);
    hmac_enable_kv_key(KV_KEY_SLOT);
}

static void set_kv_dest(void) {
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL,
        HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
        HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK |
        ((KV_DEST_SLOT << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
         HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK));
}

// Command rejected: error2 raised and no tag produced
static void expect_rejected(const char *label) {
    for (int i = 0; i < 200; i++) __asm__ volatile ("nop");
    if (lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_VALID_MASK) fail(label);
    hmac_check_error_intr(HMAC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK, 0x1);
}

static void test_kv_key_no_intermediate_leak(void) {
    VPRINTF(LOW, "--- KV key, INIT/NEXT/NEXT|LAST without key reload ---\n");
    hmac_wait_ready();
    load_kv_key();
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0, lfsr_seed_dwords, 6);
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, b1, 32);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_INIT_MASK, HMAC512_MODE, FALSE);
    hmac_wait_valid();
    expect_tag_hidden("intermediate TAG after INIT not hidden");

    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, b2, 32);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_NEXT_MASK, HMAC512_MODE, FALSE);
    hmac_wait_valid();
    expect_tag_hidden("KV-keyed inner state leaked in TAG after NEXT");

    set_kv_dest();
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, b2f, 32);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_NEXT_MASK | HMAC_REG_HMAC512_CTRL_LAST_MASK, HMAC512_MODE, FALSE);
    hmac_wait_valid();
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS) & HMAC_REG_HMAC512_KV_WR_STATUS_VALID_MASK) == 0);
    if (lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS) & HMAC_REG_HMAC512_KV_WR_STATUS_ERROR_MASK) fail("KV write error");
    expect_tag_hidden("final KV-keyed TAG not hidden");
    hmac_zeroize();
}

static void test_kv_key_restore_rejected(void) {
    VPRINTF(LOW, "--- KV key, RESTORE|NEXT rejected ---\n");
    hmac_wait_ready();
    load_kv_key();
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0, lfsr_seed_dwords, 6);
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_TAG_0, h1_fw, 16);
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, b2, 32);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_RESTORE_MASK | HMAC_REG_HMAC512_CTRL_NEXT_MASK, HMAC512_MODE, FALSE);
    expect_rejected("RESTORE|NEXT with KV key was not rejected");
    hmac_zeroize();
}

static void test_kv_key_next_without_init_rejected(void) {
    VPRINTF(LOW, "--- KV key, NEXT|LAST without INIT rejected ---\n");
    hmac_wait_ready();
    load_kv_key();
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0, lfsr_seed_dwords, 6);
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, b2f, 32);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_NEXT_MASK | HMAC_REG_HMAC512_CTRL_LAST_MASK, HMAC512_MODE, FALSE);
    expect_rejected("NEXT|LAST without INIT on KV key was not rejected");
    hmac_zeroize();
}

static void test_fw_key_mid_op_kv_load_refused(void) {
    VPRINTF(LOW, "--- FW key save path; mid-op KV key load refused ---\n");
    hmac_wait_ready();
    hmac_load_inputs(k_fw, b1, lfsr_seed_dwords);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_INIT_MASK, HMAC512_MODE, FALSE);
    hmac_wait_valid();
    expect_tag(h1_fw, "FW-keyed intermediate TAG != expected inner state");

    lsu_write_32(STDOUT, (KV_KEY_SLOT << 8) | 0xa9);
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL,
        HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
        ((KV_KEY_SLOT << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) &
         HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));
    for (int i = 0; i < 100; i++) __asm__ volatile ("nop");

    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, b2f, 32);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_NEXT_MASK | HMAC_REG_HMAC512_CTRL_LAST_MASK, HMAC512_MODE, FALSE);
    hmac_wait_valid();
    expect_tag(t_fw, "FW-keyed final TAG != HMAC-SHA512(K_FW, M)");
    hmac_zeroize();
}

static void test_csr_mode_locked_mid_op(void) {
    VPRINTF(LOW, "--- CSR key, CSR_MODE cleared mid-op ---\n");
    hmac_wait_ready();
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0, lfsr_seed_dwords, 6);
    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, b1, 32);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_INIT_MASK, HMAC512_MODE, TRUE);
    hmac_wait_valid();
    expect_tag_hidden("CSR-keyed intermediate TAG after INIT not hidden");

    write_hmac_reg((volatile uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0, b2, 32);
    hmac_ctrl_write(HMAC_REG_HMAC512_CTRL_NEXT_MASK, HMAC512_MODE, FALSE);
    hmac_wait_valid();
    expect_tag_hidden("CSR-keyed inner state leaked after CSR_MODE cleared");
    hmac_zeroize();
}

void main(void) {
    VPRINTF(LOW, "HMAC KV multi-block no-leak test\n");
    test_kv_key_no_intermediate_leak();
    test_kv_key_restore_rejected();
    test_kv_key_next_without_init_rejected();
    test_fw_key_mid_op_kv_load_refused();
    test_csr_mode_locked_mid_op();
    VPRINTF(LOW, "HMAC KV multi-block no-leak test PASSED\n");
    SEND_STDOUT_CTRL(0xff);
}
