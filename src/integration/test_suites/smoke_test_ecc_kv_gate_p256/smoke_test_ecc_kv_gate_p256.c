// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// KV-gate matrix test for kv_under_p256_invalid (CURVE_SEL=1).
// Covers every architecturally reachable OR-bit feeding the gate, organized
// as src (KV-read into ECC) vs dst (ECC writes into KV):
//
//   [1] src privkey: arm KV_RD_PKEY, dispatch SIGN+CURVE_SEL=1
//                    (RAND_K_EN randomized)
//         -> ecc_error via kv_privkey_read_ctrl.read_en + sticky
//            kv_key_data_present (handled inside ecc_signing_flow).
//   [2] src seed:    arm KV_RD_SEED standalone under CURVE_SEL=0, wait
//                    for KV read to land (sets kv_seed_data_present
//                    sticky), then dispatch SIGN under CURVE_SEL=1 with
//                    SW privkey
//         -> ecc_error via sticky kv_seed_data_present.
//   [3] dst swwe:    with CURVE_SEL=1, attempt SW arm of WRITE_EN; the
//                    existing swwe lockout drops the write
//         -> no ecc_error; readback bit==0.
//
// Each sub-case ends with ecc_zeroize to clear sticky state, error latch,
// and ECC_CTRL.CURVE_SEL.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "ecc.h"
#include "caliptra_rtl_lib.h"

volatile uint32_t* stdout         = (uint32_t *)STDOUT;
volatile uint32_t  intr_count     = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

static const uint32_t ecc_iv_p256[]  = {0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                        0xE93B8299, 0x3BEA1417, 0xC81B1E72, 0x5191DDD8,
                                        0xC8B3EDA5, 0xE4FE8883, 0xA5D6BB3E, 0xA5D3173F};
static const uint32_t ecc_msg_p256[] = {0x00000000, 0x00000000, 0x00000000, 0x00000000,
                                        0xB37D6700, 0x3B99E49B, 0x770DE71E, 0x5429D527,
                                        0xEA59BA6F, 0xFE7AE6F5, 0x313C44E5, 0x921102A6};

static void expect_ecc_error(const char *tag) {
    if (cptra_intr_rcv.ecc_error == 0) {
        VPRINTF(ERROR, "FAIL[%s]: ecc_error not asserted\n", tag);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
    VPRINTF(LOW, "PASS[%s]: ecc_error asserted\n", tag);
    cptra_intr_rcv.ecc_error = 0;
}

static void expect_no_ecc_error(const char *tag) {
    if (cptra_intr_rcv.ecc_error != 0) {
        VPRINTF(ERROR, "FAIL[%s]: unexpected ecc_error\n", tag);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
}

static void poll_ecc_ready(void) {
    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
}

static void load_io(ecc_io *io, const uint32_t *src) {
    io->kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++) io->data[i] = src[i];
}

void main() {
    VPRINTF(LOW, "--------------------------------------------------------\n");
    VPRINTF(LOW, " ECC KV-gate matrix test (CURVE_SEL=1, P-256)\n");
    VPRINTF(LOW, "--------------------------------------------------------\n");

    init_interrupts();

    ecc_io privkey, msg, iv, sign_r, sign_s;
    load_io(&msg, ecc_msg_p256);
    load_io(&iv,  ecc_iv_p256);
    sign_r.kv_intf = FALSE;
    sign_s.kv_intf = FALSE;

    const uint8_t kv_slot      = 0x3;
    const uint8_t kv_seed_slot = 0x4;

    // -----------------------------------------------------------------
    // [1] src privkey: SIGN + KV-privkey + CURVE_SEL=1 (RAND_K_EN randomized)
    // -----------------------------------------------------------------
    VPRINTF(LOW, "\n[1] src privkey: SIGN + KV-privkey + CURVE_SEL=1\n");
    lsu_write_32(STDOUT, (kv_slot << 8) | 0xad);
    privkey.kv_intf = TRUE;
    privkey.kv_id   = kv_slot;
    uint8_t rand_k_en_rand = (uint8_t)(xorshift32() & 0x1);
    VPRINTF(LOW, "    RAND_K_EN (randomized) = %0d\n", rand_k_en_rand);
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, FALSE, /*curve_sel=*/1, rand_k_en_rand);
    expect_ecc_error("1 src-privkey");
    ecc_zeroize();
    cptra_intr_rcv.ecc_notif = 0;

    // -----------------------------------------------------------------
    // [2] src seed sticky: arm KV_RD_SEED under CURVE_SEL=0 (swwe permits),
    // wait for KV read to land (kv_seed_data_present sticky=1), then
    // dispatch SIGN under CURVE_SEL=1 with SW privkey -> gate fires.
    // -----------------------------------------------------------------
    VPRINTF(LOW, "\n[2] src seed sticky: arm KV_RD_SEED then SIGN+CURVE_SEL=1\n");
    poll_ecc_ready();
    lsu_write_32(STDOUT, (kv_seed_slot << 8) | 0x80);
    lsu_write_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL,
                 ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK |
                 ((kv_seed_slot << ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW) &
                  ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_MASK));
    while ((lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_STATUS) &
            (ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_MASK |
             ECC_REG_ECC_KV_RD_SEED_STATUS_ERROR_MASK)) == 0);

    privkey.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++) privkey.data[i] = 0xDEADBEEF;
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, FALSE, /*curve_sel=*/1, /*rand_k_en=*/0);
    expect_ecc_error("2 src-seed-sticky");
    ecc_zeroize();
    cptra_intr_rcv.ecc_notif = 0;

    // -----------------------------------------------------------------
    // [3] dst swwe: with CURVE_SEL=1, arm of WRITE_EN must drop.
    // -----------------------------------------------------------------
    VPRINTF(LOW, "\n[3] dst swwe: arm WRITE_EN with CURVE_SEL=1\n");
    poll_ecc_ready();
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_REG_ECC_CTRL_CURVE_SEL_MASK);
    uint32_t wr_arm = ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                      ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK |
                      ((kv_slot << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) &
                       ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK);
    lsu_write_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, wr_arm);
    uint32_t wr_rd = lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL);
    if ((wr_rd & ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK) != 0) {
        VPRINTF(ERROR, "FAIL[3]: WRITE_EN swwe did not block under CURVE_SEL=1 (readback=0x%x)\n", wr_rd);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
    expect_no_ecc_error("3 dst-swwe");
    VPRINTF(LOW, "PASS[3]: WRITE_EN arm dropped (readback=0x%x), no ecc_error\n", wr_rd);
    ecc_zeroize();

    VPRINTF(LOW, "\n*** All KV-gate sub-cases passed (P-256) ***\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
