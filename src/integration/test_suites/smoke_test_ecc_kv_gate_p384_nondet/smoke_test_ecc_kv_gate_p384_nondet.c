// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// KV-gate matrix test for kv_under_nondet_invalid (P-384 + NONDETERMINISTIC=1).
// Covers every architecturally reachable OR-bit feeding the gate, organized
// as src (KV-read into ECC) vs dst (ECC writes into KV):
//
//   [1] src privkey: arm KV_RD_PKEY, dispatch SIGN+NONDETERMINISTIC
//         -> ecc_error via kv_privkey_read_ctrl.read_en + sticky
//            kv_key_data_present (handled inside ecc_signing_flow).
//   [2] src seed:    arm KV_RD_SEED standalone, wait for KV read to land
//                    (sets kv_seed_data_present sticky), dispatch SIGN+
//                    NONDETERMINISTIC with SW privkey
//         -> ecc_error via sticky kv_seed_data_present.
//   [3] dst swwe:    with NONDETERMINISTIC=1, attempt SW arm of WRITE_EN; the
//                    new swwe lockout drops the write
//         -> no ecc_error; readback bit==0.
//
// Notes on unreachable OR-bits (not tested here):
//   - nondet_mode only latches in the SIGN branch (ecc_dsa_ctrl.sv:969),
//     so KEYGEN/VERIFY/ECDH paths are intercepted by nondet_invalid_cmd
//     (a different gate, tested elsewhere).
//   - dest_keyvault and kv_write_ctrl.write_en cannot reach the gate
//     because: SIGN never writes to KV, and the swwe lockout blocks SW
//     from staging write_en before any SIGN dispatch.
//
// Each sub-case ends with ecc_zeroize to clear sticky state, the error
// latch, and ECC_CTRL.NONDETERMINISTIC.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "ecc.h"

volatile uint32_t* stdout         = (uint32_t *)STDOUT;
volatile uint32_t  intr_count     = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

static const uint32_t ecc_iv_p384[]  = {0x3401CEFA, 0xE20A7376, 0x49073AC1, 0xA351E329,
                                        0x26DB9ED0, 0xDB6B1CFF, 0xAB0493DA, 0xAFB93DDD,
                                        0xD83EDEA2, 0x8A803D0D, 0x003B2633, 0xB9D0F1BF};
static const uint32_t ecc_msg_p384[] = {0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C, 0x3C9E16FB,
                                        0x800AF504, 0xDB988435, 0x48C5F623, 0xEE115F73,
                                        0xD4C62ABC, 0x06D303B5, 0xD90D9A17, 0x5087290D};

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
    VPRINTF(LOW, " ECC KV-gate matrix test (P-384 + NONDETERMINISTIC=1)\n");
    VPRINTF(LOW, "--------------------------------------------------------\n");

    init_interrupts();

    ecc_io privkey, msg, iv, sign_r, sign_s;
    load_io(&msg, ecc_msg_p384);
    load_io(&iv,  ecc_iv_p384);
    sign_r.kv_intf = FALSE;
    sign_s.kv_intf = FALSE;

    const uint8_t kv_slot      = 0x3;
    const uint8_t kv_seed_slot = 0x4;

    // -----------------------------------------------------------------
    // [1] src privkey: SIGN + KV-sourced privkey + NONDETERMINISTIC=1
    // -----------------------------------------------------------------
    VPRINTF(LOW, "\n[1] src privkey: SIGN + KV-privkey + NONDETERMINISTIC=1\n");
    lsu_write_32(STDOUT, (kv_slot << 8) | 0xad);
    privkey.kv_intf = TRUE;
    privkey.kv_id   = kv_slot;
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, FALSE, /*curve_sel=*/0, /*nondet=*/1);
    expect_ecc_error("1 src-privkey");
    ecc_zeroize();
    cptra_intr_rcv.ecc_notif = 0;

    // -----------------------------------------------------------------
    // [2] src seed: arm KV_RD_SEED standalone, wait for KV read to land
    // so kv_seed_data_present is sticky=1, then dispatch SIGN+NONDETERMINISTIC
    // with SW-sourced privkey -> gate fires from sticky bit.
    // -----------------------------------------------------------------
    VPRINTF(LOW, "\n[2] src seed sticky: arm KV_RD_SEED then SIGN+NONDETERMINISTIC\n");
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
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, FALSE, /*curve_sel=*/0, /*nondet=*/1);
    expect_ecc_error("2 src-seed-sticky");
    ecc_zeroize();
    cptra_intr_rcv.ecc_notif = 0;

    // -----------------------------------------------------------------
    // [3] dst swwe: with NONDETERMINISTIC=1 sticky, SW arm of WRITE_EN must drop.
    // -----------------------------------------------------------------
    VPRINTF(LOW, "\n[3] dst swwe: arm WRITE_EN with NONDETERMINISTIC=1\n");
    poll_ecc_ready();
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_REG_ECC_CTRL_NONDETERMINISTIC_MASK);
    uint32_t wr_arm = ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                      ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK |
                      ((kv_slot << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) &
                       ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK);
    lsu_write_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, wr_arm);
    uint32_t wr_rd = lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL);
    if ((wr_rd & ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK) != 0) {
        VPRINTF(ERROR, "FAIL[3]: WRITE_EN swwe did not block under NONDETERMINISTIC=1 (readback=0x%x)\n", wr_rd);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }
    expect_no_ecc_error("3 dst-swwe");
    VPRINTF(LOW, "PASS[3]: WRITE_EN arm dropped (readback=0x%x), no ecc_error\n", wr_rd);
    ecc_zeroize();

    VPRINTF(LOW, "\n*** All KV-gate sub-cases passed (P-384 nondet) ***\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
