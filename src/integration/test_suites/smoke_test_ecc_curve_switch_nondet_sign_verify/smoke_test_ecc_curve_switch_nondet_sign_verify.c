// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Curve-switch smoke (part 2 of 2): SIGN nondet + VERIFY.
// Sequence: SIGN P-384 nondet -> SIGN P-256 nondet -> VERIFY P-384 -> VERIFY P-256.
// 3 back-to-back CURVE_SEL transitions, no ecc_zeroize() in between.
// Nondet SIGNs check completion only (output randomized by NONDETERMINISTIC=1);
// VERIFY deterministic outputs are checked against KATs. Validates
// curve_sel_reg latching and no cross-curve datapath contamination for
// SIGN-nondet + VERIFY paths. Companion: smoke_test_ecc_curve_switch_keygen_det_sign.

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

// P-384 KAT.
static const uint32_t p384_msg[]     = {0xC8F518D4,0xF3AA1BD4,0x6ED56C1C,0x3C9E16FB,
                                        0x800AF504,0xDB988435,0x48C5F623,0xEE115F73,
                                        0xD4C62ABC,0x06D303B5,0xD90D9A17,0x5087290D};
static const uint32_t p384_privkey[] = {0xF274F69D,0x163B0C9F,0x1FC3EBF4,0x292AD1C4,
                                        0xEB3CEC1C,0x5A7DDE6F,0x80C14292,0x934C2055,
                                        0xE087748D,0x0A169C77,0x2483ADEE,0x5EE70E17};
static const uint32_t p384_pubkey_x[] = {0xD79C6D97,0x2B34A1DF,0xC916A7B6,0xE0A99B6B,
                                         0x5387B34D,0xA2187607,0xC1AD0A4D,0x1A8C2E41,
                                         0x72AB5FA5,0xD9AB58FE,0x45E43F56,0xBBB66BA4};
static const uint32_t p384_pubkey_y[] = {0x5A736393,0x2B06B4F2,0x23BEF0B6,0x0A639026,
                                         0x5112DBBD,0x0AAE67FE,0xF26B465B,0xE935B48E,
                                         0x451E68D1,0x6F1118F2,0xB32B4C28,0x608749ED};
static const uint32_t p384_sign_r[]  = {0x871E6EA4,0xDDC5432C,0xDDAA60FD,0x7F055472,
                                        0xD3C4DD41,0xA5BFB267,0x09E88C31,0x1A970935,
                                        0x99A7C8F5,0x5B3974C1,0x9E4F5A7B,0xFC1DD2AC};
static const uint32_t p384_sign_s[]  = {0x3E5552DE,0x6403350E,0xE70AD74E,0x4B854D2D,
                                        0xC4126BBF,0x9C153A5D,0x7A07BD4B,0x85D06E45,
                                        0xF850920E,0x898FB7D3,0x4F80796D,0xAE29365C};
static const uint32_t p384_iv[]      = {0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329,
                                        0x26DB9ED0,0xDB6B1CFF,0xAB0493DA,0xAFB93DDD,
                                        0xD83EDEA2,0x8A803D0D,0x003B2633,0xB9D0F1BF};

// P-256 KAT. Upper 4 dwords zero.
static const uint32_t p256_msg[]     = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xB37D6700,0x3B99E49B,0x770DE71E,0x5429D527,
                                        0xEA59BA6F,0xFE7AE6F5,0x313C44E5,0x921102A6};
static const uint32_t p256_privkey[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xB57BA11F,0x3735F3B6,0x8147151E,0xB788736D,
                                        0xC6F013A0,0xBEEBC555,0xC4317F70,0x44C5E426};
static const uint32_t p256_pubkey_x[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                                         0x2DF90173,0x72533003,0xF44A693D,0xB9952A5E,
                                         0xAA889872,0x1BBE53E7,0x4473C781,0x5FB739E9};
static const uint32_t p256_pubkey_y[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                                         0x3A423A9F,0xD9B08199,0x84797AA4,0x44132704,
                                         0x8FB38315,0xC1911A1D,0xB1E7E73B,0xD9CC932A};
static const uint32_t p256_sign_r[]  = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0x30E59258,0x8D80798B,0xA426855A,0x06407035,
                                        0xFD2C2CD0,0x3ADE2B2A,0xFA6592B5,0xFAC90FFE};
static const uint32_t p256_sign_s[]  = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0x1C571D9D,0xCA33E72F,0x06F6E4A9,0xBECB7649,
                                        0x495AF20B,0x8B67A1EC,0x2ACB5CEB,0x65900786};
static const uint32_t p256_iv[]      = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xE93B8299,0x3BEA1417,0xC81B1E72,0x5191DDD8,
                                        0xC8B3EDA5,0xE4FE8883,0xA5D6BB3E,0xA5D3173F};

static void make_io(ecc_io *io, const uint32_t *data) {
    io->kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++) io->data[i] = data[i];
}

void main() {
    VPRINTF(LOW, "----------------------------------------------------\n");
    VPRINTF(LOW, " ECC curve-switch (SIGN nondet + VERIFY) smoke test !!\n");
    VPRINTF(LOW, "----------------------------------------------------\n");

    init_interrupts();

    ecc_io iv, privkey, pubkey_x, pubkey_y, msg, sign_r, sign_s;

    // [1/4] SIGN P-384 nondet
    VPRINTF(LOW, "\n[1/4] SIGN P-384 nondet\n");
    make_io(&privkey, p384_privkey);
    make_io(&msg,     p384_msg);
    make_io(&iv,      p384_iv);
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, FALSE, 0, 1);
    cptra_intr_rcv.ecc_notif = 0;
    cptra_intr_rcv.ecc_error = 0;

    // [2/4] SIGN P-256 nondet (P-384 -> P-256 switch)
    VPRINTF(LOW, "\n[2/4] SIGN P-256 nondet\n");
    make_io(&privkey, p256_privkey);
    make_io(&msg,     p256_msg);
    make_io(&iv,      p256_iv);
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, FALSE, 1, 1);
    cptra_intr_rcv.ecc_notif = 0;
    cptra_intr_rcv.ecc_error = 0;

    // [3/4] VERIFY P-384 (P-256 -> P-384 back-switch)
    VPRINTF(LOW, "\n[3/4] VERIFY P-384\n");
    make_io(&msg,      p384_msg);
    make_io(&pubkey_x, p384_pubkey_x);
    make_io(&pubkey_y, p384_pubkey_y);
    make_io(&sign_r,   p384_sign_r);
    make_io(&sign_s,   p384_sign_s);
    ecc_verifying_flow(msg, pubkey_x, pubkey_y, sign_r, sign_s, 0);
    cptra_intr_rcv.ecc_notif = 0;
    cptra_intr_rcv.ecc_error = 0;

    // [4/4] VERIFY P-256 (P-384 -> P-256 switch)
    VPRINTF(LOW, "\n[4/4] VERIFY P-256\n");
    make_io(&msg,      p256_msg);
    make_io(&pubkey_x, p256_pubkey_x);
    make_io(&pubkey_y, p256_pubkey_y);
    make_io(&sign_r,   p256_sign_r);
    make_io(&sign_s,   p256_sign_s);
    ecc_verifying_flow(msg, pubkey_x, pubkey_y, sign_r, sign_s, 1);
    cptra_intr_rcv.ecc_notif = 0;
    cptra_intr_rcv.ecc_error = 0;

    ecc_zeroize();
    SEND_STDOUT_CTRL(0xff);  // end of test
}
