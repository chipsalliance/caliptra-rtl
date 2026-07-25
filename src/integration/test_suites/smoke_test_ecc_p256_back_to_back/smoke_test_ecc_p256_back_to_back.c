// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Back-to-back P-256 smoke: SIGN P-256 det -> SIGN P-256 det (same KAT),
// with the upper 4 dwords of every operand CSR deliberately polluted on the
// 2nd op. CURVE_SEL stays at 1 the whole test; no ecc_zeroize between ops.
// Targets the steady-state P-256 upper-128b scrub: a per-op scrub must fire
// every P-256 dispatch (not only the P-384->P-256 edge), otherwise the 2nd
// op's reducer feeds an unreduced hashed_msg/seed/nonce to the DRBG and the
// signature mismatches the KAT.

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

// P-256 KAT (same vectors as smoke_test_ecc_sign_p256). Upper 4 dwords zero
// in the "clean" image; the "polluted" image below replaces them with 0xDEADBEEF.
static const uint32_t p256_msg[]     = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xB37D6700,0x3B99E49B,0x770DE71E,0x5429D527,
                                        0xEA59BA6F,0xFE7AE6F5,0x313C44E5,0x921102A6};
static const uint32_t p256_privkey[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xB57BA11F,0x3735F3B6,0x8147151E,0xB788736D,
                                        0xC6F013A0,0xBEEBC555,0xC4317F70,0x44C5E426};
static const uint32_t p256_sign_r[]  = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0x30E59258,0x8D80798B,0xA426855A,0x06407035,
                                        0xFD2C2CD0,0x3ADE2B2A,0xFA6592B5,0xFAC90FFE};
static const uint32_t p256_sign_s[]  = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0x1C571D9D,0xCA33E72F,0x06F6E4A9,0xBECB7649,
                                        0x495AF20B,0x8B67A1EC,0x2ACB5CEB,0x65900786};
static const uint32_t p256_iv[]      = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xE93B8299,0x3BEA1417,0xC81B1E72,0x5191DDD8,
                                        0xC8B3EDA5,0xE4FE8883,0xA5D6BB3E,0xA5D3173F};

// Fill an ecc_io with register-sourced data. If pollute_upper is true, the
// upper 4 dwords (data[0..3], which map to ECC_*_0..3 == upper 128b of *_reg)
// are forced to 0xDEADBEEF to model SW-leftover state from a prior op.
static void make_io(ecc_io *io, const uint32_t *data, BOOL pollute_upper) {
    io->kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++) io->data[i] = data[i];
    if (pollute_upper) {
        for (int i = 0; i < 4; i++) io->data[i] = 0xDEADBEEFu;
    }
}

void main() {
    VPRINTF(LOW, "----------------------------------------------------\n");
    VPRINTF(LOW, " ECC back-to-back P-256 SIGN smoke test !!\n");
    VPRINTF(LOW, "----------------------------------------------------\n");

    init_interrupts();

    ecc_io iv, privkey, msg, sign_r, sign_s;

    // [1/2] SIGN P-256 det -- clean inputs, KAT-checked. Establishes good state
    // with CURVE_SEL latched to 1 on dispatch.
    VPRINTF(LOW, "\n[1/2] SIGN P-256 det (clean)\n");
    make_io(&privkey, p256_privkey, FALSE);
    make_io(&msg,     p256_msg,     FALSE);
    make_io(&iv,      p256_iv,      FALSE);
    make_io(&sign_r,  p256_sign_r,  FALSE);
    make_io(&sign_s,  p256_sign_s,  FALSE);
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, TRUE, 1, 0);
    cptra_intr_rcv.ecc_notif = 0;

    // [2/2] SIGN P-256 det -- same KAT message/key, but upper 4 dwords of every
    // operand CSR (PRIVKEY/MSG/IV) are 0xDEADBEEF. CURVE_SEL stays at 1; no
    // zeroize. With the per-op scrub fix, the upper 128b are cleared on
    // dispatch and the signature matches the KAT. Without the fix, the reducer
    // produces a non-mod-q hashed_msg and the engine raises ecc_error (and the
    // stale SIGN_R/S from op 1 would falsely match the KAT -- so we explicitly
    // check ecc_error here before declaring pass).
    VPRINTF(LOW, "\n[2/2] SIGN P-256 det (upper-128b polluted -- bug-exposing)\n");
    make_io(&privkey, p256_privkey, TRUE);
    make_io(&msg,     p256_msg,     TRUE);
    make_io(&iv,      p256_iv,      TRUE);
    make_io(&sign_r,  p256_sign_r,  FALSE);   // expected KAT, unchanged
    make_io(&sign_s,  p256_sign_s,  FALSE);
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, TRUE, 1, 0);
    if (cptra_intr_rcv.ecc_error) {
        VPRINTF(ERROR, "Op2 raised ecc_error -- per-op P-256 scrub missing.\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    cptra_intr_rcv.ecc_notif = 0;

    ecc_zeroize();
    SEND_STDOUT_CTRL(0xff);  // end of test
}
