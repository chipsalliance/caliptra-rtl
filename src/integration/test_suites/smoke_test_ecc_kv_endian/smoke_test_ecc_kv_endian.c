// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// ECC P-384 KV endianness smoke (via deterministic SIGN).
//
// ECC is big-endian and KV mapping is word-order sensitive. End-to-end KV
// endianness on the ECDH path is already exercised by smoke_test_kv_ecdh_flow
// (KV-sourced privkey -> KV sharedkey -> HMAC -> AES with golden checks),
// but that test compares the FINAL AES ciphertext, not the intermediate KV
// data path in isolation.
//
// This test isolates the KV-read endianness for ECC PRIVKEY using deterministic
// SIGN: SIGN_R/S writes are NOT gated by kv_key_data_present (ecc_dsa_ctrl.sv
// lines 521/529), so a signature produced from a KV-sourced privkey is SW-
// readable. With identical {privkey, msg, iv} and RAND_K_EN=0, the (R,S) pair
// is deterministic. We compute SIGN twice:
//   Run 1: register-sourced privkey  -> signature_sw (also verified vs KAT)
//   Run 2: KV-sourced privkey  (via TB 0xad)  -> signature_kv
// signature_sw MUST equal signature_kv. A byte/word mismatch on the KV read
// path would produce a different signature.
//
// The TB 0xad backdoor loads the P-384 KAT privkey
//   F274F69D163B0C9F1FC3EBF4292AD1C4EB3CEC1C5A7DDE6F80C14292934C2055
//   E087748D0A169C772483ADEE5EE70E17
// into the requested KV slot (see ecc_privkey_tb in caliptra_top_tb_services.sv).

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

// ECC P-384 KAT privkey -- must match ecc_privkey_tb in caliptra_top_tb_services.sv.
static const uint32_t ecc_privkey[] = {0xF274F69D,0x163B0C9F,0x1FC3EBF4,0x292AD1C4,
                                       0xEB3CEC1C,0x5A7DDE6F,0x80C14292,0x934C2055,
                                       0xE087748D,0x0A169C77,0x2483ADEE,0x5EE70E17};
// Message + IV from the standard P-384 KAT (smoke_test_ecc_sign).
static const uint32_t ecc_msg[] = {0xC8F518D4,0xF3AA1BD4,0x6ED56C1C,0x3C9E16FB,
                                   0x800AF504,0xDB988435,0x48C5F623,0xEE115F73,
                                   0xD4C62ABC,0x06D303B5,0xD90D9A17,0x5087290D};
static const uint32_t ecc_iv[]  = {0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329,
                                   0x26DB9ED0,0xDB6B1CFF,0xAB0493DA,0xAFB93DDD,
                                   0xD83EDEA2,0x8A803D0D,0x003B2633,0xB9D0F1BF};
// Golden deterministic SIGN_R/S for the (privkey, msg, iv) triple above.
static const uint32_t ecc_sign_r_golden[] = {0x871E6EA4,0xDDC5432C,0xDDAA60FD,0x7F055472,
                                             0xD3C4DD41,0xA5BFB267,0x09E88C31,0x1A970935,
                                             0x99A7C8F5,0x5B3974C1,0x9E4F5A7B,0xFC1DD2AC};
static const uint32_t ecc_sign_s_golden[] = {0x3E5552DE,0x6403350E,0xE70AD74E,0x4B854D2D,
                                             0xC4126BBF,0x9C153A5D,0x7A07BD4B,0x85D06E45,
                                             0xF850920E,0x898FB7D3,0x4F80796D,0xAE29365C};

static void make_io(ecc_io *io, const uint32_t *data) {
    io->kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++) io->data[i] = data[i];
}

// Capture SIGN_R/S register contents into out[0..11]=R, out[12..23]=S.
static void read_sign_rs(uint32_t *out) {
    volatile uint32_t *r_ptr = (volatile uint32_t *) CLP_ECC_REG_ECC_SIGN_R_0;
    volatile uint32_t *s_ptr = (volatile uint32_t *) CLP_ECC_REG_ECC_SIGN_S_0;
    for (uint8_t i = 0; i < 12; i++) out[i]    = r_ptr[i];
    for (uint8_t i = 0; i < 12; i++) out[12+i] = s_ptr[i];
}

void main() {
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " ECC P-384 KV endianness smoke\n");
    VPRINTF(LOW, "----------------------------------\n");

    init_interrupts();

    ecc_io privkey, msg, iv, sign_r, sign_s;
    uint32_t sig_sw[24];
    uint32_t sig_kv[24];

    // ---- Run 1: register-sourced privkey, deterministic SIGN ----
    // ecc_signing_flow checks SIGN_R/S against sign_r.data/sign_s.data when
    // check_result=TRUE; this also acts as a KAT sanity check.
    VPRINTF(LOW, "\n[1/2] SIGN with register-sourced privkey, verify vs KAT\n");
    make_io(&privkey, ecc_privkey);
    make_io(&msg,     ecc_msg);
    make_io(&iv,      ecc_iv);
    make_io(&sign_r,  ecc_sign_r_golden);
    make_io(&sign_s,  ecc_sign_s_golden);
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, TRUE, 0, 0);
    cptra_intr_rcv.ecc_notif = 0;
    read_sign_rs(sig_sw);
    ecc_zeroize();

    // ---- Run 2: KV-sourced privkey (same value, via TB 0xad backdoor) ----
    VPRINTF(LOW, "\n[2/2] SIGN with KV-sourced privkey (slot 3)\n");
    uint8_t privkey_kv_id = 0x3;
    lsu_write_32(STDOUT, (privkey_kv_id << 8) | 0xad);  // TB inject ecc_privkey_tb into KV slot

    privkey.kv_intf = TRUE;
    privkey.kv_id   = privkey_kv_id;
    make_io(&msg, ecc_msg);
    make_io(&iv,  ecc_iv);
    // check_result=FALSE: KV-sourced sign should still be deterministic, but the
    // lib's sign_r.data fields aren't pre-populated for the KV path. We compare
    // manually below against sig_sw to catch any KV-read endian mismatch.
    sign_r.kv_intf = FALSE;
    sign_s.kv_intf = FALSE;
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, FALSE, 0, 0);
    cptra_intr_rcv.ecc_notif = 0;
    read_sign_rs(sig_kv);
    ecc_zeroize();

    // ---- Compare ----
    VPRINTF(LOW, "\nComparing deterministic SIGN results (SW-priv vs KV-priv)\n");
    for (int i = 0; i < 24; i++) {
        if (sig_sw[i] != sig_kv[i]) {
            const char *fld = (i < 12) ? "SIGN_R" : "SIGN_S";
            VPRINTF(ERROR, "MISMATCH at %s dword[%0d]: SW=0x%x KV=0x%x\n",
                    fld, (i % 12), sig_sw[i], sig_kv[i]);
            SEND_STDOUT_CTRL(0x1); while(1);
        }
    }
    VPRINTF(LOW, "\nPASS: KV-sourced privkey produces identical signature -- KV read endianness correct.\n");

    SEND_STDOUT_CTRL(0xff);
}
