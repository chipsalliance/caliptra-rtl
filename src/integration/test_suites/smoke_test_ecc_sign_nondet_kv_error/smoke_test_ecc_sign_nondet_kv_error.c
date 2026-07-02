// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Negative test: arm KV privkey-read together with SIGN+RAND_K_EN=1.
// The HW gate (kv_under_rand_k_invalid) must fire ecc_error.

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

void main() {
    VPRINTF(LOW, "-------------------------------------------------\n");
    VPRINTF(LOW, " ECC KV + RAND_K_EN illegal-combo error test\n");
    VPRINTF(LOW, "-------------------------------------------------\n");

    ecc_io privkey, msg, iv, sign_r, sign_s;

    uint32_t ecc_iv[]      = {0x3401CEFA, 0xE20A7376, 0x49073AC1, 0xA351E329,
                              0x26DB9ED0, 0xDB6B1CFF, 0xAB0493DA, 0xAFB93DDD,
                              0xD83EDEA2, 0x8A803D0D, 0x003B2633, 0xB9D0F1BF};
    uint32_t ecc_msg[]     = {0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C, 0x3C9E16FB,
                              0x800AF504, 0xDB988435, 0x48C5F623, 0xEE115F73,
                              0xD4C62ABC, 0x06D303B5, 0xD90D9A17, 0x5087290D};

    init_interrupts();

    // Use KV-sourced privkey (kv_intf=TRUE) so ecc_signing_flow arms KV read,
    // then issues SIGN with RAND_K_EN=1. HW must reject the combo.
    privkey.kv_intf = TRUE;
    privkey.kv_id   = 0x3;
    msg.kv_intf     = FALSE;
    iv.kv_intf      = FALSE;
    sign_r.kv_intf  = FALSE;
    sign_s.kv_intf  = FALSE;

    for (int i = 0; i < ECC_INPUT_SIZE; i++) {
        msg.data[i] = ecc_msg[i];
        iv.data[i]  = ecc_iv[i];
    }

    // Inject a valid privkey into KV slot privkey_kv_id (TB STDOUT magic 0xad)
    VPRINTF(LOW, "Inject PRIVKEY into KV slot %0d\n", privkey.kv_id);
    lsu_write_32(STDOUT, (privkey.kv_id << 8) | 0xad);

    // SIGN with KV-sourced privkey + RAND_K_EN=1 (P-384). check_result=FALSE
    // since the engine must error out before producing a signature.
    uint8_t curve_sel = 0;
    uint8_t rand_k_en = 1;
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, FALSE, curve_sel, rand_k_en);

    if (cptra_intr_rcv.ecc_error == 0) {
        VPRINTF(ERROR, "FAIL: ecc_err intr not asserted for KV + RAND_K_EN combo\n");
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    VPRINTF(LOW, "PASS: ecc_err intr correctly asserted for KV + RAND_K_EN combo\n");
    ecc_zeroize();
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
