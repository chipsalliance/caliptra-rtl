// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Negative test: arm KV privkey-read together with SIGN under CURVE_SEL=P256.
// The HW gate (kv_under_p256_invalid in ecc_dsa_ctrl.sv) must fire ecc_error
// regardless of NONDETERMINISTIC, so nondet is randomized between 0 (det) and 1 (nondet).

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

void main() {
    VPRINTF(LOW, "-------------------------------------------------\n");
    VPRINTF(LOW, " ECC KV + P-256 illegal-combo error test\n");
    VPRINTF(LOW, "-------------------------------------------------\n");

    ecc_io privkey, msg, iv, sign_r, sign_s;

    // P-256 message/IV: active 256-bit values in dwords [4..11], upper 4 dwords zero.
    uint32_t ecc_iv[]  = {0x00000000, 0x00000000, 0x00000000, 0x00000000,
                          0xE93B8299, 0x3BEA1417, 0xC81B1E72, 0x5191DDD8,
                          0xC8B3EDA5, 0xE4FE8883, 0xA5D6BB3E, 0xA5D3173F};
    uint32_t ecc_msg[] = {0x00000000, 0x00000000, 0x00000000, 0x00000000,
                          0xB37D6700, 0x3B99E49B, 0x770DE71E, 0x5429D527,
                          0xEA59BA6F, 0xFE7AE6F5, 0x313C44E5, 0x921102A6};

    init_interrupts();

    // Use KV-sourced privkey (kv_intf=TRUE) so ecc_signing_flow arms KV read,
    // then issues SIGN with CURVE_SEL=1. HW must reject the combo.
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

    // Randomize NONDETERMINISTIC to cover both det and nondet P-256 KV-gate paths.
    // check_result=FALSE since the engine must error out before producing a signature.
    uint8_t curve_sel = 1;
    uint8_t nondet = (uint8_t)(xorshift32() & 0x1);
    VPRINTF(LOW, "Selected NONDETERMINISTIC = %0d\n", nondet);
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s, FALSE, curve_sel, nondet);

    if (cptra_intr_rcv.ecc_error == 0) {
        VPRINTF(ERROR, "FAIL: ecc_err intr not asserted for KV + P-256 combo\n");
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    VPRINTF(LOW, "PASS: ecc_err intr correctly asserted for KV + P-256 combo\n");
    ecc_zeroize();
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
