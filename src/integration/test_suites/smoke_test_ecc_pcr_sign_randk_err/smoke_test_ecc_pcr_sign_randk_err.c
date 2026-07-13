// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Negative test: PCR_SIGN and NONDETERMINISTIC illegal combos. Expect ecc_error for each.
//   Subtest 1: SIGN + P-384 + PCR_SIGN + NONDETERMINISTIC=1  -> nondet_pcr_sign_illegal
//   Subtest 2: SIGN + P-256 + PCR_SIGN + NONDETERMINISTIC=1  -> nondet_pcr_sign_illegal + pcr_sign_under_p256_invalid
//   Subtest 3: SIGN + P-256 + PCR_SIGN + NONDETERMINISTIC=0  -> pcr_sign_under_p256_invalid (P-256 det)
//   Subtest 4: KEYGEN     + NONDETERMINISTIC=1  -> nondet_invalid_cmd
//   Subtest 5: VERIFY     + NONDETERMINISTIC=1  -> nondet_invalid_cmd
//   Subtest 6: SHARED_KEY + NONDETERMINISTIC=1  -> nondet_invalid_cmd
// PCR_SIGN is architecturally P-384 deterministic SIGN only; NONDETERMINISTIC is architecturally SIGN only.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "ecc.h"

volatile uint32_t* stdout         = (uint32_t *)STDOUT;
volatile uint32_t  intr_count     = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// P-384 KAT IV (errortrigger2 vector).
static const uint32_t p384_iv[] = {0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329,
                                   0x26DB9ED0,0xDB6B1CFF,0xAB0493DA,0xAFB93DDD,
                                   0xD83EDEA2,0x8A803D0D,0x003B2633,0xB9D0F1BF};
// P-256 KAT IV (smoke_test_ecc_keygen_p256). Upper 4 dwords zero.
static const uint32_t p256_iv[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                                   0xE93B8299,0x3BEA1417,0xC81B1E72,0x5191DDD8,
                                   0xC8B3EDA5,0xE4FE8883,0xA5D6BB3E,0xA5D3173F};

// Helper: set up PCR-sign inputs (privkey in KV slot 7, MSG via SHA512 digest)
// and issue SIGN+PCR_SIGN with the given CURVE_SEL and NONDETERMINISTIC. Expect ecc_error.
static void run_pcr_sign_err(const uint32_t *iv, uint8_t curve_sel,
                             uint8_t nondet, const char *label) {
    volatile uint32_t *reg_ptr;

    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    VPRINTF(LOW, "\n %s\n", label);
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
    for (uint8_t i = 0; i < 12; i++) reg_ptr[i] = iv[i];

    VPRINTF(LOW, "Inject PRIVKEY into KV slot 7\n");
    SEND_STDOUT_CTRL(0x88 + 0x7);  // TB backdoor: load fixed PRIVKEY into KV slot 7
    VPRINTF(LOW, "Inject MSG into SHA512 digest\n");
    SEND_STDOUT_CTRL(0x90);        // TB backdoor: load fixed MSG into SHA512 digest path

    uint32_t ctrl = ECC_CMD_SIGNING |
                    ((1u << ECC_REG_ECC_CTRL_PCR_SIGN_LOW)  & ECC_REG_ECC_CTRL_PCR_SIGN_MASK)  |
                    ((nondet  << ECC_REG_ECC_CTRL_NONDETERMINISTIC_LOW) & ECC_REG_ECC_CTRL_NONDETERMINISTIC_MASK) |
                    ((curve_sel << ECC_REG_ECC_CTRL_CURVE_SEL_LOW) & ECC_REG_ECC_CTRL_CURVE_SEL_MASK);
    VPRINTF(LOW, "\nECC PCR SIGNING (CURVE_SEL=%0d, NONDETERMINISTIC=%0d)\n", curve_sel, nondet);
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ctrl);

    wait_for_ecc_intr();
    if (cptra_intr_rcv.ecc_error == 0) {
        VPRINTF(ERROR, "\n%s: ecc_error not asserted for illegal PCR_SIGN combo\n", label);
        SEND_STDOUT_CTRL(0x1); while(1);
    }
    VPRINTF(LOW, "PASS: %s\n", label);
    ecc_zeroize();
}

// Helper: issue non-SIGN command (KEYGEN/VERIFY/SHARED_KEY) with NONDETERMINISTIC=1.
// Expect ecc_error via nondet_invalid_cmd. No PCR/KV setup needed.
static void run_rand_k_nonsign_err(uint32_t cmd, const char *label) {
    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    VPRINTF(LOW, "\n %s\n", label);
    uint32_t ctrl = cmd | ((1u << ECC_REG_ECC_CTRL_NONDETERMINISTIC_LOW) &
                            ECC_REG_ECC_CTRL_NONDETERMINISTIC_MASK);
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ctrl);

    wait_for_ecc_intr();
    if (cptra_intr_rcv.ecc_error == 0) {
        VPRINTF(ERROR, "\n%s: ecc_error not asserted for NONDETERMINISTIC on non-SIGN\n", label);
        SEND_STDOUT_CTRL(0x1); while(1);
    }
    VPRINTF(LOW, "PASS: %s\n", label);
    ecc_zeroize();
}

void main() {
    VPRINTF(LOW, "----------------------------------------------------\n");
    VPRINTF(LOW, " ECC PCR_SIGN / NONDETERMINISTIC illegal-combo error test\n");
    VPRINTF(LOW, "----------------------------------------------------\n");

    init_interrupts();
    rst_count++;

    switch (rst_count) {
        case 1:
            run_pcr_sign_err(p384_iv, 0, 1,
                             "P-384 PCR_SIGN + NONDETERMINISTIC=1");
            SEND_STDOUT_CTRL(0xf6);
            break;
        case 2:
            run_pcr_sign_err(p256_iv, 1, 1,
                             "P-256 PCR_SIGN + NONDETERMINISTIC=1");
            SEND_STDOUT_CTRL(0xf6);
            break;
        case 3:
            run_pcr_sign_err(p256_iv, 1, 0,
                             "P-256 PCR_SIGN + NONDETERMINISTIC=0 (det)");
            SEND_STDOUT_CTRL(0xf6);
            break;
        case 4:
            run_rand_k_nonsign_err(ECC_CMD_KEYGEN,    "KEYGEN + NONDETERMINISTIC=1");
            SEND_STDOUT_CTRL(0xf6);
            break;
        case 5:
            run_rand_k_nonsign_err(ECC_CMD_VERIFYING, "VERIFY + NONDETERMINISTIC=1");
            SEND_STDOUT_CTRL(0xf6);
            break;
        case 6:
            run_rand_k_nonsign_err(ECC_CMD_SHAREDKEY, "SHARED_KEY + NONDETERMINISTIC=1");
            break;
        default:
            break;
    }

    SEND_STDOUT_CTRL(0xff);  // end of test
}
