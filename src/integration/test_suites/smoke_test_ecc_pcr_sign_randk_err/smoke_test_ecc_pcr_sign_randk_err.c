// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Negative test: SIGN + PCR_SIGN + RAND_K_EN=1 illegal combo.
// Expect ecc_error from rand_k_pcr_sign_illegal (ecc_dsa_ctrl.sv:825).
// Covers P-384 nondet (subtest 1) and P-256 nondet (subtest 2 — also fires
// kv_under_p256_invalid since PCR_SIGN reads KV slot 7).

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
// and issue SIGN+PCR_SIGN+RAND_K_EN with the given CURVE_SEL. Expect ecc_error.
static void run_pcr_sign_randk_err(const uint32_t *iv, uint8_t curve_sel,
                                   const char *label) {
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
                    ((1u << ECC_REG_ECC_CTRL_RAND_K_EN_LOW) & ECC_REG_ECC_CTRL_RAND_K_EN_MASK) |
                    ((curve_sel << ECC_REG_ECC_CTRL_CURVE_SEL_LOW) & ECC_REG_ECC_CTRL_CURVE_SEL_MASK);
    VPRINTF(LOW, "\nECC PCR SIGNING + RAND_K_EN (CURVE_SEL=%0d)\n", curve_sel);
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ctrl);

    wait_for_ecc_intr();
    if (cptra_intr_rcv.ecc_error == 0) {
        VPRINTF(ERROR, "\n%s: ecc_error not asserted for PCR_SIGN+RAND_K_EN\n", label);
        SEND_STDOUT_CTRL(0x1); while(1);
    }
    VPRINTF(LOW, "PASS: %s\n", label);
    ecc_zeroize();
}

void main() {
    VPRINTF(LOW, "-------------------------------------------------\n");
    VPRINTF(LOW, " ECC PCR_SIGN + RAND_K_EN illegal-combo error test\n");
    VPRINTF(LOW, "-------------------------------------------------\n");

    init_interrupts();
    rst_count++;

    switch (rst_count) {
        case 1:
            run_pcr_sign_randk_err(p384_iv, 0,
                                   "P-384 PCR_SIGN + RAND_K_EN");
            SEND_STDOUT_CTRL(0xf6);
            break;
        case 2:
            run_pcr_sign_randk_err(p256_iv, 1,
                                   "P-256 PCR_SIGN + RAND_K_EN");
            break;
        default:
            break;
    }

    SEND_STDOUT_CTRL(0xff);  // end of test
}
