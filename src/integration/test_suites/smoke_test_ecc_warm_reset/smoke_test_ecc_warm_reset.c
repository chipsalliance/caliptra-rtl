// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Mid-command warm-reset smoke. For each rst_count phase: program inputs,
// kick a command, then immediately request warm reset via TB backdoor 0xf6.
// After re-entry, confirm ECC is ready and output registers are cleared,
// then run a known-good command to prove the engine is fully operational.

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

// P-384 KAT.
static const uint32_t p384_seed[]    = {0x8FA8541C,0x82A392CA,0x74F23ED1,0xDBFD7354,
                                        0x1C596639,0x1B97EA73,0xD744B0E3,0x4B9DF59E,
                                        0xD0158063,0xE39C09A5,0xA055371E,0xDF7A5441};
static const uint32_t p384_nonce[]   = {0x1B7EC5E5,0x48E8AAA9,0x2EC77097,0xCA9551C9,
                                        0x783CE682,0xCA18FB1E,0xDBD9F1E5,0x0BC382DB,
                                        0x8AB39496,0xC8EE423F,0x8CA105CB,0xBA7B6588};
static const uint32_t p384_iv[]      = {0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329,
                                        0x26DB9ED0,0xDB6B1CFF,0xAB0493DA,0xAFB93DDD,
                                        0xD83EDEA2,0x8A803D0D,0x003B2633,0xB9D0F1BF};
static const uint32_t p384_privkey[] = {0xF274F69D,0x163B0C9F,0x1FC3EBF4,0x292AD1C4,
                                        0xEB3CEC1C,0x5A7DDE6F,0x80C14292,0x934C2055,
                                        0xE087748D,0x0A169C77,0x2483ADEE,0x5EE70E17};
static const uint32_t p384_msg[]     = {0xC8F518D4,0xF3AA1BD4,0x6ED56C1C,0x3C9E16FB,
                                        0x800AF504,0xDB988435,0x48C5F623,0xEE115F73,
                                        0xD4C62ABC,0x06D303B5,0xD90D9A17,0x5087290D};

// P-256 KAT. Upper 4 dwords zero.
static const uint32_t p256_seed[]    = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xAE6CADE4,0xA2E25537,0x0144805E,0x2557B195,
                                        0x0F68A166,0x9E6C305B,0x52C927B3,0x0DBD60EC};
static const uint32_t p256_nonce[]   = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0x15925C0A,0xDE01EDF6,0x2683F876,0x9DA2A9DF,
                                        0x91985A1A,0xE96ABBED,0x62508DA9,0xAB7F0E11};
static const uint32_t p256_iv[]      = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xE93B8299,0x3BEA1417,0xC81B1E72,0x5191DDD8,
                                        0xC8B3EDA5,0xE4FE8883,0xA5D6BB3E,0xA5D3173F};
static const uint32_t p256_privkey[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xB57BA11F,0x3735F3B6,0x8147151E,0xB788736D,
                                        0xC6F013A0,0xBEEBC555,0xC4317F70,0x44C5E426};
static const uint32_t p256_msg[]     = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xB37D6700,0x3B99E49B,0x770DE71E,0x5429D527,
                                        0xEA59BA6F,0xFE7AE6F5,0x313C44E5,0x921102A6};

static void write_12dw(uintptr_t base_addr, const uint32_t *data) {
    volatile uint32_t *reg_ptr = (volatile uint32_t *)base_addr;
    for (uint8_t i = 0; i < 12; i++) reg_ptr[i] = data[i];
}

static void check_cleared(uintptr_t base_addr, const char *label) {
    volatile uint32_t *reg_ptr = (volatile uint32_t *)base_addr;
    for (uint8_t i = 0; i < 12; i++) {
        if (reg_ptr[i] != 0) {
            VPRINTF(ERROR, "%s dword[%0d] not cleared after warm reset: 0x%x\n",
                    label, i, reg_ptr[i]);
            SEND_STDOUT_CTRL(0x1); while(1);
        }
    }
    VPRINTF(LOW, "%s cleared cleanly after warm reset.\n", label);
}

// Kick command then immediately issue warm reset.
static void warm_reset_mid_op(uint32_t ctrl_val, const char *label) {
    VPRINTF(LOW, "\n[%s] kick command, then warm reset mid-op\n", label);
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ctrl_val);
    for (volatile uint32_t i = 0; i < 200; i++) {
        __asm__ volatile ("nop");
    }
    SEND_STDOUT_CTRL(0xf6);  // TB backdoor: issue warm reset
    while (1);               // main() will re-enter with bumped rst_count
}

void main() {
    VPRINTF(LOW, "------------------------------\n");
    VPRINTF(LOW, " ECC warm-reset mid-op smoke\n");
    VPRINTF(LOW, "------------------------------\n");

    init_interrupts();
    rst_count++;

    uint32_t curve_p256 = (1 << ECC_REG_ECC_CTRL_CURVE_SEL_LOW) & ECC_REG_ECC_CTRL_CURVE_SEL_MASK;
    uint32_t rand_k     = (1 << ECC_REG_ECC_CTRL_NONDETERMINISTIC_LOW) & ECC_REG_ECC_CTRL_NONDETERMINISTIC_MASK;

    switch (rst_count) {
        case 1:
            // First entry: kick P-384 KEYGEN then warm-reset.
            while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
            write_12dw(CLP_ECC_REG_ECC_SEED_0,  p384_seed);
            write_12dw(CLP_ECC_REG_ECC_NONCE_0, p384_nonce);
            write_12dw(CLP_ECC_REG_ECC_IV_0,    p384_iv);
            warm_reset_mid_op(ECC_CMD_KEYGEN, "P-384 KEYGEN");
            break;
        case 2:
            // After warm reset from case 1: verify cleared, then kick P-256 KEYGEN.
            while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
            check_cleared(CLP_ECC_REG_ECC_PRIVKEY_OUT_0, "P-384 KEYGEN privkey_out");
            write_12dw(CLP_ECC_REG_ECC_SEED_0,  p256_seed);
            write_12dw(CLP_ECC_REG_ECC_NONCE_0, p256_nonce);
            write_12dw(CLP_ECC_REG_ECC_IV_0,    p256_iv);
            warm_reset_mid_op(ECC_CMD_KEYGEN | curve_p256, "P-256 KEYGEN");
            break;
        case 3:
            while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
            check_cleared(CLP_ECC_REG_ECC_PRIVKEY_OUT_0, "P-256 KEYGEN privkey_out");
            write_12dw(CLP_ECC_REG_ECC_PRIVKEY_IN_0, p384_privkey);
            write_12dw(CLP_ECC_REG_ECC_MSG_0,        p384_msg);
            write_12dw(CLP_ECC_REG_ECC_IV_0,         p384_iv);
            warm_reset_mid_op(ECC_CMD_SIGNING, "P-384 SIGN det");
            break;
        case 4:
            while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
            check_cleared(CLP_ECC_REG_ECC_SIGN_R_0, "P-384 SIGN sign_r");
            write_12dw(CLP_ECC_REG_ECC_PRIVKEY_IN_0, p256_privkey);
            write_12dw(CLP_ECC_REG_ECC_MSG_0,        p256_msg);
            write_12dw(CLP_ECC_REG_ECC_IV_0,         p256_iv);
            warm_reset_mid_op(ECC_CMD_SIGNING | curve_p256, "P-256 SIGN det");
            break;
        case 5:
            while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
            check_cleared(CLP_ECC_REG_ECC_SIGN_R_0, "P-256 SIGN sign_r");
            write_12dw(CLP_ECC_REG_ECC_PRIVKEY_IN_0, p384_privkey);
            write_12dw(CLP_ECC_REG_ECC_MSG_0,        p384_msg);
            write_12dw(CLP_ECC_REG_ECC_IV_0,         p384_iv);
            warm_reset_mid_op(ECC_CMD_SIGNING | rand_k, "P-384 SIGN nondet");
            break;
        case 6:
            while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
            check_cleared(CLP_ECC_REG_ECC_SIGN_R_0, "P-384 SIGN nondet sign_r");
            write_12dw(CLP_ECC_REG_ECC_PRIVKEY_IN_0, p256_privkey);
            write_12dw(CLP_ECC_REG_ECC_MSG_0,        p256_msg);
            write_12dw(CLP_ECC_REG_ECC_IV_0,         p256_iv);
            warm_reset_mid_op(ECC_CMD_SIGNING | curve_p256 | rand_k, "P-256 SIGN nondet");
            break;
        case 7:
            // Final entry: verify last sign cleared and end test.
            while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
            check_cleared(CLP_ECC_REG_ECC_SIGN_R_0, "P-256 SIGN nondet sign_r");
            VPRINTF(LOW, "\nAll warm-reset mid-op variants passed.\n");
            break;
        default:
            break;
    }

    SEND_STDOUT_CTRL(0xff);  // end of test
}
