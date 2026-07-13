// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// P-256 half of nondet errortrigger (SIGN-only error paths with NONDETERMINISTIC=1).
// 4 subtests across warm resets via persistent rst_count:
//   case 1: PRIVKEY=0           -> privkey_input_outofrange
//   case 2: PRIVKEY>n           -> privkey_input_outofrange
//   case 3: forced SIGN_R=0     -> r_output_outofrange
//   case 4: forced SIGN_S=0     -> s_output_outofrange
// KEYGEN/VERIFY/ECDH paths are skipped because nondeterministic_mode latches only
// on SIGN dispatch in RTL. Companion: smoke_test_ecc_errortrigger_nondet_p384.

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

// P-256 KAT (smoke_test_ecc_keygen_p256 vectors). Upper 4 dwords zero.
static const uint32_t p256_msg[]     = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xB37D6700,0x3B99E49B,0x770DE71E,0x5429D527,
                                        0xEA59BA6F,0xFE7AE6F5,0x313C44E5,0x921102A6};
static const uint32_t p256_privkey[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xB57BA11F,0x3735F3B6,0x8147151E,0xB788736D,
                                        0xC6F013A0,0xBEEBC555,0xC4317F70,0x44C5E426};
static const uint32_t p256_iv[]      = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xE93B8299,0x3BEA1417,0xC81B1E72,0x5191DDD8,
                                        0xC8B3EDA5,0xE4FE8883,0xA5D6BB3E,0xA5D3173F};
// All-ones in dwords[4..11] is > n_256 (which has leading zero bits in upper bytes).
static const uint32_t p256_greater_q[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                                          0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,
                                          0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF};
static const uint32_t zero_vec[]       = {0,0,0,0, 0,0,0,0, 0,0,0,0};

// Helper: bulk-write 12 dwords starting at base_addr.
static void write_12dw(uintptr_t base_addr, const uint32_t *data) {
    volatile uint32_t *reg_ptr = (volatile uint32_t *)base_addr;
    for (uint8_t i = 0; i < 12; i++) reg_ptr[i] = data[i];
}

// Helper: run a P-256 SIGN+NONDETERMINISTIC subtest with the given privkey, expect ecc_error.
static void run_p256_nondet_sign_err(const uint32_t *privkey, uint8_t inject_cmd,
                                     const char *label) {
    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    VPRINTF(LOW, "\n %s (CURVE_SEL=1, NONDETERMINISTIC=1)\n", label);
    write_12dw(CLP_ECC_REG_ECC_PRIVKEY_IN_0, privkey);
    write_12dw(CLP_ECC_REG_ECC_MSG_0,        p256_msg);
    write_12dw(CLP_ECC_REG_ECC_IV_0,         p256_iv);

    if (inject_cmd) {
        SEND_STDOUT_CTRL(inject_cmd);  // TB backdoor: 0x98=zero sign_r, 0x9a=zero sign_s
    }

    uint32_t ctrl = ECC_CMD_SIGNING |
                    ((1u << ECC_REG_ECC_CTRL_CURVE_SEL_LOW) & ECC_REG_ECC_CTRL_CURVE_SEL_MASK) |
                    ((1u << ECC_REG_ECC_CTRL_NONDETERMINISTIC_LOW) & ECC_REG_ECC_CTRL_NONDETERMINISTIC_MASK);
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ctrl);

    wait_for_ecc_intr();
    if (cptra_intr_rcv.ecc_error == 0) {
        VPRINTF(ERROR, "\n%s: ecc_error not asserted\n", label);
        SEND_STDOUT_CTRL(0x1); while(1);
    }
    ecc_zeroize();
}

void main() {
    VPRINTF(LOW, "----------------------------------------------------------\n");
    VPRINTF(LOW, " Running ECC P-256 nondet SIGN error_trigger smoke test !!\n");
    VPRINTF(LOW, "----------------------------------------------------------\n");

    init_interrupts();
    rst_count++;

    switch (rst_count) {
        case 1:
            run_p256_nondet_sign_err(zero_vec, 0,
                                     "P-256 NONDET: PRIVKEY=0");
            SEND_STDOUT_CTRL(0xf6);
            break;
        case 2:
            run_p256_nondet_sign_err(p256_greater_q, 0,
                                     "P-256 NONDET: PRIVKEY>n");
            SEND_STDOUT_CTRL(0xf6);
            break;
        case 3:
            run_p256_nondet_sign_err(p256_privkey, 0x98,
                                     "P-256 NONDET: forced SIGN_R=0");
            SEND_STDOUT_CTRL(0xf6);
            break;
        case 4:
            run_p256_nondet_sign_err(p256_privkey, 0x9a,
                                     "P-256 NONDET: forced SIGN_S=0");
            break;
        default:
            break;
    }

    SEND_STDOUT_CTRL(0xff);  // end of test
}
