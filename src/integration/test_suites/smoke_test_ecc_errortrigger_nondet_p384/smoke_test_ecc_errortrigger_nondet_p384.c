// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// P-384 half of nondet errortrigger (SIGN-only error paths with NONDETERMINISTIC=1).
// 4 subtests across warm resets via persistent rst_count:
//   case 1: PRIVKEY=0           -> privkey_input_outofrange
//   case 2: PRIVKEY>n           -> privkey_input_outofrange
//   case 3: forced SIGN_R=0     -> r_output_outofrange
//   case 4: forced SIGN_S=0     -> s_output_outofrange
// KEYGEN/VERIFY/ECDH paths are skipped because nondeterministic_mode latches only
// on SIGN dispatch in RTL. Companion: smoke_test_ecc_errortrigger_nondet_p256.

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

// P-384 KAT (errortrigger1 vectors).
static const uint32_t p384_msg[]     = {0xC8F518D4,0xF3AA1BD4,0x6ED56C1C,0x3C9E16FB,
                                        0x800AF504,0xDB988435,0x48C5F623,0xEE115F73,
                                        0xD4C62ABC,0x06D303B5,0xD90D9A17,0x5087290D};
static const uint32_t p384_privkey[] = {0xF274F69D,0x163B0C9F,0x1FC3EBF4,0x292AD1C4,
                                        0xEB3CEC1C,0x5A7DDE6F,0x80C14292,0x934C2055,
                                        0xE087748D,0x0A169C77,0x2483ADEE,0x5EE70E17};
static const uint32_t p384_iv[]      = {0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329,
                                        0x26DB9ED0,0xDB6B1CFF,0xAB0493DA,0xAFB93DDD,
                                        0xD83EDEA2,0x8A803D0D,0x003B2633,0xB9D0F1BF};
static const uint32_t p384_greater_q[] = {0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,
                                          0xFFFFFFFF,0xFFFFFFFF,0xC7634D81,0xF4372DDF,
                                          0x5B1A0DB2,0x48B0A77A,0xECEC196A,0xCCC52973};
static const uint32_t zero_vec[]       = {0,0,0,0, 0,0,0,0, 0,0,0,0};

// Helper: bulk-write 12 dwords starting at base_addr.
static void write_12dw(uintptr_t base_addr, const uint32_t *data) {
    volatile uint32_t *reg_ptr = (volatile uint32_t *)base_addr;
    for (uint8_t i = 0; i < 12; i++) reg_ptr[i] = data[i];
}

// Helper: run a P-384 SIGN+NONDETERMINISTIC subtest with the given privkey, expect ecc_error.
static void run_p384_nondet_sign_err(const uint32_t *privkey, uint8_t inject_cmd,
                                     const char *label) {
    while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    VPRINTF(LOW, "\n %s (CURVE_SEL=0, NONDETERMINISTIC=1)\n", label);
    write_12dw(CLP_ECC_REG_ECC_PRIVKEY_IN_0, privkey);
    write_12dw(CLP_ECC_REG_ECC_MSG_0,        p384_msg);
    write_12dw(CLP_ECC_REG_ECC_IV_0,         p384_iv);

    if (inject_cmd) {
        SEND_STDOUT_CTRL(inject_cmd);  // TB backdoor: 0x98=zero sign_r, 0x9a=zero sign_s
    }

    uint32_t ctrl = ECC_CMD_SIGNING |
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
    VPRINTF(LOW, " Running ECC P-384 nondet SIGN error_trigger smoke test !!\n");
    VPRINTF(LOW, "----------------------------------------------------------\n");

    init_interrupts();
    rst_count++;

    switch (rst_count) {
        case 1:
            run_p384_nondet_sign_err(zero_vec, 0,
                                     "P-384 NONDET: PRIVKEY=0");
            SEND_STDOUT_CTRL(0xf6);
            break;
        case 2:
            run_p384_nondet_sign_err(p384_greater_q, 0,
                                     "P-384 NONDET: PRIVKEY>n");
            SEND_STDOUT_CTRL(0xf6);
            break;
        case 3:
            run_p384_nondet_sign_err(p384_privkey, 0x98,
                                     "P-384 NONDET: forced SIGN_R=0");
            SEND_STDOUT_CTRL(0xf6);
            break;
        case 4:
            run_p384_nondet_sign_err(p384_privkey, 0x9a,
                                     "P-384 NONDET: forced SIGN_S=0");
            break;
        default:
            break;
    }

    SEND_STDOUT_CTRL(0xff);  // end of test
}
