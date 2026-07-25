// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// P-256 mirror of smoke_test_ecc_errortrigger1 (+ SIGN_S subtest from
// errortrigger3). Covers SIGN/VERIFY input/output range checks under CURVE_SEL=1.
// 256-bit values are packed MSW-first into dwords[4..11]; upper 4 dwords zero.

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

// P-256 KAT (matches smoke_test_ecc_keygen_p256 / sign_p256). Upper 4 dwords zero.
//   PRIVKEY  = B57BA11F3735F3B68147151EB788736DC6F013A0BEEBC555C4317F7044C5E426
//   PUBKEY_X = 2DF9017372533003F44A693DB9952A5EAA8898721BBE53E74473C7815FB739E9
//   PUBKEY_Y = 3A423A9FD9B0819984797AA4441327048FB38315C1911A1DB1E7E73BD9CC932A

void main() {
    VPRINTF(LOW, "----------------------------------------------\n");
    VPRINTF(LOW, " Running ECC P-256 SIGN/VERIFY error_trigger !!\n");
    VPRINTF(LOW, "----------------------------------------------\n");

    uint32_t ecc_msg[]      = {0x00000000,0x00000000,0x00000000,0x00000000,
                               0xB37D6700,0x3B99E49B,0x770DE71E,0x5429D527,
                               0xEA59BA6F,0xFE7AE6F5,0x313C44E5,0x921102A6};
    uint32_t ecc_privkey[]  = {0x00000000,0x00000000,0x00000000,0x00000000,
                               0xB57BA11F,0x3735F3B6,0x8147151E,0xB788736D,
                               0xC6F013A0,0xBEEBC555,0xC4317F70,0x44C5E426};
    uint32_t ecc_pubkey_x[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                               0x2DF90173,0x72533003,0xF44A693D,0xB9952A5E,
                               0xAA889872,0x1BBE53E7,0x4473C781,0x5FB739E9};
    uint32_t ecc_pubkey_y[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                               0x3A423A9F,0xD9B08199,0x84797AA4,0x44132704,
                               0x8FB38315,0xC1911A1D,0xB1E7E73B,0xD9CC932A};
    uint32_t ecc_sign_r[]   = {0x00000000,0x00000000,0x00000000,0x00000000,
                               0x30E59258,0x8D80798B,0xA426855A,0x06407035,
                               0xFD2C2CD0,0x3ADE2B2A,0xFA6592B5,0xFAC90FFE};
    uint32_t ecc_sign_s[]   = {0x00000000,0x00000000,0x00000000,0x00000000,
                               0x1C571D9D,0xCA33E72F,0x06F6E4A9,0xBECB7649,
                               0x495AF20B,0x8B67A1EC,0x2ACB5CEB,0x65900786};
    uint32_t ecc_iv[]       = {0x00000000,0x00000000,0x00000000,0x00000000,
                               0xE93B8299,0x3BEA1417,0xC81B1E72,0x5191DDD8,
                               0xC8B3EDA5,0xE4FE8883,0xA5D6BB3E,0xA5D3173F};

    // All-ones in dwords[4..11] is > p_256 and > n_256 (both have leading zero bits in upper bytes).
    uint32_t value_greater_p[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                                  0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,
                                  0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF};
    uint32_t value_greater_q[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                                  0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,
                                  0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF};

    init_interrupts();
    rst_count++;

    uint8_t offset;
    volatile uint32_t * reg_ptr;
    // CURVE_SEL=1 bit pattern for ECC_CTRL writes.
    uint32_t curve_p256 = (1 << ECC_REG_ECC_CTRL_CURVE_SEL_LOW) & ECC_REG_ECC_CTRL_CURVE_SEL_MASK;

    if (rst_count == 1) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n TEST P-256: OUT OF RANGE PRIVKEY ZERO\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_11) { *reg_ptr++ = 0; }

        VPRINTF(LOW, "\nECC SIGNING (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 privkey_input_outofrange 0 error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 2) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n TEST P-256: OUT OF RANGE PRIVKEY GREATER n\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_11) {
            *reg_ptr++ = value_greater_q[offset++];
        }

        VPRINTF(LOW, "\nECC SIGNING (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 privkey_input_outofrange 1 error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 3) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n TEST P-256: OUT OF RANGE PUBKEY\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_11) {
            *reg_ptr++ = value_greater_p[offset++];
        }
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_11) {
            *reg_ptr++ = value_greater_p[offset++];
        }

        VPRINTF(LOW, "\nECC VERIFYING (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_VERIFYING | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 pubkey_input_outofrange error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 4) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n TEST P-256: INVALID PUBKEY (off-curve via x<->y swap)\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_11) {
            *reg_ptr++ = ecc_pubkey_y[offset++];
        }
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_11) {
            *reg_ptr++ = ecc_pubkey_x[offset++];
        }
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_11) {
            *reg_ptr++ = ecc_sign_r[offset++];
        }
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_11) {
            *reg_ptr++ = ecc_sign_s[offset++];
        }

        VPRINTF(LOW, "\nECC VERIFYING (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_VERIFYING | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 pubkey_input_invalid error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 5) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n TEST P-256: INVALID OUTPUT SIGN_R (forced 0)\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_11) {
            *reg_ptr++ = ecc_privkey[offset++];
        }
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_MSG_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_MSG_11) {
            *reg_ptr++ = ecc_msg[offset++];
        }
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
            *reg_ptr++ = ecc_iv[offset++];
        }

        SEND_STDOUT_CTRL(0x98);  // TB backdoor: inject zero sign_r

        VPRINTF(LOW, "\nECC SIGNING (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 r_output_outofrange error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 6) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n TEST P-256: INVALID OUTPUT SIGN_S (forced 0)\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_11) {
            *reg_ptr++ = ecc_privkey[offset++];
        }
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_MSG_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_MSG_11) {
            *reg_ptr++ = ecc_msg[offset++];
        }
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
            *reg_ptr++ = ecc_iv[offset++];
        }

        SEND_STDOUT_CTRL(0x9a);  // TB backdoor: inject zero sign_s

        VPRINTF(LOW, "\nECC SIGNING (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 s_output_outofrange error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 7) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n TEST P-256: OUT OF RANGE INPUT R/S\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_11) {
            *reg_ptr++ = value_greater_q[offset++];
        }
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_11) {
            *reg_ptr++ = 0;
        }

        VPRINTF(LOW, "\nECC VERIFYING (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_VERIFYING | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 r/s_input_outofrange error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
    }

    SEND_STDOUT_CTRL(0xff);  // end of test
}
