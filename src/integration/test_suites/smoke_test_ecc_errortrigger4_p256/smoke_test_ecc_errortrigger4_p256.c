// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// P-256 mirror of smoke_test_ecc_errortrigger4. Covers ECDH (SHARED_KEY)
// input/output range checks under CURVE_SEL=1.
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

void main() {
    VPRINTF(LOW, "-----------------------------------------------\n");
    VPRINTF(LOW, " Running ECC P-256 ECDH error_trigger Smoke !!\n");
    VPRINTF(LOW, "-----------------------------------------------\n");

    // P-256 KAT pubkey (on-curve), same as smoke_test_ecc_keygen_p256.
    uint32_t ecc_pubkey_x[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                               0x2DF90173,0x72533003,0xF44A693D,0xB9952A5E,
                               0xAA889872,0x1BBE53E7,0x4473C781,0x5FB739E9};
    uint32_t ecc_pubkey_y[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                               0x3A423A9F,0xD9B08199,0x84797AA4,0x44132704,
                               0x8FB38315,0xC1911A1D,0xB1E7E73B,0xD9CC932A};
    uint32_t value_greater_p[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                                  0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,
                                  0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF};

    init_interrupts();
    rst_count++;

    uint8_t offset;
    volatile uint32_t * reg_ptr;
    uint32_t curve_p256 = (1 << ECC_REG_ECC_CTRL_CURVE_SEL_LOW) & ECC_REG_ECC_CTRL_CURVE_SEL_MASK;

    if (rst_count == 1) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n P-256 ECDH WITH OUT OF RANGE PUBKEY\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_11) {
            *reg_ptr++ = value_greater_p[offset++];
        }
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_11) {
            *reg_ptr++ = value_greater_p[offset++];
        }

        VPRINTF(LOW, "\nECDH (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SHAREDKEY | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 ECDH pubkey_input_outofrange error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 2) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n P-256 ECDH INVALID PUBKEY (off-curve via x<->y swap)\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_11) {
            *reg_ptr++ = ecc_pubkey_y[offset++];
        }
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_11) {
            *reg_ptr++ = ecc_pubkey_x[offset++];
        }

        VPRINTF(LOW, "\nECDH (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SHAREDKEY | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 ECDH pubkey_input_invalid error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 3) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n P-256 ECDH INVALID SHARED_KEY (forced out-of-range)\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_11) {
            *reg_ptr++ = ecc_pubkey_x[offset++];
        }
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_11) {
            *reg_ptr++ = ecc_pubkey_y[offset++];
        }

        VPRINTF(LOW, "Inject invalid shared_key\n");
        SEND_STDOUT_CTRL(0x97);  // TB backdoor: force DH_SHAREDKEY register write to all-ones

        VPRINTF(LOW, "\nECDH (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SHAREDKEY | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 ECDH sharedkey_outofrange error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
    }

    SEND_STDOUT_CTRL(0xff);  // end of test
}
