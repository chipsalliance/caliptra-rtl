// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// P-256 mirror of smoke_test_ecc_errortrigger5. Covers KEYGEN-output
// out-of-range checks under CURVE_SEL=1 via TB backdoor forces.
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
    VPRINTF(LOW, "------------------------------------------------\n");
    VPRINTF(LOW, " Running ECC P-256 KEYGEN error_trigger Smoke !!\n");
    VPRINTF(LOW, "------------------------------------------------\n");

    // P-256 KAT IV (same as smoke_test_ecc_keygen_p256).
    uint32_t ecc_iv[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                         0xE93B8299,0x3BEA1417,0xC81B1E72,0x5191DDD8,
                         0xC8B3EDA5,0xE4FE8883,0xA5D6BB3E,0xA5D3173F};

    init_interrupts();
    rst_count++;

    uint8_t offset;
    volatile uint32_t * reg_ptr;
    uint32_t curve_p256 = (1 << ECC_REG_ECC_CTRL_CURVE_SEL_LOW) & ECC_REG_ECC_CTRL_CURVE_SEL_MASK;

    if (rst_count == 1) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n TEST P-256: invalid privkey injection\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
            *reg_ptr++ = ecc_iv[offset++];
        }

        SEND_STDOUT_CTRL(0x9c);  // TB backdoor: force PRIVKEY register write to all-ones

        VPRINTF(LOW, "\nECC KEYGEN (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_KEYGEN | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 invalid privkey error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 2) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n TEST P-256: invalid pubkey_x injection\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
            *reg_ptr++ = ecc_iv[offset++];
        }

        SEND_STDOUT_CTRL(0x9d);  // TB backdoor: force PUBKEY_X register write to all-ones

        VPRINTF(LOW, "\nECC KEYGEN (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_KEYGEN | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 invalid pubkey_x error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 3) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n TEST P-256: invalid pubkey_y injection\n");
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0; offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
            *reg_ptr++ = ecc_iv[offset++];
        }

        SEND_STDOUT_CTRL(0x9e);  // TB backdoor: force PUBKEY_Y register write to all-ones

        VPRINTF(LOW, "\nECC KEYGEN (P-256)\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_KEYGEN | curve_p256);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nP-256 invalid pubkey_y error not detected.\n");
            SEND_STDOUT_CTRL(0x1); while(1);
        }

        ecc_zeroize();
    }

    SEND_STDOUT_CTRL(0xff);  // end of test
}
