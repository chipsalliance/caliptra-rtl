// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// smoke_test_ecc_errortrigger6:
//   Exercises the (read_reg >= group_order) branch of r_output_outofrange and
//   s_output_outofrange in ecc_dsa_ctrl. Existing errortrigger2/3 force these
//   outputs to zero (hitting the read_reg == 0 branch). This test forces them
//   to all-ones (>= group_order for both P-256 and P-384) to cover the other
//   half of the compare.
//
//   Phase 0 (rst_count==0): SIGN, force sign_r to all-ones via TB backdoor 0xa2
//   Phase 1 (rst_count==1): SIGN, force sign_s to all-ones via TB backdoor 0xa3

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "ecc.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Reuse the shared P-384 KAT (mirrors smoke_test_ecc_errortrigger3).
static const uint32_t ecc_msg[]      = {0xC8F518D4,0xF3AA1BD4,0x6ED56C1C,0x3C9E16FB,
                                        0x800AF504,0xDB988435,0x48C5F623,0xEE115F73,
                                        0xD4C62ABC,0x06D303B5,0xD90D9A17,0x5087290D};
static const uint32_t ecc_privkey[]  = {0xF274F69D,0x163B0C9F,0x1FC3EBF4,0x292AD1C4,
                                        0xEB3CEC1C,0x5A7DDE6F,0x80C14292,0x934C2055,
                                        0xE087748D,0x0A169C77,0x2483ADEE,0x5EE70E17};
static const uint32_t ecc_iv[]       = {0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329,
                                        0x26DB9ED0,0xDB6B1CFF,0xAB0493DA,0xAFB93DDD,
                                        0xD83EDEA2,0x8A803D0D,0x003B2633,0xB9D0F1BF};

static void program_sign_inputs() {
    volatile uint32_t *reg_ptr;
    uint8_t offset;

    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_11) *reg_ptr++ = ecc_privkey[offset++];

    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_MSG_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_MSG_11) *reg_ptr++ = ecc_msg[offset++];

    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) *reg_ptr++ = ecc_iv[offset++];
}

void main() {
    VPRINTF(LOW, "----------------------------------------\n");
    VPRINTF(LOW, " Running ECC Smoke Test error_trigger6 !\n");
    VPRINTF(LOW, "----------------------------------------\n");

    init_interrupts();

    if (rst_count == 0) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n TEST INVALID OUTPUT SIGN_R (>= group_order)\n");
        program_sign_inputs();

        // Force sign_r to all-ones during hw_r_we -> exercises the
        // (read_reg >= group_order) branch of r_output_outofrange.
        SEND_STDOUT_CTRL(0xa2);

        VPRINTF(LOW, "\nECC SIGNING\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nECC r_output_outofrange (>= group_order) error is not detected.\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        ecc_zeroize();
        rst_count++;
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 1) {
        while ((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

        VPRINTF(LOW, "\n TEST INVALID OUTPUT SIGN_S (>= group_order)\n");
        program_sign_inputs();

        // Force sign_s to all-ones during hw_s_we -> exercises the
        // (read_reg >= group_order) branch of s_output_outofrange.
        SEND_STDOUT_CTRL(0xa3);

        VPRINTF(LOW, "\nECC SIGNING\n");
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING);

        wait_for_ecc_intr();
        if (cptra_intr_rcv.ecc_error == 0) {
            VPRINTF(ERROR, "\nECC s_output_outofrange (>= group_order) error is not detected.\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        ecc_zeroize();
    }

    SEND_STDOUT_CTRL(0xff); //End the test
}
