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
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "caliptra_rtl_lib.h"
#include "printf.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>

volatile char* stdout = (char *)STDOUT;
volatile uint32_t  intr_count = 0;
volatile int error_count __attribute__((section(".dccm.persistent"))) = 0;
volatile int rst_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t obf_key[8] __attribute__((section(".dccm.persistent")));

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define TB_CMD_WARM_RESET 0xF6
#define TB_CMD_COLD_RESET 0xF5
#define TB_CMD_TEST_PASS 0xFF
#define TB_CMD_TEST_FAIL 0x01

void main(void) {

    rst_count++;
    VPRINTF_LOW("----------------\nrst count = %d\n----------------\n", rst_count);

    VPRINTF_LOW("==================\nIFC HW Only Reg Test\n==================\n\n");


    if (rst_count == 1) {
        for (int i = 0; i < 8; ++i) {
            obf_key[i] = xorshift32();
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, obf_key[i]);
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x407F|(i<<8));
        }

        // Issue cold reset
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        while(1);
    } else if (rst_count == 2) {
        for (int i = 0; i < 8; ++i) {
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x487F | (i<<8));
            if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) != obf_key[i]) {
                error_count += 1;
            }
        }

        // Modify OBF strap and check that it did not changed
        for (int i = 0; i < 8; ++i) {
            uint32_t new_obf_key = xorshift32() ^ obf_key[i];
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, new_obf_key);
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x407F|(i<<8));
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x487F | (i<<8));
            if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) != obf_key[i]) {
                error_count += 1;
            }
            obf_key[i] = new_obf_key;
        }

        // Issue cold reset
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        while(1);
    } else if (rst_count == 3) {
        for (int i = 0; i < 8; ++i) {
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x487F | (i<<8));
            if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) != obf_key[i]) {
                error_count += 1;
            }
        }
    }
    VPRINTF_LOW("\nIFC HW Only Reg Test Completed\n");

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (error_count == 0 ) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
}
