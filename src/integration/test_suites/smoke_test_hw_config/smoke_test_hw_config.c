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
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"


//int whisperPrintf(const char* format, ...);
//#define ee_printf whisperPrintf


volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {
    .doe_error        = 0,
    .doe_notif        = 0,
    .ecc_error        = 0,
    .ecc_notif        = 0,
    .hmac_error       = 0,
    .hmac_notif       = 0,
    .kv_error         = 0,
    .kv_notif         = 0,
    .sha512_error     = 0,
    .sha512_notif     = 0,
    .sha256_error     = 0,
    .sha256_notif     = 0,
    .qspi_error       = 0,
    .qspi_notif       = 0,
    .uart_error       = 0,
    .uart_notif       = 0,
    .i3c_error        = 0,
    .i3c_notif        = 0,
    .soc_ifc_error    = 0,
    .soc_ifc_notif    = 0,
    .sha512_acc_error = 0,
    .sha512_acc_notif = 0,
};

void main(void) {
        int argc=0;
        char *argv[1];
        uint32_t data;
        uint32_t data_exp;
        uint8_t fail = 0;

        VPRINTF(LOW, "----------------------------------\nHardware Config Test from VeeR EL2  !!\n----------------------------------\n");

        // Setup the interrupt CSR configuration
        init_interrupts();

        // Test HW REV ID
        data = (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_REV_ID) & SOC_IFC_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_MASK) >> SOC_IFC_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_LOW;
        #ifdef CALIPTRA_HW_REV_ID
        if (data != CALIPTRA_HW_REV_ID) {
            VPRINTF(FATAL, "HW REV ID register reports a version of major [%u], minor [%u], patch [%u] which does not match the expected value %u.%u.%u\n",
                           (data & 0xf),
                           (data & 0xf0) >> 4,
                           (data & 0xff00) >> 16,
                           (CALIPTRA_HW_REV_ID & 0xf),
                           (CALIPTRA_HW_REV_ID & 0xf0) >> 4,
                           (CALIPTRA_HW_REV_ID & 0xff00) >> 16);
            fail = 1;
        }
        #else
        VPRINTF(FATAL, "CALIPTRA_HW_REV_ID is not defined!\n");
        fail = 1;
        #endif

        // Test HW CONFIG
        data = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
        #ifdef CALIPTRA_HWCONFIG_TRNG_EN
        data_exp = SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK;
        #else
        data_exp = 0;
        #endif
        if ((data & SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK) != data_exp) {
            VPRINTF(FATAL, "HW Config register reports [%d] for ITRNG EN, expected [%d]!\n", (data & SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK), data_exp);
            fail = 1;
        }
        #ifdef CALIPTRA_HWCONFIG_QSPI_EN
        data_exp = SOC_IFC_REG_CPTRA_HW_CONFIG_QSPI_EN_MASK;
        #else
        data_exp = 0;
        #endif
        if ((data & SOC_IFC_REG_CPTRA_HW_CONFIG_QSPI_EN_MASK) != data_exp) {
            VPRINTF(FATAL, "HW Config register reports [%d] for QSPI EN, expected [%d]!\n", (data & SOC_IFC_REG_CPTRA_HW_CONFIG_QSPI_EN_MASK), data_exp);
            fail = 1;
        }
        #ifdef CALIPTRA_HWCONFIG_I3C_EN
        data_exp = SOC_IFC_REG_CPTRA_HW_CONFIG_I3C_EN_MASK;
        #else
        data_exp = 0;
        #endif
        if ((data & SOC_IFC_REG_CPTRA_HW_CONFIG_I3C_EN_MASK) != data_exp) {
            VPRINTF(FATAL, "HW Config register reports [%d] for I3C EN, expected [%d]!\n", (data & SOC_IFC_REG_CPTRA_HW_CONFIG_I3C_EN_MASK), data_exp);
            fail = 1;
        }
        #ifdef CALIPTRA_HWCONFIG_UART_EN
        data_exp = SOC_IFC_REG_CPTRA_HW_CONFIG_UART_EN_MASK;
        #else
        data_exp = 0;
        #endif
        if ((data & SOC_IFC_REG_CPTRA_HW_CONFIG_UART_EN_MASK) != data_exp) {
            VPRINTF(FATAL, "HW Config register reports [%d] for UART EN, expected [%d]!\n", (data & SOC_IFC_REG_CPTRA_HW_CONFIG_UART_EN_MASK), data_exp);
            fail = 1;
        }
        #ifdef CALIPTRA_HWCONFIG_LMS_EN
        data_exp = SOC_IFC_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_MASK;
        #else
        data_exp = 0;
        #endif
        if ((data & SOC_IFC_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_MASK) != data_exp) {
            VPRINTF(FATAL, "HW Config register reports [%d] for LMS Acc EN, expected [%d]!\n", (data & SOC_IFC_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_MASK), data_exp);
            fail = 1;
        }

        // Ending status
        if (fail) {
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        return;
}
