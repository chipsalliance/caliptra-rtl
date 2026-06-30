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
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "riscv_hw_if.h"
#include "wdt.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
volatile rv_exception_struct_s exc_flag __attribute__((section(".dccm.persistent")));

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif


volatile uint32_t * hw_error_fatal      = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void nmi_handler       (void);

void nmi_handler (void) {
    VPRINTF_LOW("**** Entering NMI Handler ****\n");
    if (rst_count == 1 && csr_read_mcause() != 0xF0000000) {
        SEND_STDOUT_CTRL(0x01);
    } else if (rst_count == 2 && csr_read_mcause() != 0xF0000001) {
        SEND_STDOUT_CTRL(0x01);
    }
    SEND_STDOUT_CTRL(0xf6);
}

void main() {
    VPRINTF_LOW("---------------------------\n");
    VPRINTF_LOW(" Smoke Test Invalid regs !!\n");
    VPRINTF_LOW("---------------------------\n");

    rst_count++;

    // Setup the NMI Handler
    lsu_write_32((uintptr_t) (CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR), (uint32_t) (nmi_handler));

    if(rst_count == 1) {
        VPRINTF_LOW("Module: AES\n");
        lsu_write_8((uintptr_t) (CLP_AES_REG_STATUS + 1), 0xFF);
        SEND_STDOUT_CTRL(0xf6);
    }
    if(rst_count == 2) {
        VPRINTF_LOW("Module: SOC_IFC \n");
        lsu_read_32((uintptr_t) (0x30023000));
        SEND_STDOUT_CTRL(0xf6);
    }
    else {
        VPRINTF_LOW("End of test\n");
    }
}
