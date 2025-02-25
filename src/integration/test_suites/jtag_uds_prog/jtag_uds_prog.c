// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

/* --------------- Function Definitions --------------- */
void main() {

    printf("----------------------------------\n");
    printf(" Mimicking ROM for UDS Programming Flow with JTAG commands!!\n");
    printf("----------------------------------\n");

    // Initialize interrupts (if any)
    init_interrupts();

    uint32_t req_val = 0;
    // Wait for UDS programming request to be asserted.
    printf("Waiting for UDS programming request (mask 0x%X) on register 0x%X...\n",
           SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK,
           CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ);
    do {
        req_val = lsu_read_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ);
        printf("Read request register: 0x%08X\n", req_val);
    } while ((req_val & SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK) == 0);

    printf("UDS programming request detected! (req=0x%08X)\n", req_val);

    // Write the in-progress response.
    printf("Writing UDS programming IN-PROGRESS response (mask 0x%X) to register 0x%X...\n",
           SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK,
           CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP);
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP,
                 SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK);


    // Introduce a delay to simulate processing time.
    for (uint16_t slp = 0; slp < 100; slp++) {
        __asm__ volatile ("nop"); // Simple delay loop (nop)
    }

    // Write the success response.
    printf("Writing UDS programming SUCCESS response (mask 0x%X) to register 0x%X...\n",
           SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK,
           CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP);
    lsu_write_32(CLP_SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP,
                 SOC_IFC_REG_SS_DBG_MANUF_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK);

    printf("----------------------------------\n");
    printf(" JTAG commands successfully fetched and responded to!\n");
    printf("----------------------------------\n");
    for (uint16_t slp = 0; slp < 300; slp++) {
        __asm__ volatile ("nop"); // Simple delay loop (nop)
    }

    SEND_STDOUT_CTRL( 0xff);
}
