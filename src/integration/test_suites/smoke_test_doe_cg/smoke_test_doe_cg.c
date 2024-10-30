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
#include "clk_gate.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

uint32_t IV_DATA_UDS0 = 0x2eb94297;
uint32_t IV_DATA_UDS1 = 0x77285196;
uint32_t IV_DATA_UDS2 = 0x3dd39a1e;
uint32_t IV_DATA_UDS3 = 0xb95d438f;

volatile uint32_t * doe_iv_0 = (uint32_t *) CLP_DOE_REG_DOE_IV_0;
volatile uint32_t * doe_iv_1 = (uint32_t *) CLP_DOE_REG_DOE_IV_1;
volatile uint32_t * doe_iv_2 = (uint32_t *) CLP_DOE_REG_DOE_IV_2;
volatile uint32_t * doe_iv_3 = (uint32_t *) CLP_DOE_REG_DOE_IV_3;

volatile uint32_t * doe_ctrl = (uint32_t *) CLP_DOE_REG_DOE_CTRL;
volatile uint32_t * doe_status = (uint32_t *) CLP_DOE_REG_DOE_STATUS;

volatile uint32_t * soc_ifc_fw_update_reset = (uint32_t *) (CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET);

volatile uint32_t * pcr_ctrl0 = (uint32_t *) CLP_PV_REG_PCR_CTRL_0;
volatile uint32_t * pcr_ctrl2 = (uint32_t *) CLP_PV_REG_PCR_CTRL_2;
volatile uint32_t * pcr_ctrl5 = (uint32_t *) CLP_PV_REG_PCR_CTRL_5;

volatile uint32_t * key_ctrl1 = (uint32_t *) CLP_KV_REG_KEY_CTRL_1;
volatile uint32_t * key_ctrl4 = (uint32_t *) CLP_KV_REG_KEY_CTRL_4;
volatile uint32_t * key_ctrl7 = (uint32_t *) CLP_KV_REG_KEY_CTRL_7;

volatile uint32_t doe_status_int;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {
    volatile uint32_t mitb0 = 0x00000400;
    volatile uint32_t mitb1 = 0x00000500;
    volatile uint32_t mie_timer0_en = 0x20000000;

    rst_count++;

    VPRINTF(LOW,"---------------------------\n");
    VPRINTF(LOW," DOE Smoke Test With Rand UDS/FE !!\n");
    VPRINTF(LOW,"---------------------------\n");

    //Call interrupt init
    init_interrupts();

    //Enable clk gating and halt core
    SEND_STDOUT_CTRL(0xf2);
    set_mit0(mitb0, mie_timer0_en);
    
    //VPRINTF(LOW,"Rand UDS\n");
    printf("Rand UDS\n");

    //Start UDS and store in KV3
    SEND_STDOUT_CTRL(0xec);
    *doe_ctrl = 0x0000000D;

    __asm__ volatile ("csrwi    %0, %1" \
                    : /* output: none */        \
                    : "i" (0x7c6), "i" (0x03)  /* input : immediate  */ \
                    : /* clobbers: none */);

    // //Poll for DOE status
    while(doe_status_int != (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK)) {
        doe_status_int = *doe_status;
        doe_status_int = doe_status_int & (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK) ;
    }

    //Clear doe_status_int
    doe_status_int = 0;
    
    //--------------------------------------------------------------------
    //Enable clk gating and halt core
    SEND_STDOUT_CTRL(0xf2);
    set_mit0(mitb0, mie_timer0_en);
    
    printf("Rand FE\n");

    //Start FE and store in KV7
    SEND_STDOUT_CTRL(0xed);
    *doe_ctrl = 0x0000001E;

    __asm__ volatile ("csrwi    %0, %1" \
                    : /* output: none */        \
                    : "i" (0x7c6), "i" (0x03)  /* input : immediate  */ \
                    : /* clobbers: none */);

    // //Poll for DOE status
    while(doe_status_int != (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK)) {
        doe_status_int = *doe_status;
        doe_status_int = doe_status_int & (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK) ;
    }

    //Clear doe_status_int
    doe_status_int = 0;

}
