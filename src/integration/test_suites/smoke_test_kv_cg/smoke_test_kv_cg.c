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

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t rst_count __attribute__((section(".dccm.persistent"))) = 0;
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

void main() {
    volatile uint32_t mitb0 = 0x00000400;
    volatile uint32_t mitb1 = 0x00000500;
    volatile uint32_t mie_timer0_en = 0x20000000;

    VPRINTF(LOW,"---------------------------\n");
    VPRINTF(LOW," KV Smoke Test With Warm Reset !!\n");
    VPRINTF(LOW,"---------------------------\n");

    //Call interrupt init
    init_interrupts();

    //Enable clk gating and halt core
    SEND_STDOUT_CTRL(0xf2);
    set_mit0(mitb0, mie_timer0_en);

    VPRINTF(LOW,"UDS flow\n");
    //Write UDS IV
    *doe_iv_0 = IV_DATA_UDS0;
    *doe_iv_1 = IV_DATA_UDS1;
    *doe_iv_2 = IV_DATA_UDS2;
    *doe_iv_3 = IV_DATA_UDS3;

    //Start UDS and store in KV0
    *doe_ctrl = 0x00000001;

    //Sleep
    // for (uint16_t i = 0; i < 2; i++){
    //     printf("%d\n", i);
    // }
    printf("Dummy print\n");
    __asm__ volatile ("csrwi    %0, %1" \
                    : /* output: none */        \
                    : "i" (0x7c6), "i" (0x03)  /* input : immediate  */ \
                    : /* clobbers: none */);
    // set_mit0_and_halt_core(mitb0, mie_timer0_en);
    //halt_core();
    // set_mit0(mitb1, mie_timer0_en);
    // halt_core();

    // //Poll for DOE status
    while(doe_status_int != (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK)) {
        doe_status_int = *doe_status;
        doe_status_int = doe_status_int & (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK) ;
    }
    

    VPRINTF(LOW, "Core back up\n");
    //Restart UDS flow after core wakes up - should not go through
    //Write UDS IV
    VPRINTF(LOW, "Writing IV a 2nd time\n");
    *doe_iv_0 = IV_DATA_UDS3;
    *doe_iv_1 = IV_DATA_UDS2;
    *doe_iv_2 = IV_DATA_UDS1;
    *doe_iv_3 = IV_DATA_UDS0;

    //Start UDS and store in KV0
    VPRINTF(LOW, "Starting UDS again\n");
    *doe_ctrl = 0x00000001;

    // //Poll for DOE status
    doe_status_int = 0x00000000;
        while(doe_status_int != (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK)) {
            doe_status_int = *doe_status;
            doe_status_int = doe_status_int & (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK) ;
        }
    
}
