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
    VPRINTF(LOW,"---------------------------\n");
    VPRINTF(LOW," KV Smoke Test With Warm Reset !!\n");
    VPRINTF(LOW,"---------------------------\n");

    //Call interrupt init
    //init_interrupts();
    if(rst_count == 0) {
        VPRINTF(LOW,"1st UDS flow + warm reset\n");
        //Write UDS IV
        *doe_iv_0 = IV_DATA_UDS0;
        *doe_iv_1 = IV_DATA_UDS1;
        *doe_iv_2 = IV_DATA_UDS2;
        *doe_iv_3 = IV_DATA_UDS3;

        //Start UDS and store in KV0
        *doe_ctrl = 0x00000001;
        //Issue warm reset after starting UDS - Interrupts UDS flow so lock_uds_flow should not be set
        rst_count++;
        SEND_STDOUT_CTRL(0xf6);
    }
    else if(rst_count == 1) {
        VPRINTF(LOW,"2nd UDS flow + warm reset\n");
        //Rewrite UDS IV
        *doe_iv_0 = IV_DATA_UDS0;
        *doe_iv_1 = IV_DATA_UDS1;
        *doe_iv_2 = IV_DATA_UDS2;
        *doe_iv_3 = IV_DATA_UDS3;

        //Restart UDS and store in KV0
        *doe_ctrl = 0x00000001;

        //Issue warm reset right before lock_uds_flow is set
         rst_count++;
         SEND_STDOUT_CTRL(0xf7);

        // //Poll for DOE status
        while(doe_status_int != (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK)) {
            doe_status_int = *doe_status;
            doe_status_int = doe_status_int & (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK) ;
        }
        doe_status_int = 0x00000000; //reset internal status register to reuse next time
    }
    else if(rst_count == 2) {
        VPRINTF(LOW,"3rd UDS flow + warm reset\n");
        //Rewrite UDS IV
        *doe_iv_0 = IV_DATA_UDS0;
        *doe_iv_1 = IV_DATA_UDS1;
        *doe_iv_2 = IV_DATA_UDS2;
        *doe_iv_3 = IV_DATA_UDS3;

        //Restart UDS and store in KV0 - this should go through since lock_uds_flow is not set and it will overwrite KV entries
        *doe_ctrl = 0x00000001;

        //Poll for DOE status
        while(doe_status_int != (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK)) {
            doe_status_int = *doe_status;
            doe_status_int = doe_status_int & (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK) ;
        }
        doe_status_int = 0x00000000; //reset internal status register to reuse next time
        
        //Issue warm reset to make sure lock_uds_flow is not reset
        rst_count++;
        SEND_STDOUT_CTRL(0xf6);
    }
    else if(rst_count == 3){
        VPRINTF(LOW,"Cold reset\n");
        rst_count++;
        SEND_STDOUT_CTRL(0xf5); //Issue cold reset and see lock_uds_flow getting reset
    }
    else if(rst_count == 4) {
        VPRINTF(LOW,"4th UDS flow after cold reset\n");
        //Rewrite UDS IV
        *doe_iv_0 = IV_DATA_UDS0;
        *doe_iv_1 = IV_DATA_UDS1;
        *doe_iv_2 = IV_DATA_UDS2;
        *doe_iv_3 = IV_DATA_UDS3;

        //Restart UDS and store in KV0 - this should go through since lock_uds_flow is not set and it will overwrite KV entries
        *doe_ctrl = 0x00000001;

        //Poll for DOE status
        while(doe_status_int != (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK)) {
            doe_status_int = *doe_status;
            doe_status_int = doe_status_int & (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK) ;
        }
        printf("DOE Status %d \n", doe_status_int);

        //Set KV locks
        *key_ctrl1 = 0x00000003;
        *key_ctrl4 = 0x00000001;
        *key_ctrl7 = 0x00000003;
        //Set PCR lock bit
        *pcr_ctrl0 = 0x00000001;
        *pcr_ctrl2 = 0x00000001;
        *pcr_ctrl5 = 0x00000001;

        //Issue fw update reset
        rst_count++;
        *soc_ifc_fw_update_reset = SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK;
    }
    else {
        SEND_STDOUT_CTRL( 0xff);
    }
    
}
