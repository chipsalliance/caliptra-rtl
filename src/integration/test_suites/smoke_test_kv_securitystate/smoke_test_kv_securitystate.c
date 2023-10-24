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

volatile uint32_t * clear_secrets = (uint32_t *) CLP_KV_REG_CLEAR_SECRETS;
volatile uint32_t * reset_reason  = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_RESET_REASON;
volatile uint16_t i = 0;

void main() {
    printf("---------------------------\n");
    printf(" KV Smoke Test for Security States !!\n");
    printf("---------------------------\n");

    rst_count++;

    //Call interrupt init
    //init_interrupts();
    if(rst_count == 1) {
        //Enable prandom reset trigger in the bg
        // SEND_STDOUT_CTRL( 0xee);

        //Unlock debug mode - expecting ?
        printf("Unlock debug mode\n");
        SEND_STDOUT_CTRL(0xfa);
        //Add reset
        // for(int i=0; i<100;i++) {
        //     printf("%d\n",i);
        // }
        for(i=0;i<100;i++);
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 2) {
        //Write random value to KV00 and KV54
        // SEND_STDOUT_CTRL(0xf4);

        printf("Clear secrets during debug mode\n");

        //Flush KV with debug value 0 - expecting AAs
        *clear_secrets = 0x00000001; 

        //Flush KV with debug value 1 - expecting 55s
        *clear_secrets = 0x00000003;


        //Deassert flush, but keep debug value 1
        *clear_secrets = 0x00000002;

        //Write random value to KV00 and KV54
        // SEND_STDOUT_CTRL(0xf4);

        //Lock debug mode
        printf("Lock debug mode\n");
        SEND_STDOUT_CTRL(0xf9);
        //Add reset
        // for(int i=0; i<100;i++){
        //     printf("%d\n",i);
        // }
        for(i=0;i<100;i++);
        SEND_STDOUT_CTRL(0xf6);

    }
    else if (rst_count == 3) {

        printf("Unlock debug mode - 2\n");
        //Unlock and lock debug mode - expecting AAs
        SEND_STDOUT_CTRL(0xfa);
        //Add reset
        // for(int i=0; i<100;i++){
        //     printf("%d\n",i);
        // }
        for(i=0;i<100;i++);
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 4) {
        printf("Clear secrets again\n");
        //Debug value 0
        *clear_secrets = 0x00000000;

        //Debug value 1
        *clear_secrets = 0x00000002;

        printf("Lock debug mode - 2\n");
        SEND_STDOUT_CTRL(0xf9);
        //Add reset
        // for(int i=0; i<100;i++) {
        //     printf("%d\n",i);
        // }
        for(i=0;i<100;i++);
        SEND_STDOUT_CTRL(0xf6);
    }
    else if (rst_count == 5) {
        printf("Enable scan mode\n");
        //Enable and disable scan mode - expecting 55s
        SEND_STDOUT_CTRL(0xef);
        //Add reset
        // for(int i=0; i<100;i++) {
        //     printf("%d\n",i);
        // }
        for(i=0;i<100;i++);
        SEND_STDOUT_CTRL(0xf6);

    }
    else if (rst_count == 6) {
        // printf("Waiting for reason\n");
        // //Wait for reset to be asserted before advancing
        // while(*reset_reason & SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK != SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK);

        printf("Disable scan mode\n");
        //Disable scan mode
        SEND_STDOUT_CTRL(0xf0);
        //Add reset
        // for(int i=0; i<100;i++){
        //     printf("%d\n",i);
        // }
        for(i=0;i<100;i++);
        SEND_STDOUT_CTRL(0xf6);

    }
    else if(rst_count == 7) {
        // printf("Waiting for reason - 2\n");
        // //Wait for reset to be asserted before advancing
        // while(*reset_reason & SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK != SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK);

        //-------------------------------------------------
        //Cold reset - all 0s
        //-------------------------------------------------
        printf("Cold rst\n");
        SEND_STDOUT_CTRL(0xf5);
    }
}
