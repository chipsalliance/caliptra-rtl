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

volatile uint32_t * clear_secrets = (uint32_t *) CLP_KV_REG_CLEAR_SECRETS;
volatile uint32_t * reset_reason  = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_RESET_REASON;

void main() {
    printf("---------------------------\n");
    printf(" KV Smoke Test for Security States !!\n");
    printf("---------------------------\n");

    //Call interrupt init
    //init_interrupts();
    if(rst_count == 0) {
        //Enable prandom reset trigger in the bg
        rst_count++;
        printf("%c", 0xee);

        //Write random value to KV00 and KV54
        printf("%c",0xf4);

        //Flush KV with debug value 0 - expecting AAs
        *clear_secrets = 0x00000001; 

        //Flush KV with debug value 1 - expecting 55s
        *clear_secrets = 0x00000003;


        //Deassert flush, but keep debug value 1
        *clear_secrets = 0x00000002;

        //Write random value to KV00 and KV54
        printf("%c",0xf4);

        //Unlock debug mode - expecting 55s
        printf("%c",0xfa);

        //Lock debug mode
        printf("%c", 0xf9);

        //Debug value 0
        *clear_secrets = 0x00000000;

        //Unlock and lock debug mode - expecting AAs
        printf("%c", 0xfa);
        printf("%c", 0xf9);

        //Debug value 1
        *clear_secrets = 0x00000002;

        //Enable and disable scan mode - expecting 55s
        printf("%c", 0xef);
        printf("%c", 0xf0);

        //Wait for reset to be asserted before advancing
        while(*reset_reason & SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK != SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK);
    }
    else if(rst_count == 1) {
        //-------------------------------------------------
        //Cold reset - all 0s
        //-------------------------------------------------
        rst_count++;
        printf("%c", 0xf5);
    }
}
