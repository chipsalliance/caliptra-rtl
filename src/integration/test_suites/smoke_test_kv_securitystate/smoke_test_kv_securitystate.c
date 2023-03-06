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

void main() {
    printf("---------------------------\n");
    printf(" KV Smoke Test for Security States !!\n");
    printf("---------------------------\n");

    //Call interrupt init
    //init_interrupts();
    if(rst_count == 0) {

        printf("%c",0xf4);

        //Flush KV with debug mode 0 values - expecting AAs
        *clear_secrets = 0x00000001; 

        //Flush KV with debug mode 1 values - expecting 55s
        *clear_secrets = 0x00000003;


        //Deassert flush, but keep debug mode 1
        *clear_secrets = 0x00000002;

        //Write random value to KV00 and KV54
        printf("%c",0xf4);

        //Unlock debug mode - expecting AAs
        printf("%c",0xfa);

        //Lock debug mode
        printf("%c", 0xf9);

        //Debug mode 0
        *clear_secrets = 0x00000000;

        //Unlock and lock debug mode - expecting 55s
        printf("%c", 0xfa);
        printf("%c", 0xf9);

        //-------------------------------------------------
        //Warm reset - Nothing reset?
        //-------------------------------------------------
        rst_count++;
        printf("%c", 0xf6);
    }
    else if(rst_count == 1) {
        //-------------------------------------------------
        //Cold reset - all 0s
        //-------------------------------------------------
        rst_count++;
        printf("%c", 0xf5);
    }
}
