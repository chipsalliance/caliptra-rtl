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
volatile uint32_t rst_count = 0;

uint32_t IV_DATA_FE0 = 0x14451624;
uint32_t IV_DATA_FE1 = 0x6a752c32;
uint32_t IV_DATA_FE2 = 0x9056d884;
uint32_t IV_DATA_FE3 = 0xdaf3c89d;

volatile uint32_t * doe_iv_0 = (uint32_t *) CLP_DOE_REG_DOE_IV_0;
volatile uint32_t * doe_iv_1 = (uint32_t *) CLP_DOE_REG_DOE_IV_1;
volatile uint32_t * doe_iv_2 = (uint32_t *) CLP_DOE_REG_DOE_IV_2;
volatile uint32_t * doe_iv_3 = (uint32_t *) CLP_DOE_REG_DOE_IV_3;

volatile uint32_t * doe_ctrl = (uint32_t *) CLP_DOE_REG_DOE_CTRL;
volatile uint32_t * doe_status = (uint32_t *) CLP_DOE_REG_DOE_STATUS;

volatile uint32_t doe_status_int;

void main() {
    printf("---------------------------\n");
    printf(" KV Smoke Test With FE + Reset !!\n");
    printf("---------------------------\n");

    //Call interrupt init
    //init_interrupts();
    if(rst_count == 0) {
        printf("1st FE flow + warm reset\n");
        //Write FE IV
        *doe_iv_0 = IV_DATA_FE0;
        *doe_iv_1 = IV_DATA_FE1;
        *doe_iv_2 = IV_DATA_FE2;
        *doe_iv_3 = IV_DATA_FE3;

        //Start FE and store in KV0
        *doe_ctrl = 0x00000002;
        //Issue warm reset after starting FE - Interrupts FE flow so lock_FE_flow should not be set
        rst_count++;
        printf("%c",0xf6);
    }
    else if(rst_count == 1) {
        printf("2nd FE flow + warm reset\n");
        //Rewrite FE IV
        *doe_iv_0 = IV_DATA_FE0;
        *doe_iv_1 = IV_DATA_FE1;
        *doe_iv_2 = IV_DATA_FE2;
        *doe_iv_3 = IV_DATA_FE3;

        //Restart FE and store in KV0
        *doe_ctrl = 0x00000002;

        //Issue warm reset right before lock_FE_flow is set
         rst_count++;
         printf("%c",0xf7);

        // //Poll for DOE status
        while(doe_status_int != (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK)) {
            doe_status_int = *doe_status;
        }
        doe_status_int = 0x00000000; //reset internal status register to reuse next time
    }
    else if(rst_count == 2) {
        printf("3rd FE flow + warm reset\n");
        //Rewrite FE IV
        *doe_iv_0 = IV_DATA_FE0;
        *doe_iv_1 = IV_DATA_FE1;
        *doe_iv_2 = IV_DATA_FE2;
        *doe_iv_3 = IV_DATA_FE3;

        //Restart FE and store in KV0 - this should go through since lock_FE_flow is not set and it will overwrite KV entries
        *doe_ctrl = 0x00000002;

        //Poll for DOE status
        while(doe_status_int != (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK)) {
            doe_status_int = *doe_status;
        }
        doe_status_int = 0x00000000; //reset internal status register to reuse next time
        
        //Issue warm reset to make sure lock_FE_flow is not reset
        rst_count++;
        printf("%c",0xf6);
    }
    else if(rst_count == 3){
        printf("Cold reset\n");
        rst_count++;
        printf("%c",0xf5); //Issue cold reset and see lock_FE_flow getting reset
    }
    else if(rst_count == 4) {
        printf("4th FE flow after cold reset\n");
        //Rewrite FE IV
        *doe_iv_0 = IV_DATA_FE0;
        *doe_iv_1 = IV_DATA_FE1;
        *doe_iv_2 = IV_DATA_FE2;
        *doe_iv_3 = IV_DATA_FE3;

        //Restart FE and store in KV0 - this should go through since lock_FE_flow is not set and it will overwrite KV entries
        *doe_ctrl = 0x00000002;

        //Poll for DOE status
        while(doe_status_int != (DOE_REG_DOE_STATUS_VALID_MASK | DOE_REG_DOE_STATUS_READY_MASK)) {
            doe_status_int = *doe_status;
            printf("doe status = %d", doe_status_int);
        }
    }
    else {
        printf("%c", 0xff);
    }
    
}