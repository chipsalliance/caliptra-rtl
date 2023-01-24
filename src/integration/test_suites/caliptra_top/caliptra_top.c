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
#include <string.h>
#include <stdint.h>
#include "printf.h"

/* --------------- Global symbols/typedefs --------------- */
enum doe_cmd_e {
    DOE_IDLE = 0,
    DOE_UDS = 1,
    DOE_FE = 2,
    DOE_CLEAR_OBF_SECRETS = 3
};

/* --------------- Global vars --------------- */
volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count       = 0;

/* --------------- Function Prototypes --------------- */
void init_doe();

/* --------------- Function Definitions --------------- */
void main() {

    printf("----------------------------------\n");
    printf(" Caliptra Validation ROM!!\n"        );
    printf("----------------------------------\n");

    init_interrupts();

    init_doe();

    while(1);

    printf("----------------------------------\n");
    printf(" Reached end of val FW image unexpectedly! \n");
    printf("----------------------------------\n");
}

void init_doe() {
    uint8_t offset;
    uint32_t* reg_ptr;
    uint32_t iv_data_uds[] = {0x2eb94297,
                              0x77285196,
                              0x3dd39a1e,
                              0xb95d438f};
    uint32_t iv_data_fe[] = {0x14451624,
                             0x6a752c32,
                             0x9056d884,
                             0xdaf3c89d};

    // Write IV
    reg_ptr = (uint32_t*) CLP_DOE_REG_DOE_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_DOE_REG_DOE_IV_3) {
        *reg_ptr++ = iv_data_uds[offset++];
    }

    //start UDS and store in KV0
    lsu_write_32((uint32_t*) CLP_DOE_REG_DOE_CTRL, DOE_UDS);

    // Check that UDS flow is done
    while((lsu_read_32((uint32_t*) CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_VALID_MASK) == 0);

    // Write IV
    reg_ptr = (uint32_t*) CLP_DOE_REG_DOE_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_DOE_REG_DOE_IV_3) {
        *reg_ptr++ = iv_data_fe[offset++];
    }

    //start FE and store in KV6/7
    lsu_write_32((uint32_t*) CLP_DOE_REG_DOE_CTRL, DOE_FE | (0x6 << DOE_REG_DOE_CTRL_DEST_LOW)); // TODO replace 0x6 with entry indicators

    // Check that FE flow is done
    while((lsu_read_32((uint32_t*) CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_VALID_MASK) == 0);

    // Clear Secrets
    lsu_write_32((uint32_t*) CLP_DOE_REG_DOE_CTRL, DOE_CLEAR_OBF_SECRETS);

}
