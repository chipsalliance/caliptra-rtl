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
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "ecc.h"
#include "hmac.h"
#include "sha512.h"
#include "sha256.h"
#include "doe.h"
#include "mldsa.h"
#include <stdlib.h>

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#ifdef MY_RANDOM_SEED
    unsigned time = (unsigned) MY_RANDOM_SEED;
#else
    unsigned time = 0;
#endif


volatile caliptra_intr_received_s cptra_intr_rcv = {0};

const uint32_t iv_data[]  = {0x2eb94297,0x77285196,0x3dd39a1e,0xb95d438f};
    
uint8_t error_flag = 0;


void doe_set_ctrl(const enum doe_cmd_e cmd, uint32_t kv_dest) {
    lsu_write_32(CLP_DOE_REG_DOE_CTRL, ((cmd        << DOE_REG_DOE_CTRL_CMD_LOW    ) & DOE_REG_DOE_CTRL_CMD_MASK    ) |
                                       ((kv_dest    << DOE_REG_DOE_CTRL_DEST_LOW   ) & DOE_REG_DOE_CTRL_DEST_MASK   ) |
                                       (((cmd >> 2) << DOE_REG_DOE_CTRL_CMD_EXT_LOW) & DOE_REG_DOE_CTRL_CMD_EXT_MASK));
}

void doe_flow(const enum doe_cmd_e cmd, uint8_t doe_dest_id) {
    volatile uint8_t offset;
    volatile uint32_t* reg_ptr;


    // Write IV
    VPRINTF(LOW,"DOE: Writing IV\n");
    reg_ptr = (uint32_t*) CLP_DOE_REG_DOE_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_DOE_REG_DOE_IV_3) {
        *reg_ptr++ = iv_data[offset++];
    }

    //start DOE and store in KV
    VPRINTF(LOW, "DOE: Starting flow with cmd = %d, dest id = %d\n", cmd, doe_dest_id);
    doe_set_ctrl(cmd, doe_dest_id);

    // Check that DOE flow is done
    if (doe_dest_id != 23) {
        while((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_VALID_MASK) == 0);
        VPRINTF(LOW, "DOE completed successfully\n");
    }
    else {
        while ((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_ERROR_MASK) == 0);
        VPRINTF(LOW, "Received expected err from DOE flow\n");
        error_flag = 1;
    }
}

void main(){

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " KV Smoke Test With DOE flow    !!\n");
    VPRINTF(LOW, "----------------------------------\n");

    volatile uint8_t doe_dest_id;
    volatile uint8_t ocp_progress_bit;

    //Call interrupt init
    init_interrupts();

    rst_count++;
    error_flag = 0;

    uint32_t ocp_lock_mode = (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK);
    VPRINTF(LOW, "OCP_LOCK_MODE_EN: 0x%x\n", ocp_lock_mode);

    
    if(ocp_lock_mode) {

        ocp_progress_bit = rand() % 2;
        if (ocp_progress_bit) {
            VPRINTF(LOW,"OCP lock in progress\n");
            lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, 1);
        } else {
            VPRINTF(LOW,"OCP lock not in progress\n");
        }

        VPRINTF(LOW, "rst count = %d\n", rst_count);

        if (rst_count == 1) {
            //-------------------------------------------------------
            VPRINTF(LOW, "DOE: Init\n");
            doe_dest_id = rand() % 2 + 22;

            doe_flow(DOE_UDS, doe_dest_id);

            if (error_flag) {
                SEND_STDOUT_CTRL(0xf5); //Issue cold reset
            } else {
                doe_dest_id = rand() % 2 + 22;
                doe_flow(DOE_FE, doe_dest_id);
                if (error_flag) {
                    SEND_STDOUT_CTRL(0xf5); //Issue cold reset
                } else {
                    doe_dest_id = rand() % 2 + 22;
                    doe_flow(DOE_HEK, doe_dest_id);
                    if (error_flag) {
                        SEND_STDOUT_CTRL(0xf5); //Issue cold reset
                    } else {
                        SEND_STDOUT_CTRL(0xff); //End the test
                    }
                }
            }
        } 
        else if (rst_count == 2) {

            //--------------------------------------------------------
            doe_dest_id = rand() % 2 + 22;

            doe_flow(DOE_FE, doe_dest_id);

            if (error_flag) {
                SEND_STDOUT_CTRL(0xf5); //Issue cold reset
            } else {
                doe_dest_id = rand() % 2 + 22;
                doe_flow(DOE_HEK, doe_dest_id);
                if (error_flag) {
                    SEND_STDOUT_CTRL(0xf5); //Issue cold reset
                } else {
                    SEND_STDOUT_CTRL(0xff); //End the test
                }
            }
        }
        else if (rst_count == 3) {

            //--------------------------------------------------------
            doe_dest_id = rand() % 2 + 22;

            doe_flow(DOE_HEK, doe_dest_id);
            if (error_flag) {
                SEND_STDOUT_CTRL(0xf5); //Issue cold reset
            }
        }

    }
    else {
        VPRINTF(ERROR, "This test is supported only in SS_MODE\n");
    }

    SEND_STDOUT_CTRL(0xff); //End the test
}
