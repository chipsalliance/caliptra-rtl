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

    const uint32_t iv_data_uds[]  = {0x2eb94297,0x77285196,0x3dd39a1e,0xb95d438f};
    const uint32_t iv_data_fe[]   = {0x14451624,0x6a752c32,0x9056d884,0xdaf3c89d};
    const uint32_t iv_data_hek[]  = {0x14451624,0x6a752c32,0x9056d884,0xdaf3c89d}; // TODO unique value



    
//******************************************************************
// DOE(IV_OBF, IV_FE)
//****************************************************************** 
// void kv_doe(uint8_t doe_dest_id){

//     doe_init(iv_data_uds, iv_data_fe, iv_data_hek, (uint32_t) doe_dest_id);

//     VPRINTF(LOW,"doe_fe kv id = %x\n", doe_dest_id);

//     doe_clear_secrets();
// }


/*inline*/ void doe_set_ctrl(const enum doe_cmd_e cmd, uint32_t kv_dest) {
    lsu_write_32(CLP_DOE_REG_DOE_CTRL, ((cmd        << DOE_REG_DOE_CTRL_CMD_LOW    ) & DOE_REG_DOE_CTRL_CMD_MASK    ) |
                                       ((kv_dest    << DOE_REG_DOE_CTRL_DEST_LOW   ) & DOE_REG_DOE_CTRL_DEST_MASK   ) |
                                       (((cmd >> 2) << DOE_REG_DOE_CTRL_CMD_EXT_LOW) & DOE_REG_DOE_CTRL_CMD_EXT_MASK));
}

void main(){

    printf("----------------------------------\n");
    printf(" KV Smoke Test With DOE flow    !!\n");
    printf("----------------------------------\n");

    // uint8_t doe_uds_dest_id;
    volatile uint8_t doe_dest_id;
    volatile uint8_t ocp_progress_bit;

    volatile uint8_t offset;
    volatile uint32_t* reg_ptr;


    //Call interrupt init
    init_interrupts();

    rst_count++;

    uint32_t ocp_lock_mode = (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK);
    VPRINTF(LOW, "OCP_LOCK_MODE_EN: 0x%x\n", ocp_lock_mode);

    // doe_uds_dest_id = 0;
    // random_generator(&doe_dest_id, &cdi_idevid_id, &idevid_ecc_seed_id, &idevid_mldsa_seed_id, &idevid_ecc_privkey_id, &cdi_ldevid_id);
    
    
    if(ocp_lock_mode) {

        ocp_progress_bit = 1; //rand() % 2;
        if (ocp_progress_bit) {
            VPRINTF(LOW,"OCP lock in progress\n");
            lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, 1);
        } else {
            VPRINTF(LOW,"OCP lock not in progress\n");
        }
        
        if (rst_count == 1) {
            //-------------------------------------------------------
            VPRINTF(LOW, "DOE: Init\n");
            doe_dest_id = rand() % 2 + 22;

            // Write IV
            VPRINTF(LOW,"DOE: Writing UDS IV\n");
            reg_ptr = (uint32_t*) CLP_DOE_REG_DOE_IV_0;
            offset = 0;
            while (reg_ptr <= (uint32_t*) CLP_DOE_REG_DOE_IV_3) {
                *reg_ptr++ = iv_data_uds[offset++];
            }

            //start UDS and store in KV
            VPRINTF(LOW,"DOE: Starting UDS Deobfuscation flow with dest id = %d\n", doe_dest_id);
            doe_set_ctrl(DOE_UDS, doe_dest_id);

            // Check that UDS flow is done
            if (doe_dest_id != 23) {
                while((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_VALID_MASK) == 0);
                VPRINTF(LOW, "UDS completed successfully\n");
            }
            else {
                while ((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_ERROR_MASK) == 0);
                VPRINTF(LOW, "Received expected err from DOE UDS flow\n");
                printf("%c", 0xf6); //Issue warm reset
            }
            // VPRINTF(LOW,"DOE flow complete\n");
        } 
        else if (rst_count == 2) {

            //--------------------------------------------------------
            doe_dest_id = rand() % 2 + 22;

            // Write IV
            VPRINTF(LOW,"DOE: Writing Field Entropy IV\n");
            reg_ptr = (uint32_t*) CLP_DOE_REG_DOE_IV_0;
            offset = 0;
            while (reg_ptr <= (uint32_t*) CLP_DOE_REG_DOE_IV_3) {
                *reg_ptr++ = iv_data_fe[offset++];
            }

            //start FE and store in KV
            VPRINTF(LOW,"DOE: Starting Field Entropy Deobfuscation flow with dest id = %d\n", doe_dest_id);
            doe_set_ctrl(DOE_FE, doe_dest_id);

            // Check that FE flow is done
            if (doe_dest_id != 23) {
                while((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_VALID_MASK) == 0);
                VPRINTF(LOW, "FE completed successfully\n");
            }
            else {
                while ((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_ERROR_MASK) == 0);
                VPRINTF(LOW, "Received expected err from DOE FE flow\n");
                printf("%c", 0xf6); //Issue warm reset
            }
            // VPRINTF(LOW,"DOE flow complete\n");
            // printf("%c", 0xf6); //Issue warm reset
        }
        else if (rst_count == 3) {

            //--------------------------------------------------------
            doe_dest_id = rand() % 2 + 22;

            // Write IV
            VPRINTF(LOW,"DOE: Writing HEK IV\n");
            reg_ptr = (uint32_t*) CLP_DOE_REG_DOE_IV_0;
            offset = 0;
            while (reg_ptr <= (uint32_t*) CLP_DOE_REG_DOE_IV_3) {
                *reg_ptr++ = iv_data_hek[offset++];
            }

            if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK) {
                //start HEK and store in KV
                VPRINTF(LOW,"DOE: Starting HEK Deobfuscation flow with dest id = %d\n", doe_dest_id);
                doe_set_ctrl(DOE_HEK, doe_dest_id); // FIXME magic number

                // Check that HEK flow is done
                if (doe_dest_id != 23) {
                    while((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_VALID_MASK) == 0);
                    VPRINTF(LOW, "HEK completed successfully\n");
                }
                else {
                    while ((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_ERROR_MASK) == 0);
                    VPRINTF(LOW, "Received expected err from DOE HEK flow\n");
                    printf("%c", 0xf6); //Issue warm reset
                }
                // VPRINTF(LOW,"DOE flow complete\n");
                // printf("%c", 0xf6); //Issue warm reset
            } else {
                VPRINTF(LOW, "DOE: Skipping HEK Deobfuscation due to HW_CONFIG\n");
            }
        }

    }
    else {
        VPRINTF(LOW, "This test is supported only in SS_MODE\n");
    }

    printf("%c",0xff); //End the test
    // }
}
