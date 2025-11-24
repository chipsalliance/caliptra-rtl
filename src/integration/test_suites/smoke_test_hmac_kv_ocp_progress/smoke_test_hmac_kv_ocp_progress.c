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
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "hmac.h"
#include "caliptra_rtl_lib.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
uint8_t key_kv_intf_bit, block_kv_intf_bit, tag_kv_intf_bit;

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

hmac_io hmac_key;
hmac_io hmac_block;
hmac_io hmac_lfsr_seed;
hmac_io hmac384_tag;
hmac_io hmac512_tag;

//this is the key 384-bit
    uint32_t key384_data[] = {0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b};
    //this is the key 512-bit
    uint32_t key512_data[] = {0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b};

    uint32_t block_data[] = {0x48692054,
                             0x68657265,
                             0x80000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000440};
    uint32_t expected384_tag[] = {0xb6a8d563,
                                0x6f5c6a72,
                                0x24f9977d,
                                0xcf7ee6c7,
                                0xfb6d0c48,
                                0xcbdee973,
                                0x7a959796,
                                0x489bddbc,
                                0x4c5df61d,
                                0x5b3297b4,
                                0xfb68dab9,
                                0xf1b582c2};
    uint32_t expected512_tag[] = {0x637edc6e,
                                  0x01dce7e6,
                                  0x742a9945,
                                  0x1aae82df,
                                  0x23da3e92,
                                  0x439e590e,
                                  0x43e761b3,
                                  0x3e910fb8,
                                  0xac2878eb,
                                  0xd5803f6f,
                                  0x0b61dbce,
                                  0x5e251ff8,
                                  0x789a4722,
                                  0xc1be65ae,
                                  0xa45fd464,
                                  0xe89f8f5b};
    //this is a random lfsr_seed
    uint32_t lfsr_seed_data[12] =  {0xC8F518D4,
                                    0xF3AA1BD4,
                                    0x6ED56C1C,
                                    0x3C9E16FB,
                                    0x800AF504,
                                    0xC8F518D4,
                                    0xF3AA1BD4,
                                    0x6ED56C1C,
                                    0x3C9E16FB,
                                    0x800AF504,
                                    0xC8F518D4,
                                    0xF3AA1BD4};

void set_kv_intf_hmac(uint8_t hmackey_kv_id, uint8_t hmacblock_kv_id, uint8_t tag_kv_id) 
{
    key_kv_intf_bit = (xorshift32() % 2);
    hmac_key.exp_kv_err = FALSE; 
    if (key_kv_intf_bit == 1) {
        hmac_key.kv_intf = TRUE;
        hmac_key.kv_id = hmackey_kv_id;
        VPRINTF(LOW, "HMAC Key KV interface enabled\n");
    }
    else {
        hmac_key.kv_intf = FALSE;
        for (int i = 0; i < HMAC512_KEY_SIZE; i++)
            hmac_key.data[i] = key512_data[i];
        VPRINTF(LOW, "HMAC Key FW interface enabled\n");
    }
    //--------------------------------------------------      

    block_kv_intf_bit = (xorshift32() % 2);
    hmac_block.exp_kv_err = FALSE; 
    if (block_kv_intf_bit == 1) {
        hmac_block.kv_intf = TRUE;
        hmac_block.kv_id = hmacblock_kv_id;
        VPRINTF(LOW, "HMAC Block KV interface enabled\n");
    }
    else {
        hmac_block.kv_intf = FALSE;
        for (int i = 0; i < HMAC512_BLOCK_SIZE; i++)
            hmac_block.data[i] = block_data[i];
        VPRINTF(LOW, "HMAC Block FW interface enabled\n");
    }
    //--------------------------------------------------

    for (int i = 0; i < HMAC512_LFSR_SEED_SIZE; i++)
        hmac_lfsr_seed.data[i] = lfsr_seed_data[i];
    //--------------------------------------------------

    tag_kv_intf_bit = (xorshift32() % 2);
    hmac512_tag.exp_kv_err = FALSE;
    if (tag_kv_intf_bit == 1) {
        hmac512_tag.kv_intf = TRUE;
        hmac512_tag.kv_id = tag_kv_id;
        VPRINTF(LOW, "HMAC Tag KV interface enabled\n");
    }
    else {
        if (key_kv_intf_bit == 1 || block_kv_intf_bit == 1) {
            for (int i = 0; i < HMAC384_TAG_SIZE; i++)
                hmac384_tag.data[i] = 0; //If either key or block is from FW interface, expected tag is 0
        }
        else {
            for (int i = 0; i < HMAC384_TAG_SIZE; i++)
                hmac384_tag.data[i] = expected384_tag[i];
        }

        hmac512_tag.kv_intf = FALSE;
        if (key_kv_intf_bit == 1 || block_kv_intf_bit == 1) {
            for (int i = 0; i < HMAC512_TAG_SIZE; i++)
                hmac512_tag.data[i] = 0; //If either key or block is from FW interface, expected tag is 0
        }
        else {
            for (int i = 0; i < HMAC512_TAG_SIZE; i++)
                hmac512_tag.data[i] = expected512_tag[i];
        }
        VPRINTF(LOW, "HMAC Tag FW interface enabled\n");
    }
}

int get_region(uint8_t kv_id) {
    if (kv_id >= KV_STANDARD_SLOT_LOW && kv_id <= KV_STANDARD_SLOT_HI) {
        return 0; // STANDARD
    } else if (kv_id >= KV_OCP_LOCK_SLOT_LOW && kv_id <= KV_OCP_LOCK_SLOT_HI) {
        return 1; // OCP_LOCK
    }
    return -1; // invalid
}

void main() {

    uint8_t hmacblock_kv_id;
    uint8_t hmackey_kv_id;
    uint8_t tag_kv_id;
    uint8_t ocp_progress_bit;

    srand(time);

    //Call interrupt init
    init_interrupts();

    uint32_t ocp_lock_mode = (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK);
    VPRINTF(LOW, "OCP_LOCK_MODE_EN: 0x%x\n", ocp_lock_mode);

    if (ocp_lock_mode) {
        for(int i = 0; i < 20; i++) {
            //Randomize slots to upper slots
            hmackey_kv_id = xorshift32() % 24;
            hmacblock_kv_id = xorshift32() % 24;
            tag_kv_id = xorshift32() % 24;
            if (ocp_progress_bit == 0){
                ocp_progress_bit = xorshift32() % 2;
            }
            // --- Force values in the first iteration --
            if (i < 3) {
                hmackey_kv_id = KV_OCP_LOCK_KEY_RELEASE_KV_SLOT;
                hmacblock_kv_id = KV_OCP_LOCK_KEY_RELEASE_KV_SLOT;
                tag_kv_id = KV_OCP_LOCK_KEY_RELEASE_KV_SLOT;
            }
            VPRINTF(LOW, "\nSTART TEST %d\n", i);

            set_kv_intf_hmac(hmackey_kv_id, hmacblock_kv_id, tag_kv_id);

            if (ocp_progress_bit) {
                // Enable OCP LOCK mode
                VPRINTF(LOW,"OCP lock in progress\n");
                lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK);
                if ((hmac_key.kv_intf == TRUE) && (hmackey_kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT)){ 
                    hmac_key.exp_kv_err = TRUE;
                }
                if ((hmac_block.kv_intf == TRUE) && (hmacblock_kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT)){ 
                    hmac_block.exp_kv_err = TRUE;
                }
                if ((hmac512_tag.kv_intf == TRUE) && (tag_kv_id == KV_OCP_LOCK_KEY_RELEASE_KV_SLOT)){ 
                    hmac512_tag.exp_kv_err = TRUE;
                }

                int region_key = (hmac_key.kv_intf == TRUE) ? get_region(hmac_key.kv_id) : -2;
                int region_block = (hmac_block.kv_intf == TRUE) ? get_region(hmac_block.kv_id) : -2;
                int region_tag = (hmac512_tag.kv_intf == TRUE) ? get_region(hmac512_tag.kv_id) : -2;

                if (region_key >= 0 && region_block >= 0 && region_tag >= 0) {
                    if (!(region_key == region_tag && region_block == region_tag)) {
                        hmac512_tag.exp_kv_err = TRUE;
                    }
                }
                else if (region_key >= 0 && region_tag >= 0 && region_key != region_tag) {
                    hmac512_tag.exp_kv_err = TRUE;
                }
                else if (region_block >= 0 && region_tag >= 0 && region_block != region_tag) {
                    hmac512_tag.exp_kv_err = TRUE;
                }


            }
            else {
                VPRINTF(LOW,"Regular mode\n");
                lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, 0);
            }

            hmac384_tag.kv_intf = hmac512_tag.kv_intf;
            hmac384_tag.kv_id = hmac512_tag.kv_id;
            hmac384_tag.exp_kv_err = hmac512_tag.exp_kv_err;

            VPRINTF(LOW, "Key KV ID: %d, KV Intf: %d, exp_err: %d\n", hmac_key.kv_id, hmac_key.kv_intf, hmac_key.exp_kv_err);
            VPRINTF(LOW, "Block KV ID: %d, KV Intf: %d, exp_err: %d\n", hmac_block.kv_id, hmac_block.kv_intf, hmac_block.exp_kv_err);
            VPRINTF(LOW, "Tag KV ID: %d, KV Intf: %d, exp_err: %d\n", hmac512_tag.kv_id, hmac512_tag.kv_intf, hmac512_tag.exp_kv_err);

            //inject hmac512_key to kv key reg (in RTL)
            lsu_write_32(STDOUT, (hmac_key.kv_id << 8) | 0xa9);
            //inject hmac_block to kv key reg (in RTL)
            lsu_write_32(STDOUT, (hmac_block.kv_id << 8) | 0xb0);

            uint8_t mode = xorshift32() % 2;
            if (mode == 0){
                VPRINTF(LOW,"Trig hmac384 flow\n");
                hmac384_flow(hmac_key, hmac_block, hmac_lfsr_seed, hmac384_tag, TRUE);
            }
            else{
                VPRINTF(LOW,"Trig hmac512 flow\n");
                hmac512_flow(hmac_key, hmac_block, hmac_lfsr_seed, hmac512_tag, TRUE);
            }

            if (hmac512_tag.kv_intf == TRUE){
                if ((hmac_key.exp_kv_err == FALSE) && (hmac_block.exp_kv_err == FALSE)) {
                    if (hmac512_tag.exp_kv_err == TRUE){
                        if((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS) >> HMAC_REG_HMAC512_KV_WR_STATUS_ERROR_LOW) == 0) {
                            VPRINTF(FATAL, "KV_WRITE_FAIL is not detected!\n");
                            SEND_STDOUT_CTRL(0x1);
                            while(1);
                        }
                        else{
                            VPRINTF(LOW,"KV_WRITE_FAIL is successfully set\n");
                        }
                    }
                    else if((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS) >> HMAC_REG_HMAC512_KV_WR_STATUS_ERROR_LOW) != 0) {
                        VPRINTF(FATAL, "Unexpected KV_WRITE_FAIL is detected!\n");
                        SEND_STDOUT_CTRL(0x1);
                        while(1);
                    }
                }
            }

            hmac_zeroize();
            cptra_intr_rcv.hmac_error = 0;
            cptra_intr_rcv.hmac_notif = 0;
        }
    } else {
        VPRINTF(ERROR, "This test is supported only in SS_MODE\n");
    }
    SEND_STDOUT_CTRL(0xff); //End the test
}
