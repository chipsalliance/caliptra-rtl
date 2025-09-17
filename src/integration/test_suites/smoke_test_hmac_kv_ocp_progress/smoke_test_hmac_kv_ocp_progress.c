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

hmac_io hmac384_key;
hmac_io hmac384_block;
hmac_io hmac384_lfsr_seed;
hmac_io hmac384_tag;

hmac_io hmac512_key;
hmac_io hmac512_block;
hmac_io hmac512_lfsr_seed;
hmac_io hmac512_tag;

uint8_t hmacblock_kv_id;
uint8_t hmackey_kv_id;
uint8_t tag_kv_id;

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

void set_kv_intf_hmac384(uint8_t hmackey_kv_id, uint8_t hmacblock_kv_id, uint8_t tag_kv_id) 
{
    key_kv_intf_bit = (xorshift32() % 2);
    if (key_kv_intf_bit == 1) {
        hmac384_key.kv_intf = TRUE;
        hmac384_key.kv_id = hmackey_kv_id;
        hmac384_key.exp_kv_err = FALSE;
        VPRINTF(LOW, "HMAC384 Key KV interface enabled\n");
    }
    else {
        hmac384_key.kv_intf = FALSE;
        hmac384_key.data_size = HMAC384_KEY_SIZE;
        for (int i = 0; i < hmac384_key.data_size; i++)
            hmac384_key.data[i] = key384_data[i];
        VPRINTF(LOW, "HMAC384 Key FW interface enabled\n");
    }
    //--------------------------------------------------      

    block_kv_intf_bit = (xorshift32() % 2);
    if (block_kv_intf_bit == 1) {
        hmac384_block.kv_intf = TRUE;
        hmac384_block.kv_id = hmacblock_kv_id;
        hmac384_block.exp_kv_err = FALSE;
        VPRINTF(LOW, "HMAC384 Block KV interface enabled\n");
    }
    else {
        hmac384_block.kv_intf = FALSE;
        hmac384_block.data_size = HMAC384_BLOCK_SIZE;
        for (int i = 0; i < hmac384_block.data_size; i++)
            hmac384_block.data[i] = block_data[i];
        VPRINTF(LOW, "HMAC384 Block FW interface enabled\n");
    }
    //--------------------------------------------------

    hmac384_lfsr_seed.kv_intf = FALSE;
    hmac384_lfsr_seed.data_size = HMAC384_LFSR_SEED_SIZE;
    for (int i = 0; i < hmac384_lfsr_seed.data_size; i++)
        hmac384_lfsr_seed.data[i] = lfsr_seed_data[i];
    //--------------------------------------------------

    tag_kv_intf_bit = (xorshift32() % 2);
    if (tag_kv_intf_bit == 1) {
        hmac384_tag.kv_intf = TRUE;
        hmac384_tag.kv_id = tag_kv_id;
        hmac384_tag.exp_kv_err = FALSE;
        VPRINTF(LOW, "HMAC384 Tag KV interface enabled\n");
    }
    else {
        hmac384_tag.kv_intf = FALSE;
        hmac384_tag.data_size = HMAC384_TAG_SIZE;

        if (key_kv_intf_bit == 1 || block_kv_intf_bit == 1) {
            for (int i = 0; i < hmac384_tag.data_size; i++)
                hmac384_tag.data[i] = 0; //If either key or block is from FW interface, expected tag is 0
        }
        else {
            for (int i = 0; i < hmac384_tag.data_size; i++)
                hmac384_tag.data[i] = expected384_tag[i];
        }
        VPRINTF(LOW, "HMAC384 Tag FW interface enabled\n");
    }
}

void set_kv_intf_hmac512(uint8_t hmackey_kv_id, uint8_t hmacblock_kv_id, uint8_t tag_kv_id) 
{
    key_kv_intf_bit = (xorshift32() % 2);
    if (key_kv_intf_bit == 1) {
        hmac512_key.kv_intf = TRUE;
        hmac512_key.kv_id = hmackey_kv_id;
        hmac512_key.exp_kv_err = FALSE;
        VPRINTF(LOW, "HMAC512 Key KV interface enabled\n");
    }
    else {
        hmac512_key.kv_intf = FALSE;
        hmac512_key.data_size = HMAC512_KEY_SIZE;
        for (int i = 0; i < hmac512_key.data_size; i++)
            hmac512_key.data[i] = key512_data[i];
        VPRINTF(LOW, "HMAC512 Key FW interface enabled\n");
    }
    //--------------------------------------------------      

    block_kv_intf_bit = (xorshift32() % 2);
    if (block_kv_intf_bit == 1) {
        hmac512_block.kv_intf = TRUE;
        hmac512_block.kv_id = hmacblock_kv_id;
        hmac512_block.exp_kv_err = FALSE;
        VPRINTF(LOW, "HMAC512 Block KV interface enabled\n");
    }
    else {
        hmac512_block.kv_intf = FALSE;
        hmac512_block.data_size = HMAC512_BLOCK_SIZE;
        for (int i = 0; i < hmac512_block.data_size; i++)
            hmac512_block.data[i] = block_data[i];
        VPRINTF(LOW, "HMAC512 Block FW interface enabled\n");
    }
    //--------------------------------------------------

    hmac512_lfsr_seed.kv_intf = FALSE;
    hmac512_lfsr_seed.data_size = HMAC512_LFSR_SEED_SIZE;
    for (int i = 0; i < hmac512_lfsr_seed.data_size; i++)
        hmac512_lfsr_seed.data[i] = lfsr_seed_data[i];
    //--------------------------------------------------

    tag_kv_intf_bit = (xorshift32() % 2);
    if (tag_kv_intf_bit == 1) {
        hmac512_tag.kv_intf = TRUE;
        hmac512_tag.kv_id = tag_kv_id;
        hmac512_tag.exp_kv_err = FALSE;
        VPRINTF(LOW, "HMAC512 Tag KV interface enabled\n");
    }
    else {
        hmac512_tag.kv_intf = FALSE;
        hmac512_tag.data_size = HMAC512_TAG_SIZE;

        if (key_kv_intf_bit == 1 || block_kv_intf_bit == 1) {
            for (int i = 0; i < hmac512_tag.data_size; i++)
                hmac512_tag.data[i] = 0; //If either key or block is from FW interface, expected tag is 0
        }
        else {
            for (int i = 0; i < hmac512_tag.data_size; i++)
                hmac512_tag.data[i] = expected512_tag[i];
        }
        VPRINTF(LOW, "HMAC512 Tag FW interface enabled\n");
    }
}

void main() {

    uint8_t ocp_progress_bit;

    srand(time);

    //Randomize slots to upper slots
    hmackey_kv_id = (xorshift32() % 8) + 16;

    do {
        hmacblock_kv_id     = (xorshift32() % 8) + 16;
    } while (hmacblock_kv_id == hmackey_kv_id);

    tag_kv_id = (xorshift32() % 8) + 16;

    //Call interrupt init
    init_interrupts();

    uint32_t ocp_lock_mode = (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK);
    VPRINTF(LOW, "OCP_LOCK_MODE_EN: 0x%x\n", ocp_lock_mode);

    if (ocp_lock_mode) {

        ocp_progress_bit = xorshift32() % 2;
        if (ocp_progress_bit) {
            // Enable OCP LOCK mode
            VPRINTF(LOW,"OCP lock in progress\n");
            lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, 1);
            if (hmackey_kv_id == 23){ 
                hmac384_key.exp_kv_err = TRUE; 
            }
            if (hmacblock_kv_id == 23){ 
                hmac384_block.exp_kv_err = TRUE; 
            }
        }

        VPRINTF(LOW, "----------------------------------\n");
        VPRINTF(LOW, " KV Smoke Test With hmac384 flow !!\n");
        VPRINTF(LOW, "----------------------------------\n");

        VPRINTF(LOW, "Running hmac with key kv_id = 0x%x, block kv_id = 0x%x, tag kv_id = 0x%x\n", hmackey_kv_id, hmacblock_kv_id, tag_kv_id);

        set_kv_intf_hmac384(hmackey_kv_id, hmacblock_kv_id, tag_kv_id);

        //inject hmac384_key to kv key reg (in RTL)
        lsu_write_32(STDOUT, (hmac384_key.kv_id << 8) | 0xa0);
        // lsu_write_32(STDOUT, 0xaa);
        //inject hmac_block to kv key reg (in RTL)
        lsu_write_32(STDOUT, (hmac384_block.kv_id << 8) | 0xb0);

        hmac384_flow(hmac384_key, hmac384_block, hmac384_lfsr_seed, hmac384_tag, TRUE);
        hmac_zeroize();

        VPRINTF(LOW, "----------------------------------\n");
        VPRINTF(LOW, " KV Smoke Test With hmac512 flow !!\n");
        VPRINTF(LOW, "----------------------------------\n");

        //Randomize slots to upper slots
        hmackey_kv_id = (xorshift32() % 8) + 16;
        
        do {
            hmacblock_kv_id = (xorshift32() % 8) + 16;
        } while (hmacblock_kv_id == hmackey_kv_id);

        tag_kv_id = (xorshift32() % 8) + 16;

        VPRINTF(LOW, "Running hmac with key kv_id = 0x%x, block kv_id = 0x%x, tag kv_id = 0x%x\n", hmackey_kv_id, hmacblock_kv_id, tag_kv_id);
        set_kv_intf_hmac512(hmackey_kv_id, hmacblock_kv_id, tag_kv_id);


        //inject hmac512_key to kv key reg (in RTL)
        lsu_write_32(STDOUT, (hmac512_key.kv_id << 8) | 0xa9);
        // lsu_write_32(STDOUT, 0xaa);
        //inject hmac_block to kv key reg (in RTL)
        lsu_write_32(STDOUT, (hmac512_block.kv_id << 8) | 0xb0);

        ocp_progress_bit = xorshift32() % 2;
        if (ocp_progress_bit) {
            // Enable OCP LOCK mode
            VPRINTF(LOW,"OCP lock in progress\n");
            lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, 1);
            if (hmackey_kv_id == 23){ 
                hmac512_key.exp_kv_err = TRUE; 
            }
            if (hmacblock_kv_id == 23){ 
                hmac512_block.exp_kv_err = TRUE; 
            }
        }

        VPRINTF(LOW,"Trig hmac 512 flow\n");
        hmac512_flow(hmac512_key, hmac512_block, hmac512_lfsr_seed, hmac512_tag, TRUE);
        hmac_zeroize();

    } else {
        VPRINTF(ERROR, "This test is supported only in SS_MODE\n");
    }
    SEND_STDOUT_CTRL(0xff); //End the test
}
