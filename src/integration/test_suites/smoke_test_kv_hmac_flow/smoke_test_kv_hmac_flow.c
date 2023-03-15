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

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

uint8_t fail_cmd = 0x1;

/* HMAC384 test vector
    KEY = 0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
    BLOCK = 4869205468657265800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000440
    LFSR_SEED = C8F518D4F3AA1BD46ED56C1C3C9E16FB800AF504
    TAG = b6a8d5636f5c6a7224f9977dcf7ee6c7fb6d0c48cbdee9737a959796489bddbc4c5df61d5b3297b4fb68dab9f1b582c2
*/

void hmac_kvflow_test(uint8_t key_kv_id, uint8_t hmacblock_kv_id, uint8_t store_to_kv, uint8_t tag_kv_id, uint32_t block[], uint32_t lfsr_seed[], uint32_t expected_tag[12]){
    uint8_t key_inject_cmd;
    uint8_t offset;
    volatile uint32_t * reg_ptr;

    uint32_t hmac_tag   [12];

    //inject hmac_key to kv key reg (in RTL)
    key_inject_cmd = 0x88 + (key_kv_id & 0x7);
    printf("%c", key_inject_cmd);

    // wait for HMAC to be ready
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_STATUS) & HMAC_REG_HMAC384_STATUS_READY_MASK) == 0);


    // Program KEY Read with 12 dwords from key_kv_id
    lsu_write_32(CLP_HMAC_REG_HMAC384_KV_RD_KEY_CTRL, HMAC_REG_HMAC384_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                      ((key_kv_id & 0x7) << HMAC_REG_HMAC384_KV_RD_KEY_CTRL_READ_ENTRY_LOW));

    // Check that HMAC KEY is loaded
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_RD_KEY_STATUS) & HMAC_REG_HMAC384_KV_RD_KEY_STATUS_VALID_MASK) == 0);

    
    // Program HMAC_BLOCK
    lsu_write_32(CLP_HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL, HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL_READ_EN_MASK |
                                                        ((hmacblock_kv_id & 0x7) << HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW));

    // Check that HMAC BLOCK is loaded
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_RD_BLOCK_STATUS) & HMAC_REG_HMAC384_KV_RD_BLOCK_STATUS_VALID_MASK) == 0);
    /*
    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC384_BLOCK_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC384_BLOCK_31) {
        *reg_ptr++ = block[offset++];
    }
    */

    // Program LFSR_SEED
    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC384_LFSR_SEED_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC384_LFSR_SEED_4) {
        *reg_ptr++ = lfsr_seed[offset++];
    }

    // if we want to store the results into kv
    // set tag DEST to write
    if (store_to_kv){
        lsu_write_32(CLP_HMAC_REG_HMAC384_KV_WR_CTRL, HMAC_REG_HMAC384_KV_WR_CTRL_WRITE_EN_MASK |
                                                      HMAC_REG_HMAC384_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC384_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                      HMAC_REG_HMAC384_KV_WR_CTRL_SHA_BLOCK_DEST_VALID_MASK |
                                                      HMAC_REG_HMAC384_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC384_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC384_KV_WR_CTRL_ECC_MSG_DEST_VALID_MASK);
    }

    // Enable HMAC core
    lsu_write_32(CLP_HMAC_REG_HMAC384_CTRL, HMAC_REG_HMAC384_CTRL_INIT_MASK);

    printf("check tag\n");
    if (store_to_kv){
        // wait for HMAC process - check dest done
        while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_WR_STATUS) & HMAC_REG_HMAC384_KV_WR_STATUS_VALID_MASK) == 0);
    }
    else{
        reg_ptr = (uint32_t *) CLP_HMAC_REG_HMAC384_TAG_0;
        //printf("\nhmac_tag: 0x");
        for (uint32_t i=0; i<12; i++){
            hmac_tag[i] = *(reg_ptr++);
            //printf("%08x", hmac_tag[i]);
        }
        //printf("\n");
        if (memcmp(hmac_tag, expected_tag, sizeof(expected_tag)) != 0){
            printf("TAG MISMATCH!\n");
            printf("%c", fail_cmd);
        }
    }
}


void main() {
    printf("----------------------------------\n");
    printf(" KV Smoke Test With hmac384 flow !!\n");
    printf("----------------------------------\n");

    //Call interrupt init
    //init_interrupts();

    uint32_t block[32] =   {0x48692054,
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

    //this is a random lfsr_seed 160-bit
    uint32_t lfsr_seed_data[] = {0xC8F518D4,
                                 0xF3AA1BD4,
                                 0x6ED56C1C,
                                 0x3C9E16FB,
                                 0x800AF504}; 

    uint32_t expected_digest[] =   {0xb6a8d563,
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

    uint8_t hmackey_kv_id       = 0x2;
    uint8_t hmacblock_kv_id     = 0x1;
    uint8_t store_to_kv         = 0x1;
    uint8_t tag_kv_id           = 0x0;
    hmac_kvflow_test(hmackey_kv_id, hmacblock_kv_id, store_to_kv, tag_kv_id, block, lfsr_seed_data, expected_digest);

    printf("%c",0xff); //End the test
    
}
