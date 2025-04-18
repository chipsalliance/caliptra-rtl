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

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};


/* HMAC384 test vector
    KEY = 0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
    BLOCK = 4869205468657265800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000440
    LFSR_SEED = C8F518D4F3AA1BD46ED56C1C3C9E16FB800AF504
    TAG = b6a8d5636f5c6a7224f9977dcf7ee6c7fb6d0c48cbdee9737a959796489bddbc4c5df61d5b3297b4fb68dab9f1b582c2
*/




void main() {
    printf("----------------------------------\n");
    printf(" Smoke Test With FW HMAC after KV flow !!\n");
    printf("----------------------------------\n");

    //Call interrupt init
    init_interrupts();

    uint8_t offset;
    volatile uint32_t * reg_ptr;

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

    uint32_t expected384_tag[12] =   {0xb6a8d563,
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

    uint32_t tag384_zerokey_zeroblock[12] =   
                                   {0x6E120BA2,
                                    0x27BF3557,
                                    0x676B0256,
                                    0x136302D7,
                                    0xD544B868,
                                    0x080BED15,
                                    0xF7D59AB1,
                                    0x1185C79F,
                                    0x44A39E4F,
                                    0x440810F9,
                                    0x7F419C17,
                                    0xD6DB7E92}; 

    uint8_t hmackey_kv_id       = 0x2;
    uint8_t hmacblock_kv_id     = 0x1;
    uint8_t store_to_kv         = 0x1;
    uint8_t tag_kv_id           = 0x0;

    hmac_io hmac384_key;
    hmac_io hmac_block;
    hmac_io hmac_lfsr_seed;
    hmac_io hmac384_tag;

    hmac384_key.kv_intf = TRUE;
    hmac384_key.kv_id = hmackey_kv_id;

    hmac_block.kv_intf = FALSE;
    hmac_block.kv_id = hmacblock_kv_id;
    hmac_block.data_size = 32;
    for (int i = 0; i < hmac_block.data_size; i++)
        hmac_block.data[i] = block[i];

    hmac_lfsr_seed.kv_intf = FALSE;
    hmac_lfsr_seed.data_size = 12;
    for (int i = 0; i < hmac_lfsr_seed.data_size; i++)
        hmac_lfsr_seed.data[i] = lfsr_seed_data[i];

    hmac384_tag.kv_intf = TRUE;
    hmac384_tag.kv_id = tag_kv_id;
    hmac384_tag.data_size = 12;
    for (int i = 0; i < hmac384_tag.data_size; i++)
        hmac384_tag.data[i] = expected384_tag[i];


    //inject hmac384_key to kv key reg (in RTL)
    uint8_t key_inject_cmd = 0xa0 + (hmac384_key.kv_id & 0x7);
    printf("%c", key_inject_cmd);

    hmac384_flow(hmac384_key, hmac_block, hmac_lfsr_seed, hmac384_tag, TRUE);
    
    printf("KV HMAC flow is completed.\n\n");

    /*
        Start FW HMAC without injecting the key/block

        The expected result is doing HMAC with zero key 
        and zero block since all values should be cleared 
        after KV flow.
    */
    printf("Start FW HMAC\n");
    // Enable HMAC core with next command to avoid changing the key
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_NEXT_MASK |
                                            (HMAC384_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));

    // wait for HMAC process to be done
    wait_for_hmac_intr();

    printf("Load TAG from FW HMAC\n");
    reg_ptr = (uint32_t *) CLP_HMAC_REG_HMAC512_TAG_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_TAG_11) {
        if (tag384_zerokey_zeroblock[offset] != *reg_ptr) {
            printf("At offset [%d], hmac384_tag data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", *reg_ptr);
            printf("Expected data: 0x%x\n", tag384_zerokey_zeroblock[offset]);
            printf("%c", 0x1); //fail_cmd
            while(1);
        }
        reg_ptr++;
        offset++;
    }

    hmac_zeroize();

    printf("%c",0xff); //End the test
    
}
