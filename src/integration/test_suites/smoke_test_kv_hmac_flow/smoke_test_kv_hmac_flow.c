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

/* HMAC512 test vector
    KEY = 0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
    BLOCK = 4869205468657265800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000440
    LFSR_SEED = random
    TAG = 637edc6e01dce7e6742a99451aae82df23da3e92439e590e43e761b33e910fb8ac2878ebd5803f6f0b61dbce5e251ff8789a4722c1be65aea45fd464e89f8f5b
*/



void main() {
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " KV Smoke Test With hmac384 flow !!\n");
    VPRINTF(LOW, "----------------------------------\n");

    //Call interrupt init
    init_interrupts();

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
    uint32_t hmac384_lfsr_seed_data[12] =  {0xC8F518D4,
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

    uint32_t hmac384_expected_tag[12] =   {0xb6a8d563,
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

    hmac_io hmac384_key;
    hmac_io hmac384_block;
    hmac_io hmac384_lfsr_seed;
    hmac_io hmac384_tag;

    hmac384_key.kv_intf = TRUE;
    hmac384_key.kv_id = hmackey_kv_id;

    hmac384_block.kv_intf = TRUE;
    hmac384_block.kv_id = hmacblock_kv_id;
    hmac384_block.data_size = 32;
    for (int i = 0; i < hmac384_block.data_size; i++)
        hmac384_block.data[i] = block[i];

    hmac384_lfsr_seed.kv_intf = FALSE;
    hmac384_lfsr_seed.data_size = 12;
    for (int i = 0; i < hmac384_lfsr_seed.data_size; i++)
        hmac384_lfsr_seed.data[i] = hmac384_lfsr_seed_data[i];

    hmac384_tag.kv_intf = TRUE;
    hmac384_tag.kv_id = tag_kv_id;
    hmac384_tag.data_size = 12;
    for (int i = 0; i < hmac384_tag.data_size; i++)
        hmac384_tag.data[i] = hmac384_expected_tag[i];


    //inject hmac384_key to kv key reg (in RTL)
    uint8_t key384_inject_cmd = 0xa0 + (hmac384_key.kv_id & 0x7);
    SEND_STDOUT_CTRL(key384_inject_cmd);

    hmac384_flow(hmac384_key, hmac384_block, hmac384_lfsr_seed, hmac384_tag, TRUE);
    hmac_zeroize();


    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " KV Smoke Test With hmac512 flow !!\n");
    VPRINTF(LOW, "----------------------------------\n");

    //this is a random lfsr_seed
    uint32_t hmac512_lfsr_seed_data[12] =  {0xC8F518D4,
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

    uint32_t hmac512_expected_tag[16] =   {0x637edc6e,
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

    hmac_io hmac512_key;
    hmac_io hmac512_block;
    hmac_io hmac512_lfsr_seed;
    hmac_io hmac512_tag;

    hmac512_key.kv_intf = TRUE;
    hmac512_key.kv_id = 4;

    hmac512_block.kv_intf = FALSE;
    hmac512_block.kv_id = hmacblock_kv_id;
    hmac512_block.data_size = 32;
    for (int i = 0; i < hmac512_block.data_size; i++)
        hmac512_block.data[i] = block[i];

    hmac512_lfsr_seed.kv_intf = FALSE;
    hmac512_lfsr_seed.data_size = 12;
    for (int i = 0; i < hmac512_lfsr_seed.data_size; i++)
        hmac512_lfsr_seed.data[i] = hmac512_lfsr_seed_data[i];

    hmac512_tag.kv_intf = TRUE;
    hmac512_tag.kv_id = tag_kv_id;
    hmac512_tag.data_size = 16;
    for (int i = 0; i < hmac512_tag.data_size; i++)
        hmac512_tag.data[i] = hmac512_expected_tag[i];


    //inject hmac512_key to kv key reg (in RTL)
    lsu_write_32(STDOUT, (hmac512_key.kv_id << 8) | 0xa9); 

    hmac512_flow(hmac512_key, hmac512_block, hmac512_lfsr_seed, hmac512_tag, TRUE);
    hmac_zeroize();

    SEND_STDOUT_CTRL(0xff); //End the test
    
}
