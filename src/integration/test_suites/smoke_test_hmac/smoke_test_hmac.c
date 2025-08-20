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
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "hmac.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};


void main() {

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

    
    SEND_STDOUT_CTRL(0x7F); // Switch to MANUF device lifecycle state
                                    

    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC384 smoke test !!\n"            );
    VPRINTF(LOW, "----------------------------------\n");

    // Call interrupt init
    init_interrupts();

    hmac_io hmac384_key;
    hmac_io hmac_block;
    hmac_io hmac_lfsr_seed;
    hmac_io hmac384_tag;

    hmac_io hmac512_key;
    hmac_io hmac512_tag;

    hmac384_key.kv_intf = FALSE;
    hmac384_key.data_size = 12;
    for (int i = 0; i < hmac384_key.data_size; i++)
        hmac384_key.data[i] = key384_data[i];

    hmac_block.kv_intf = FALSE;
    hmac_block.data_size = 32;
    for (int i = 0; i < hmac_block.data_size; i++)
        hmac_block.data[i] = block_data[i];

    hmac_lfsr_seed.kv_intf = FALSE;
    hmac_lfsr_seed.data_size = 12;
    for (int i = 0; i < hmac_lfsr_seed.data_size; i++)
        hmac_lfsr_seed.data[i] = lfsr_seed_data[i];

    hmac384_tag.kv_intf = FALSE;
    hmac384_tag.data_size = 12;
    for (int i = 0; i < hmac384_tag.data_size; i++)
        hmac384_tag.data[i] = expected384_tag[i];


    hmac384_flow(hmac384_key, hmac_block, hmac_lfsr_seed, hmac384_tag, TRUE);
    hmac_zeroize();


    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC512 smoke test !!\n"            );
    VPRINTF(LOW, "----------------------------------\n");

    hmac512_key.kv_intf = FALSE;
    hmac512_key.data_size = 16;
    for (int i = 0; i < hmac512_key.data_size; i++)
        hmac512_key.data[i] = key512_data[i];

    hmac512_tag.kv_intf = FALSE;
    hmac512_tag.data_size = 16;
    for (int i = 0; i < hmac512_tag.data_size; i++)
        hmac512_tag.data[i] = expected512_tag[i];

    hmac512_flow(hmac512_key, hmac_block, hmac_lfsr_seed, hmac512_tag, TRUE);
    hmac_zeroize();

    hmac512_key.kv_intf = FALSE;
    hmac512_key.data_size = 16;
    for (int i = 0; i < hmac512_key.data_size; i++)
        hmac512_key.data[i] = 0x12345678;

    hmac512_flow_csr(hmac512_key, hmac_block, hmac_lfsr_seed, hmac512_tag, TRUE);
    hmac_zeroize();

    // Write 0xff to STDOUT for TB to terminate test.
    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
