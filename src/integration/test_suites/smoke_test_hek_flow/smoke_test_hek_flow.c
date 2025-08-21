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
#include "doe.h"
#include "hmac.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#ifdef MY_RANDOM_SEED
    unsigned time = (unsigned) MY_RANDOM_SEED;
#else
    unsigned time = 0;
#endif

void main() {
    VPRINTF(LOW,"----------------------------------\n");
    VPRINTF(LOW," KV Smoke Test With HEK flow !!\n");
    VPRINTF(LOW,"----------------------------------\n");

    //Call interrupt init
    init_interrupts();

    /* Intializes random number generator */  //TODO    
    srand(time);

    uint32_t iv_data_uds[]  = {0x2eb94297,0x77285196,0x3dd39a1e,0xb95d438f};
    uint32_t iv_data_fe[]   = {0x14451624,0x6a752c32,0x9056d884,0xdaf3c89d};
    uint32_t iv_data_hek[]  = {0x3e8b1c72,0xa459d6f0,0x5c27b9ae,0xf02d4389};

    // Enable OCP LOCK mode
    VPRINTF(LOW, "OCP_LOCK_MODE_EN: 0x%x\n", (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK));

    uint8_t doe_uds_dest_id;
    uint8_t doe_fe_dest_id;
    uint8_t doe_hek_dest_id;

    doe_uds_dest_id = rand() % 24;
    doe_fe_dest_id = rand() % 24;
    doe_hek_dest_id = rand() % 24;

    VPRINTF(LOW,"doe_uds_dest_id = %u\n", doe_uds_dest_id);
    VPRINTF(LOW,"doe_fe_dest_id  = %u\n", doe_fe_dest_id);
    VPRINTF(LOW,"doe_hek_dest_id = %u\n", doe_hek_dest_id);

    doe_init(iv_data_uds, iv_data_fe, iv_data_hek, doe_uds_dest_id, doe_fe_dest_id, doe_hek_dest_id);
    VPRINTF(LOW,"doe_hek kv id = %x\n", doe_hek_dest_id);
    doe_clear_secrets();

    int32_t hmac512_lfsr_seed_data[HMAC512_LFSR_SEED_SIZE] = {0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C, 0x3C9E16FB, 
                                                              0x800AF504, 0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C,
                                                              0x3C9E16FB, 0x800AF504, 0xC8F518D4, 0xF3AA1BD4}; 

    hmac_io hmac512_key;
    hmac_io hmac512_block;
    hmac_io hmac512_lfsr_seed;
    hmac_io hmac512_tag;

    hmac512_key.kv_intf = TRUE;
    hmac512_key.kv_id = 12;

    //inject hmac512_key to kv key reg (in RTL)
    lsu_write_32(STDOUT, (hmac512_key.kv_id << 8) | 0xa9); 

    hmac512_block.kv_intf = TRUE;
    hmac512_block.kv_id = doe_hek_dest_id;

    hmac512_lfsr_seed.data_size = HMAC512_LFSR_SEED_SIZE;
    for (int i = 0; i < HMAC512_LFSR_SEED_SIZE; i++)
        hmac512_lfsr_seed.data[i] = hmac512_lfsr_seed_data[i];

    hmac512_tag.kv_intf = TRUE;
    hmac512_tag.kv_id = doe_hek_dest_id;

    hmac512_flow(hmac512_key, hmac512_block, hmac512_lfsr_seed, hmac512_tag, TRUE);

    SEND_STDOUT_CTRL(0xff); //End the test
    
}
