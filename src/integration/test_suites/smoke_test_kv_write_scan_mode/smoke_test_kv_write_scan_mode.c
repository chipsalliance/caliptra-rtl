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
#include "mlkem.h"
#include "aes.h"
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


void main(){

    VPRINTF(LOW,"----------------------------------\n");
    VPRINTF(LOW," Scan Mode with KV write test !!!\n");
    VPRINTF(LOW,"----------------------------------\n");

    //Call interrupt init
    init_interrupts();

    /* Intializes random number generator */ 
    srand(time);


    //inject scan mode with kv write (in RTL)
    lsu_write_32(STDOUT, 0xba); 


    uint8_t hmac512_key_kv_id = rand() % 24;
    uint8_t hmac512_block_kv_id = rand() % 24;
    uint8_t hmac512_tag_kv_id = rand() % 24;

    //inject hmac512_key to kv key reg (in RTL)
    lsu_write_32(STDOUT, (hmac512_key_kv_id << 8) | 0xa9); 
    //inject hmac512_block to kv key reg (in RTL)
    lsu_write_32(STDOUT, (hmac512_block_kv_id << 8) | 0xb0); 
    
    VPRINTF(LOW, "wait for HMAC to be ready\n");
    while((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    VPRINTF(LOW, "Program KEY Read with 12 dwords from key_kv_id\n");
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                        ((hmac512_key_kv_id << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));
    
    // Check that HMAC KEY is loaded
    while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK) == 0);

    VPRINTF(LOW, "Program HMAC_BLOCK\n");
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL, HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_EN_MASK |
                                                            ((hmac512_block_kv_id << HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_MASK));

    // Check that HMAC BLOCK is loaded
    while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS) & HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_VALID_MASK) == 0);
    
    VPRINTF(LOW, "Program HMAC_TAG Dest\n");
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL, HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_DMA_DATA_DEST_VALID_MASK |
                                                      ((hmac512_tag_kv_id << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) & HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK));

 


    VPRINTF(LOW, "Enable HMAC core\n");
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK |
                                                (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));    

    // wait for HMAC process to be done
    wait_for_hmac_intr();
    

    SEND_STDOUT_CTRL(0xff); //End the test

}
