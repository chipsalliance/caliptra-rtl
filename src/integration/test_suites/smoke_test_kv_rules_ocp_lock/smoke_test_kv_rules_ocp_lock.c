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
#include "veer-csr.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "soc_ifc.h"
#include "hmac.h"
#include "aes.h"
#include "ecc.h"
#include "mlkem.h"
#include "keyvault.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#ifdef MY_RANDOM_SEED
    unsigned rand_seed = (unsigned) MY_RANDOM_SEED;
#else
    unsigned rand_seed = 0;
#endif


void hmac_test(uint8_t hmackey_kv_id, uint8_t hmacblock_kv_id, uint8_t tag_kv_id){
    hmac_io hmac512_key;
    hmac_io hmac512_block;
    hmac_io hmac512_lfsr_seed;
    hmac_io hmac512_tag;

    //inject hmac512_key to kv key reg (in RTL)
    lsu_write_32(STDOUT, (hmackey_kv_id << 8) | 0xa9); 
    
    //inject hmac512_block to kv key reg (in RTL)
    lsu_write_32(STDOUT, 0xb0); 

    hmac512_key.kv_intf = TRUE;
    hmac512_key.kv_id = hmackey_kv_id;

    hmac512_block.kv_intf = TRUE;
    hmac512_block.kv_id = hmacblock_kv_id;

    hmac512_lfsr_seed.data_size = HMAC512_LFSR_SEED_SIZE;
    for (int i = 0; i < HMAC512_LFSR_SEED_SIZE; i++)
        hmac512_lfsr_seed.data[i] = rand() % 0xffffffff;

    hmac512_tag.kv_intf = TRUE;
    hmac512_tag.kv_id = tag_kv_id;

    hmac512_flow(hmac512_key, hmac512_block, hmac512_lfsr_seed, hmac512_tag, TRUE);

}

void ecc_test(uint8_t seed_kv_id, uint8_t privkey_kv_id){    
    //inject seed to kv key reg (in RTL)
    printf("Inject SEED into KV\n");
    uint8_t seed_inject_cmd = 0x80 + (seed_kv_id & 0x7);
    printf("%c", seed_inject_cmd);  

    // Program ECC_SEED Read with 12 dwords from seed_kv_id
    lsu_write_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL, (ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK |
                                                ((seed_kv_id << ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW) & ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_MASK)));

    while((lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_STATUS) & ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_MASK) == 0);

    // set privkey DEST to write
    lsu_write_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, (ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                                                ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK |
                                                ((privkey_kv_id << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) & ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK)));

    printf("\nECC KEYGEN\n");
    // Enable ECC KEYGEN core
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_KEYGEN);

    //wait for privkey generation
    while (((lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_STATUS) >> 2) == 0) & (cptra_intr_rcv.ecc_error == 0) & (cptra_intr_rcv.ecc_notif == 0)){
        __asm__ volatile ("wfi"); // "Wait for interrupt"
        // Sleep during ECC operation to allow ISR to execute and show idle time in sims
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    }

}

void mlkem_test(uint8_t seed_kv_id, uint8_t sharedkey_kv_id){
    mlkem_seed seed;
    mlkem_shared_key shared_key;
    uint32_t actual_ciphertext[MLKEM_CIPHERTEXT_SIZE];
    uint32_t abr_entropy[ABR_ENTROPY_SIZE];

    seed.kv_intf = TRUE;
    seed.kv_id = seed_kv_id;
    shared_key.kv_intf = TRUE;
    shared_key.kv_id = sharedkey_kv_id;

    for (int i = 0; i < ABR_ENTROPY_SIZE; i++)
        abr_entropy[i] = rand() % 0xffffffff;

    lsu_write_32(STDOUT, (seed.kv_id << 8) | 0xb1); //Inject MLKEM SEED vectors into KV 0

    mlkem_keygen_decaps_check(seed, actual_ciphertext, abr_entropy, shared_key);
    cptra_intr_rcv.abr_notif = 0;
}

void enable_ocp_lock(){
    // Enable OCP LOCK mode
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG, SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK);
    VPRINTF(LOW, "OCP_LOCK_MODE_EN: 0x%x\n", (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK));
    // Set OCP_LOCK_IN_PROGRESS
    lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK);
    VPRINTF(LOW, "OCP_LOCK_IN_PROGRESS: 0x%x\n", lsu_read_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL));
    if((lsu_read_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL) & SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK) == 0) {
        VPRINTF(FATAL, "OCP_LOCK_IN_PROGRESS is not set!\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

void main() {
    printf("------------------------------\n");
    printf(" KV Rules for OCP LOCK Mode !!\n");
    printf("------------------------------\n");

    /* Intializes random number generator */
    srand(rand_seed);

    //Call interrupt init
    init_interrupts();
    uint8_t kv_slot0, kv_slot1, kv_slot2;

    uint8_t op = rand() % 3;
    kv_slot0 = rand() % 24;
    kv_slot1 = 4; //inject hmac_block
    if (kv_slot0 < 16){
        kv_slot2 = 16 + rand() % 8;
    }
    else {
        kv_slot2 = rand() % 16;
    }
    VPRINTF(LOW, "slot0: 0x%x, slot1: 0x%x, slot2: 0x%x\n", kv_slot0, kv_slot1, kv_slot2);

    switch (op){
        case 0:
            VPRINTF(LOW,"Running HMAC core\n");
            hmac_test(kv_slot0, kv_slot1, kv_slot2);
            if((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS) >> 2) != 0) {
                VPRINTF(FATAL, "KV_WRITE_FAIL is set!\n");
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
            else{
                VPRINTF(LOW, "KV Write is successful!\n");
            }

            enable_ocp_lock();
            hmac_test(kv_slot0, kv_slot1, kv_slot2);
            if((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS) >> 2) == 0) {
                VPRINTF(FATAL, "KV_WRITE_FAIL is not detected!\n");
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
            else{
                VPRINTF(LOW,"KV_WRITE_FAIL is successfully set\n");
            }

            break;

        case 1:
            VPRINTF(LOW,"Running ECC KeyGen core\n");
            enable_ocp_lock();
            ecc_test(kv_slot0, kv_slot2);
            
            if((lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_STATUS) >> 2) == 0) {
                VPRINTF(FATAL, "KV Write Error is not detected!\n");
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
            else{
                VPRINTF(LOW,"KV_WRITE_FAIL is successfully set\n");
            }

            break;

        case 2:
            VPRINTF(LOW,"Running MLKEM KeyGen+Decaps core\n");
            enable_ocp_lock();
            mlkem_test(kv_slot0, kv_slot2);
            
            if((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS) >> 2) == 0) {
                VPRINTF(FATAL, "KV Write Error is not detected!\n");
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
            else{
                VPRINTF(LOW,"KV_WRITE_FAIL is successfully set\n");
            }

            break;

        default:
            printf("%c",0xff); //End the test
    }

    printf("%c",0xff); //End the test
    
}
