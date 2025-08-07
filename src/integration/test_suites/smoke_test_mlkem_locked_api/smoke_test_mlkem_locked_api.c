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
#include "mlkem.h"
#include <stdlib.h>

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
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

volatile caliptra_intr_received_s cptra_intr_rcv = {
    .doe_error        = 0,
    .doe_notif        = 0,
    .ecc_error        = 0,
    .ecc_notif        = 0,
    .hmac_error       = 0,
    .hmac_notif       = 0,
    .kv_error         = 0,
    .kv_notif         = 0,
    .sha512_error     = 0,
    .sha512_notif     = 0,
    .sha256_error     = 0,
    .sha256_notif     = 0,
    .qspi_error       = 0,
    .qspi_notif       = 0,
    .uart_error       = 0,
    .uart_notif       = 0,
    .i3c_error        = 0,
    .i3c_notif        = 0,
    .soc_ifc_error    = 0,
    .soc_ifc_notif    = 0,
    .sha512_acc_error = 0,
    .sha512_acc_notif = 0,
    .abr_error      = 0,
    .abr_notif      = 0,
    .axi_dma_notif    = 0,
    .axi_dma_error    = 0,
};

uint32_t abr_entropy[ABR_ENTROPY_SIZE] = {0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329,0x26DB9ED0,0xDB6B1CFF,0xAB0493DA,0xAFB93DDD,
                                          0xD83EDEA2,0x8A803D0D,0x003B2633,0xB9D0F1BF,0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329};

                                          
void main() {
    printf("--------------------------------------------\n");
    printf(" KV Smoke Test With MLKEM Locked API flow !!\n");
    printf("--------------------------------------------\n");

    /* Intializes random number generator */  //TODO    
    srand(time);

    //Call interrupt init
    init_interrupts();
    mlkem_seed seed;
    mlkem_msg msg;
    mlkem_shared_key shared_key;
    uint32_t mlkem_ek[MLKEM_EK_SIZE];
    uint32_t mlkem_dk[MLKEM_DK_SIZE];
    uint32_t mlkem_ciphertext[MLKEM_CIPHERTEXT_SIZE];
    uint32_t actual_ek[MLKEM_EK_SIZE];
    uint32_t actual_dk[MLKEM_DK_SIZE];
    uint32_t actual_ciphertext[MLKEM_CIPHERTEXT_SIZE];
    uint32_t actual_sharedkey[MLKEM_SHAREDKEY_SIZE];

    shared_key.kv_intf = TRUE;
    shared_key.kv_id = 2;
    
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    volatile uint32_t * status_ptr;
    uint8_t fail_cmd = 0x1;

    seed.kv_intf = TRUE;
    seed.kv_id = 8;

    msg.kv_intf = TRUE;
    msg.kv_id = 2;

    lsu_write_32(STDOUT, (seed.kv_id << 8) | 0xb1); //Inject MLKEM SEED vectors
    lsu_write_32(STDOUT, (msg.kv_id << 8) | 0xb2); //Inject MLKEM MSG vectors

    //Generate vectors
    mlkem_keygen_flow(seed, abr_entropy, actual_ek, actual_dk);
    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    mlkem_encaps_flow(actual_ek, msg, abr_entropy, actual_ciphertext, shared_key, actual_sharedkey);
    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    
    
    printf("Waiting for mlkem status ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

    printf("\nTry fw read during kv access\n");

    reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SEED_D_0;
    offset = 0;
    // Program MLKEM_SEED Read with 12 dwords from seed_kv_id
    lsu_write_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_CTRL, (ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_MASK |
                                                        ((seed.kv_id << ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_MASK)));
    
    while (offset < MLKEM_SEED_SIZE) {
        if (*reg_ptr != 0) {
            printf("At offset [%d], mlkem seed data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", *reg_ptr);
            printf("Expected data: 0x%x\n", 0);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }
    
    mlkem_zeroize();

    printf("\nTry fw read by asserting zeroize during kv access\n");
    printf("%c",0xb4); //inject zeroize during kv access

    reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SEED_D_0;
    offset = 0;
    // Program MLKEM_SEED Read with 12 dwords from seed_kv_id
    lsu_write_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_CTRL, (ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_MASK |
                                                        ((seed.kv_id << ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_MASK)));
        
    while (offset < MLKEM_SEED_SIZE) {
        if (*reg_ptr != 0) {
            printf("At offset [%d], mlkem seed data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", *reg_ptr);
            printf("Expected data: 0x%x\n", 0);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }
    
    mlkem_zeroize();

    printf("\nTry fw read by asserting zeroize during kv access\n");
    printf("%c",0xb4); //inject zeroize during kv access
    
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_MSG_BASE_ADDR;
    offset = 0;
    // Program MLKEM_SEED Read with 12 dwords from seed_kv_id
    lsu_write_32(CLP_ABR_REG_KV_MLKEM_MSG_RD_CTRL, (ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_EN_MASK |
                                                    ((msg.kv_id << ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_MASK)));
    
    while (offset < MLKEM_MSG_SIZE) {
        if (*reg_ptr != 0) {
            printf("At offset [%d], mlkem msg data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", *reg_ptr);
            printf("Expected data: 0x%x\n", 0);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }
    
    mlkem_zeroize();
    
    printf("\nProgram MLKEM_SEED\n");
    // Program MLKEM_SEED Read with 12 dwords from seed_kv_id
    lsu_write_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_CTRL, (ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_MASK |
                                                        ((seed.kv_id << ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_MASK)));

    // Check that MLKEM SEED is loaded
    while((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_STATUS) & ABR_REG_KV_MLKEM_SEED_RD_STATUS_VALID_MASK) == 0);

    // Program MLKEM Ciphertext
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_CIPHERTEXT_BASE_ADDR, actual_ciphertext, MLKEM_CIPHERTEXT_SIZE);

    //program KV destination for shared key
    //if we want to store the results into kv
    if (shared_key.kv_intf){
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL, ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_EN_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_AES_KEY_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK |
                                                      ((shared_key.kv_id << ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_LOW) & ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_MASK));
    }
    
    status_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_STATUS;

    // Enable MLKEM KEYGEN DECAPS flow
    printf("[MLKEM KeyGen Decaps] Sending command\n");
    lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_KEYGEN_DECAPS);


    printf("Try to Load Locked ek data from MLKEM\n");
    while (*status_ptr == 0){
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_ENCAPS_KEY_BASE_ADDR;
        offset = 0;
        while (offset < MLKEM_EK_SIZE) {
            if ((*reg_ptr != 0) & (*status_ptr == 0)) {
                printf("At offset [%d], mlkem_ek data mismatch!\n", offset);
                printf("Actual   data: 0x%x\n", *reg_ptr);
                printf("Expected data: 0x%x\n", 0);
                printf("%c", fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }

    // wait for MLKEM process to be done
    wait_for_mlkem_intr();

    // Read the data back from MLKEM register
    printf("Try to Load Locked SEED data from MLKEM\n");
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SEED_D_0;
    offset = 0;
    while (offset < MLKEM_SEED_SIZE) {
        if (*reg_ptr != 0) {
            printf("At offset [%d], mlkem seed data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", *reg_ptr);
            printf("Expected data: 0x%x\n", 0);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

    // Read the data back from MLKEM register
    printf("Try to Load Locked decaps key data from MLKEM\n");
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_DECAPS_KEY_BASE_ADDR;
    offset = 0;
    while (offset < MLKEM_DK_SIZE) {
        if (*reg_ptr != 0) {
            printf("At offset [%d], mlkem decaps key mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", *reg_ptr);
            printf("Expected data: 0x%x\n", 0);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

    printf("[MLKEM] Starting zeroize\n");
    lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, (1 << ABR_REG_MLKEM_CTRL_ZEROIZE_LOW) & ABR_REG_MLKEM_CTRL_ZEROIZE_MASK);

    // Read the data back from MLKEM register
    printf("Try to Load zeroized Ciphertext data from MLKEM\n");
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_CIPHERTEXT_BASE_ADDR;
    offset = 0;
    while (offset < MLKEM_CIPHERTEXT_SIZE) {
        *reg_ptr = 0xFF;
        if ((*status_ptr == 0) && (*reg_ptr != 0)) {
            printf("At offset [%d], mlkem_ciphertext mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", *reg_ptr);
            printf("Expected data: 0x%x\n", 0);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

    cptra_intr_rcv.abr_notif = 0;

    printf("%c",0xff); //End the test
    
}


