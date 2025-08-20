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

enum Engine {
    ECC,
    MLDSA,
    MLKEM,
    AES,
    HMAC,
    DOE,
    NUM_ENGINES
};


uint8_t is_high_latency(enum Engine e) {
    return (e == ECC || e == MLDSA || e == MLKEM);
}

// Stub for your hardware operations
void run_engine(enum Engine eng) {
    switch (eng) {
        case ECC:
            lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING | 
                        ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK));
            break;
        case MLDSA:
            lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN);
            break;
        case MLKEM:
            lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_KEYGEN);
            break;
        case AES:
            aes_ECB_run();
            break;
        case HMAC:
            lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK |
                                                    (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));
            break;
        case DOE:
            lsu_write_32(CLP_DOE_REG_DOE_CTRL, DOE_UDS << DOE_REG_DOE_CTRL_CMD_LOW);
            break;
        default:
            break;
    }
}

const char* engine_name(enum Engine e) {
    switch (e) {
        case ECC:   return "ECC";
        case MLDSA: return "MLDSA";
        case MLKEM: return "MLKEM";
        case AES:   return "AES";
        case HMAC:  return "HMAC";
        case DOE:   return "DOE";
        default:    return "UNKNOWN";
    }
}

void aes_ECB_run(){
    uint8_t aes_key_id = 5;
    aes_flow_t aes_input;
    aes_input.data_src_mode = AES_DATA_DIRECT;
    aes_input.dma_transfer_data = (dma_transfer_data_t){0};
    
    aes_key_len_e key_len;
    aes_op_e op = AES_ENC;
    aes_mode_e mode = AES_ECB;

    uint32_t key[8];
    uint32_t key_size;
    uint32_t iv[4]; 
    uint32_t iv_length;
    uint32_t plaintext[32]; //arbitrary length here
    uint32_t plaintext_length;
    uint32_t ciphertext[32]; //arbitrary length here
    uint32_t ciphertext_length;

    aes_key_t aes_key;

    const char key_str[] = "b6a8d5636f5c6a7224f9977dcf7ee6c7fb6d0c48cbdee9737a959796489bddbc";
    const char iv_str128[] = "1234567891a824c5e023283959858062";    
    const char plaintext_str_ECB[] = "fc23e07b4018460279f8392e86423ecf";
    const char ciphertext_str_ECB[] = "294645de9db599fc87c89addcc4d2b2c";

    //Key from KV
    aes_key.kv_intf = TRUE;
    aes_key.kv_id = aes_key_id;

    //Common values
    hex_to_uint32_array(key_str, key, &key_size);
    key_len = key_size == 32 ? AES_256 :
              key_size == 16 ? AES_128 : AES_192;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    hex_to_uint32_array(iv_str128, iv, &iv_length);
    hex_to_uint32_array(plaintext_str_ECB, plaintext, &plaintext_length);
    hex_to_uint32_array(ciphertext_str_ECB, ciphertext, &ciphertext_length);

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.iv = iv;     

    uint8_t fail_cmd = 0x1;
    uint32_t partial_text_len = aes_input.text_len%16;
    uint32_t num_blocks_text = (partial_text_len == 0) ? aes_input.text_len/16 : aes_input.text_len/16 +1;
    uint32_t length;

    // wait for AES to be idle
    aes_wait_idle();

    //Load key from keyvault if expected
    if (aes_input.key.kv_intf){
        // Wait for KV read logic to be idle
        while((lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS) & AES_CLP_REG_AES_KV_RD_KEY_STATUS_READY_MASK) == 0);

        // Program KEY Read
        lsu_write_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL, AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                        ((aes_input.key.kv_id << AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

        // Check that AES key is loaded
        while((lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS) & AES_CLP_REG_AES_KV_RD_KEY_STATUS_VALID_MASK) == 0);
    }

    uint32_t aes_ctrl =
        ((op << AES_REG_CTRL_SHADOWED_OPERATION_LOW) & AES_REG_CTRL_SHADOWED_OPERATION_MASK) |
        ((mode << AES_REG_CTRL_SHADOWED_MODE_LOW) & AES_REG_CTRL_SHADOWED_MODE_MASK) |
        ((key_len << AES_REG_CTRL_SHADOWED_KEY_LEN_LOW) & AES_REG_CTRL_SHADOWED_KEY_LEN_MASK) |
        (0x0 << AES_REG_CTRL_SHADOWED_MANUAL_OPERATION_LOW) |
        (aes_input.key.kv_intf << AES_REG_CTRL_SHADOWED_SIDELOAD_LOW);
    
    //write shadowed ctrl twice
    lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, aes_ctrl);
    lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, aes_ctrl);

    aes_wait_idle();

    //Write the key
    if (!aes_input.key.kv_intf) {
        // Load key from hw_data and write to AES
        VPRINTF(LOW, "Load Key data to AES\n");
        for (int j = 0; j < 8; j++) {
            lsu_write_32(CLP_AES_REG_KEY_SHARE0_0 + j * 4, aes_input.key.key_share0[j]);
            lsu_write_32(CLP_AES_REG_KEY_SHARE1_0 + j * 4, aes_input.key.key_share1[j]);
        }
    }

    aes_wait_idle();

    for (int j = 0; j < 4; j++) {
        lsu_write_32((CLP_AES_REG_IV_0 + j * 4), aes_input.iv[j]);
    }

    if (aes_input.text_len > 0) { 
        // For Data Block I=0,...,N-1
        num_blocks_text = 1;
        for (int i = 0; i < num_blocks_text; i++) {
            
            // Wait for INPUT_READY
            while((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_INPUT_READY_MASK) == 0);

            // Write Input Data Block.
            VPRINTF(LOW, "Write AES Input Data Block %d\n", i);
            for (int j = 0; j < 4; j++) {
            if (op == AES_ENC) {
                VPRINTF(LOW, "Write In Data: 0x%x\n", aes_input.plaintext[j+i*4]);
                lsu_write_32((CLP_AES_REG_DATA_IN_0 + j * 4), aes_input.plaintext[j+i*4]);
            } else if (op == AES_DEC) {
                VPRINTF(LOW, "Write In Data: 0x%x\n", aes_input.ciphertext[j+i*4]);
                lsu_write_32((CLP_AES_REG_DATA_IN_0 + j * 4), aes_input.ciphertext[j+i*4]);
            }
            }                      
        
        }
    }

}

void main(){

    printf("----------------------------------\n");
    printf(" KV Smoke Test Parallel Access !!!\n");
    printf("----------------------------------\n");

    //Call interrupt init
    init_interrupts();

    /* Intializes random number generator */  //TODO    
    srand(time);

    uint8_t doe_fe_dest_id = 1;
    uint8_t hmac_key_id = 2;
    uint8_t hmac_tag_id = 5;
    uint8_t mldsa_seed_id = 6;
    uint8_t mlkem_seed_id = 3;
    uint8_t aes_key_id = 10;

    uint32_t iv_data_uds[]  = {0x2eb94297,0x77285196,0x3dd39a1e,0xb95d438f};
    
    printf("DOE Preparation **************\n");
    uint32_t* reg_ptr;
    uint8_t offset;
    printf("   Writing UDS IV\n");
    reg_ptr = (uint32_t*) CLP_DOE_REG_DOE_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_DOE_REG_DOE_IV_3) {
        *reg_ptr++ = iv_data_uds[offset++];
    }

    printf("ECC Preparation **************\n");
    //inject seed to kv key reg (in RTL)
    printf("   Inject randomized PRIVKEY into KV slot and MSG into SHA512 digest\n");
    printf("%c", 0x91);
    
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
    
    printf("HMAC Preparation **************\n");

    uint32_t hmac512_block   [HMAC512_BLOCK_SIZE];
    uint32_t hmac512_lfsr_seed [HMAC512_LFSR_SEED_SIZE];

    for (int i = 0; i < HMAC512_BLOCK_SIZE; i++)
        hmac512_block[i] = 0;
    
    for (int i = 0; i < HMAC512_LFSR_SEED_SIZE; i++)
        hmac512_lfsr_seed[i] = rand() % 0xffffffff;

    write_hmac_reg((uint32_t*) CLP_HMAC_REG_HMAC512_BLOCK_0, hmac512_block, HMAC512_BLOCK_SIZE);
    write_hmac_reg((uint32_t*) CLP_HMAC_REG_HMAC512_LFSR_SEED_0, hmac512_lfsr_seed, HMAC512_LFSR_SEED_SIZE);

    VPRINTF(LOW,"   Set HMAC TAG destination to KV slot = %x\n", hmac_tag_id);
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL, HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
                                                HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                ((hmac_tag_id << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) & HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK));
    
    //inject hmac512_key to kv key reg (in RTL)
    lsu_write_32(STDOUT, (hmac_key_id << 8) | 0xa9); 

    VPRINTF(LOW,"   Load Key data to HMAC from KV slot = %x\n", hmac_key_id);
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                    ((hmac_key_id << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

    
    printf("MLDSA Preparation **************\n");
    //inject mldsa seed to kv key reg (in RTL)
    uint8_t mldsa_seed_inject_cmd = 0xc0 + (mldsa_seed_id & 0x7);
    printf("%c", mldsa_seed_inject_cmd);

    lsu_write_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_CTRL, (ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_EN_MASK |
                                                    ((mldsa_seed_id << ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_MASK)));

    printf("MLKEM Preparation **************\n");
    //inject mldsa seed to kv key reg (in RTL)
    lsu_write_32(STDOUT, (mlkem_seed_id << 8) | 0xb1);
    printf("%c", mlkem_seed_id);

    lsu_write_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_CTRL, (ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_MASK |
                                                    ((mlkem_seed_id << ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_MASK)));

    printf("AES Preparation **************\n");
    while((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_IDLE_MASK) == 0);
    //inject aes key to kv key reg (in RTL)
    lsu_write_32(STDOUT, (aes_key_id << 8) | 0x9f); //Inject AES key vectors into KV 10


    if ((lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL) & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_MASK) != 0){
        printf("\nFATAL error is already set.\n");
        printf("%c", 0x1);
        while(1);
    }

    uint8_t num_engines = (rand() % 2) + 2;

    enum Engine engines[NUM_ENGINES] = {ECC, MLDSA, MLKEM, AES, HMAC, DOE};
    for (int i = NUM_ENGINES - 1; i > 0; i--) {
        int j = rand() % (i + 1);
        enum Engine tmp = engines[i];
        engines[i] = engines[j];
        engines[j] = tmp;
    }

    // Pick the first N engines
    enum Engine chosen[3];
    for (int i = 0; i < num_engines; i++) {
        chosen[i] = engines[i];
    }

    VPRINTF(LOW, "Running %d engines:\n", num_engines);
    for (int i = 0; i < num_engines; i++) {
        printf("%s%s", engine_name(chosen[i]), (i == num_engines - 1) ? "\n" : ", ");
    }

    // Step 1: Run high-latency engines first
    for (int i = 0; i < num_engines; i++) {
        if (is_high_latency(chosen[i])) {
            run_engine(chosen[i]);
        }
    }

    // Step 2: Run the rest
    for (int i = 0; i < num_engines; i++) {
        if (!is_high_latency(chosen[i])) {
            run_engine(chosen[i]);
        }
    }


    // switch (rst_count){
    //     case 0:
    //         VPRINTF(LOW,"Running ECC and HMAC core\n");
    //         lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING | 
    //                     ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK));
    //         lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK |
    //                                                 (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));
    //         break;
    //     case 1:
    //         VPRINTF(LOW,"Running ECC and MLDSA core\n");
    //         lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING | 
    //                     ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK));
    //         lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN);
    //         break;
    //     case 2:
    //         VPRINTF(LOW,"Running MLKEM and HMAC core\n");
    //         lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_KEYGEN);
    //         lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK |
    //                                                 (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));
    //         break;
    //     case 3:
    //         VPRINTF(LOW,"Running MLKEM and DOE core\n");
    //         lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_KEYGEN);
    //         lsu_write_32(CLP_DOE_REG_DOE_CTRL, DOE_UDS << DOE_REG_DOE_CTRL_CMD_LOW);
    //         break;
    //     case 4:
    //         VPRINTF(LOW,"Running HMAC and DOE core\n");
    //         lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK |
    //                                                 (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));
    //         lsu_write_32(CLP_DOE_REG_DOE_CTRL, DOE_UDS << DOE_REG_DOE_CTRL_CMD_LOW);
    //         break;
    //     case 5:
    //         VPRINTF(LOW,"Running AES and MLDSA core\n");
    //         lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN);            
    //         aes_ECB_run(aes_key_id);
    //         break;
    //     case 6:
    //         VPRINTF(LOW,"Running AES and ECC core\n");
    //         lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING | 
    //                     ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK));
            
    //         aes_ECB_run(aes_key_id);
    //         break;
    //     default:
    //         printf("%c",0xff); //End the test
    // }
    
    if ((lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL) & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_MASK) == 0){
        printf("\nParallel Crypto error is not detected for test: %0d\n", rst_count);
        printf("%c", 0x1);
        while(1);
    }
    else {
        printf("\nParallel Crypto is successfully detected for test: %0d\n", rst_count);
    }

    // if (rst_count < 6){
    //     rst_count++;
    //     //Issue cold reset
    //     SEND_STDOUT_CTRL(0xf5);
    // }
    // else
        printf("%c",0xff); //End the test

}
