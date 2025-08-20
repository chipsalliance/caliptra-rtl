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
#include "hmac.h"
#include "aes.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

uint32_t abr_entropy[ABR_ENTROPY_SIZE] = {0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329,0x26DB9ED0,0xDB6B1CFF,0xAB0493DA,0xAFB93DDD,
                                          0xD83EDEA2,0x8A803D0D,0x003B2633,0xB9D0F1BF,0x3401CEFA,0xE20A7376,0x49073AC1,0xA351E329};

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

void main() {
    //ML-KEM
    mlkem_seed seed;
    mlkem_msg msg;
    mlkem_shared_key shared_key;
    mlkem_shared_key kv_shared_key;
    uint32_t actual_ek[MLKEM_EK_SIZE];
    uint32_t actual_dk[MLKEM_DK_SIZE];
    uint32_t actual_ciphertext[MLKEM_CIPHERTEXT_SIZE];
    uint32_t actual_sharedkey[MLKEM_SHAREDKEY_SIZE];

    //HMAC
    hmac_io hmac_block;
    hmac_io hmac_lfsr_seed;
    hmac_io hmac512_key;
    hmac_io hmac512_tag;
    uint32_t actual_tag[HMAC512_TAG_SIZE];

    //AES
    aes_flow_t aes_input = {0};
    aes_input.data_src_mode = AES_DATA_DIRECT;
    aes_input.dma_transfer_data = (dma_transfer_data_t){0};
    aes_op_e op = AES_ENC;
    aes_mode_e mode = AES_GCM;
    aes_key_len_e key_len = AES_256;
    aes_key_t aes_key_mlkem = {0};
    aes_key_t aes_key_hmac = {0};
    aes_key_t aes_key_mlkem_kv = {0};
    aes_key_t aes_key_hmac_kv = {0};
    uint32_t iv[4] = {0x00000000, 0x00000000, 0x00000000, 0x00000000};

    const char plaintext_str[] = "00000000000000000000000000000000";
    uint32_t plaintext[32]; //arbitrary length here
    uint32_t plaintext_length;

    const char ciphertext_str_mlkem[] = "08c0e3e9aeca12046dc2de8298e3771d";
    const char ciphertext_str_hmac[] = "229a0948c4b591d546caa4c6a77fbb81";
    uint32_t ciphertext_mlkem[32]; //arbitrary length here
    uint32_t ciphertext_hmac[32]; //arbitrary length here
    uint32_t ciphertext_length;
    const char tag_str_mlkem[] = "1487b617dcecc4e37728b89e3a062f00";
    const char tag_str_hmac[] = "1b232924e1e944d1e84c97bdd7276649";
    uint32_t tag_mlkem[4]; 
    uint32_t tag_hmac[4]; 
    uint32_t tag_length;



    printf("----------------------------\n");
    printf(" Running MLKEM Smoke Test !!\n");
    printf("----------------------------\n");

    //Call interrupt init
    init_interrupts();

    seed.kv_intf = FALSE;
    for (int i = 0; i < MLKEM_SEED_SIZE; i++) {
        seed.data[0][i] = 0x5a5a5a5a;
        seed.data[1][i] = 0x5a5a5a5a;
    }
    msg.kv_intf = FALSE;
    for (int i = 0; i < MLKEM_MSG_SIZE; i++) {
        msg.data[i] = 0x5a5a5a5a;
    }
    shared_key.kv_intf = FALSE;
    for (int i = 0; i < MLKEM_SHAREDKEY_SIZE; i++) {
        shared_key.data[i] = 0xa5a5a5a5;
    }
    kv_shared_key.kv_intf = TRUE;
    kv_shared_key.kv_id = 2;
    for (int i = 0; i < MLKEM_SHAREDKEY_SIZE; i++) {
        kv_shared_key.data[i] = 0;
    }

    //First - run end to end flow through API
    //Generate encaps key
    mlkem_keygen_flow(seed, abr_entropy, actual_ek, actual_dk);
    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;
    //Generate shared key and ciphertext
    mlkem_encaps_flow(actual_ek, msg, abr_entropy, actual_ciphertext, shared_key, actual_sharedkey);

    printf("Shared Key data: 0x%x\n", actual_sharedkey[0]);

    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;
    //Use shared key in HMAC to derive new key
    hmac_block.kv_intf = FALSE;
    hmac_block.data_size = 32;
    for (int i = 0; i < 8; i++) {
        uint32_t val = actual_sharedkey[i];
        hmac_block.data[i] =
            ((val >> 24) & 0x000000FF) |
            ((val >> 8)  & 0x0000FF00) |
            ((val << 8)  & 0x00FF0000) |
            ((val << 24) & 0xFF000000);
    }

    //pad bit
    hmac_block.data[8] = 0x80000000;
    //pad 0s
    for (int i = 9; i < hmac_block.data_size-1; i++) {
        hmac_block.data[i] = 0x00000000;
    }
    //pad length
    hmac_block.data[hmac_block.data_size-1] = 0x00000500;

    hmac_lfsr_seed.kv_intf = FALSE;
    hmac_lfsr_seed.data_size = 12;
    for (int i = 0; i < hmac_lfsr_seed.data_size; i++)
        hmac_lfsr_seed.data[i] = lfsr_seed_data[i];
    
    hmac512_key.kv_intf = FALSE;
    hmac512_key.data_size = 16;
    for (int i = 0; i < hmac512_key.data_size; i++)
        hmac512_key.data[i] = key512_data[i];

    hmac512_tag.kv_intf = FALSE;
    hmac512_tag.data_size = 16;
    for (int i = 0; i < hmac512_tag.data_size; i++)
        hmac512_tag.data[i] = 0x00000000;


    printf("Block data: 0x%x\n", hmac_block.data[0]);
    hmac512_flow_return(hmac512_key, hmac_block, hmac_lfsr_seed, hmac512_tag, TRUE, actual_tag);
    hmac_zeroize();

    //Use SK  in aes to generate ciphertext
    hex_to_uint32_array(plaintext_str, plaintext, &plaintext_length);
    hex_to_uint32_array(ciphertext_str_mlkem, ciphertext_mlkem, &ciphertext_length);
    hex_to_uint32_array(ciphertext_str_hmac, ciphertext_hmac, &ciphertext_length);
    hex_to_uint32_array(tag_str_mlkem, tag_mlkem, &tag_length);
    hex_to_uint32_array(tag_str_hmac, tag_hmac, &tag_length);

    aes_key_mlkem.kv_intf = FALSE;
    for (int i = 0; i < 8; i++) {
        aes_key_mlkem.key_share0[i] = actual_sharedkey[i];
        aes_key_mlkem.key_share1[i] = 0x00000000;
    }

    aes_input.key = aes_key_mlkem;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext_mlkem;
    aes_input.aad_len = 0;
    aes_input.tag = tag_mlkem;
    aes_input.iv = iv;

    aes_flow(op, mode, key_len, aes_input, AES_LITTLE_ENDIAN);


    //Use HMAC result in AES to generate ciphertext
    aes_key_hmac.kv_intf = FALSE;
    for (int i = 0; i < 8; i++) {
        uint32_t val = actual_tag[i];
        aes_key_hmac.key_share0[i] =
            ((val >> 24) & 0x000000FF) |
            ((val >> 8)  & 0x0000FF00) |
            ((val << 8)  & 0x00FF0000) |
            ((val << 24) & 0xFF000000);
        aes_key_hmac.key_share1[i] = 0x00000000;
    }

    aes_input.key = aes_key_hmac;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext_hmac;
    aes_input.aad_len = 0;
    aes_input.tag = tag_hmac;
    aes_input.iv = iv;

    aes_flow(op, mode, key_len, aes_input, AES_LITTLE_ENDIAN);

    //Now do the same flow through KeyVault
    //Decaps the same shared key into keyvault
    mlkem_keygen_decaps_flow(seed, actual_ciphertext, abr_entropy, kv_shared_key);
    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;
    //Use shared key from KV in HMAC to derive new key and store in the KV

    hmac_block.kv_intf = TRUE;
    hmac_block.kv_id = kv_shared_key.kv_id;
    hmac512_tag.kv_intf = TRUE;
    hmac512_tag.kv_id = 3;
    hmac512_tag.data_size = 16;
    hmac512_flow(hmac512_key, hmac_block, hmac_lfsr_seed, hmac512_tag, TRUE);
    hmac_zeroize();

    //Use SK in AES to generate ciphertext, compare agains the one generated before

    aes_key_mlkem_kv.kv_intf = TRUE;
    aes_key_mlkem_kv.kv_id = kv_shared_key.kv_id;

    aes_input.key = aes_key_mlkem_kv;
    aes_input.ciphertext = ciphertext_mlkem;
    aes_input.tag = tag_mlkem;

    aes_flow(op, mode, key_len, aes_input, AES_LITTLE_ENDIAN);

    //Use HMAC result in AES to generate ciphertext, compare against the one generated before
    aes_key_hmac_kv.kv_intf = TRUE;
    aes_key_hmac_kv.kv_id = hmac512_tag.kv_id;

    aes_input.key = aes_key_hmac_kv;
    aes_input.ciphertext = ciphertext_hmac;
    aes_input.tag = tag_hmac;

    aes_flow(op, mode, key_len, aes_input, AES_LITTLE_ENDIAN);


    printf("%c",0xff); //End the test
    
}
