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
#include "aes.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#ifndef MY_RANDOM_SEED
#define MY_RANDOM_SEED 17
#endif // MY_RANDOM_SEED

void main() {

    // Initialize rand num generator
    VPRINTF(LOW,"\nUsing random seed = %u\n\n", (uint32_t) MY_RANDOM_SEED);
    srand((uint32_t) MY_RANDOM_SEED);

    printf("----------------------------------\n");
    printf(" Run HMAC 384 to generate a key in KV !!\n");
    printf("----------------------------------\n");

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

    uint32_t hmac384_expected_tag[12] = {0x41833b5a, 
                                        0xd860db3e, 
                                        0x9e0182cb, 
                                        0xf70555ac, 
                                        0xa65d79d4, 
                                        0x7416087f, 
                                        0x5539e002, 
                                        0xdb7c04fe, 
                                        0x56cbe683, 
                                        0x77f4092c, 
                                        0x1d4576e8, 
                                        0x326cf662}; 

    uint8_t hmackey_kv_id       = 0x2;
    uint8_t hmacblock_kv_id     = 0x1;
    uint8_t tag_kv_id           = rand() % 24; //generated key goes in a random slot

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
    printf("%c", key384_inject_cmd);

    hmac384_flow(hmac384_key, hmac384_block, hmac384_lfsr_seed, hmac384_tag, TRUE);
    hmac_zeroize();

    printf("----------------------------------\n");
    printf(" Run AES using key in KV\n");
    printf("----------------------------------\n");

    aes_flow_t aes_input;
    aes_key_len_e key_len;
    aes_op_e op = AES_ENC;
    aes_mode_e mode = AES_GCM;

    uint32_t key[8];
    uint32_t key_size;
    uint32_t iv[4]; 
    uint32_t iv_length;
    uint32_t plaintext[32]; //arbitrary length here
    uint32_t plaintext_length;
    uint32_t ciphertext[32]; //arbitrary length here
    uint32_t ciphertext_length;
    uint32_t aad[32]; //arbitrary length here
    uint32_t aad_length;
    uint32_t tag[4]; 
    uint32_t tag_length;

    aes_key_t aes_key;

    const char key_str[] = "5a3b83413edb60d8cb82019eac5505f7d4795da67f08167402e03955fe047cdb";

    const char iv_str128[] = "1234567891a824c5e023283959858062";
    const char iv_str96[]  = "91a824c5e02328395985806200000000";
    
    const char plaintext_str[] = "fc23e07b4018460279f8392e86423ecfe465b25b60382f58995ef5fa1f9ca235e4bf87112554aa0e72836831d7b5f39125df11518b8aeb1809d804419beb05ae013482213012e4ce980ddd1c58e11608b775d12b450ecace83e678c69d2c5d";
    const char plaintext_str_ECB[] = "fc23e07b4018460279f8392e86423ecfe465b25b60382f58995ef5fa1f9ca235e4bf87112554aa0e72836831d7b5f39125df11518b8aeb1809d804419beb05ae013482213012e4ce980ddd1c58e11608";
    const char aad_str[] = "b3a1db2d467780480f166859e0e7aab212738b85e88237c2782496c9c503347de02f3dad6bfc671fda71a04ff1e4661767c11303daa0c36d944346d39e3e29ec63d695cdcd83b2b57181582c5ac692b13e4299ab5e86c59d09c2dc6194ebe9";

    const char ciphertext_str_ECB[] = "87636d91139b2c88efa132e28225d5c5f48b4592b42059af618fdbaef4dccf354a5beed1fc676bbbfa8ae27d6fc615ca2f684def6c6ebf444e16ed72253d9c01297d384bc056272c3360c5ea55c90bf8372031fe214e5a82b80f8268511b4a";
    const char ciphertext_str_CBC[] = "5bf8ecc4c32bdde86e6572ea4388b28b77ab0ac520e41ff4d1f20f6d3cf3d008c5e88a94fb91bb73da0aece34c00d77126b5bb7539fcfe3757a39b2caca8c8c2ccc651798e730647c2091c8ef6cadb81ef67692fc43a2825f15535c8661cbd"; 
    const char ciphertext_str_CFB[] = "6c9ff294091438a33690af68100b646b7fb69af4140110b493decef8dc9f5423ad81320b987436d4595783726ce8bc5d067fb24de2870d9cee1cd2f72cd7fe032e5eb98a30a3bdab0e76d082e39251215e9d3cb00f4ef80706b15c3525ee65";
    const char ciphertext_str_OFB[] = "6c9ff294091438a33690af68100b646be78b0aba1f82e6ed146aca79ea22929fcd895fa84a6a9d73b1313607f5aeabb58bcb99b3ae6cd3c505a6b445b965dcf967c7a980ba936d96ca927b063d9fe68a2cc892efd44dd6b91dd290f05587b2";
    const char ciphertext_str_CTR[] = "6c9ff294091438a33690af68100b646bba6e6373d6aceefa27eb24b2da18e7e2d8c1e81e07c477bd531dc12c78cc09a043c61bf40f03742a6ec259e86eb4bfcd1bb849379d0afc7f2637953dee84e2a7a28d37d6dbae7a17f147c3dbd09290";
    const char ciphertext_str_GCM[] = "a9b939f06d2302005aaf25a12b416fac91fd374753fe16c9b4dbd6d977fb569fe1278bb2d6fa72caad3b81a430535eb0bbe982e7a33213bcae8b0c1947364e2ba1ad19c673867d9bb1b3b5e8219e28b11135c8fbe12d6634e3c892c47a50e7";
    const char ciphertext_str_GCM_128[] = "7989165c697534e660289595e2a4ea746a732252b0fac9499e873b0af346414fe6265d4cc6f6d3de85184b194798893da01135470eae6a1427ce02a164112b74fd8a9ed0e763b4b3b15abfd0685d33f0d89b957c5b2e1984cca67cb6403b99";

    const char tag_str[] = "e4e3906bddc4ccc3a0c6d6faec9bf3be";
    const char tag_str_128[] = "62155c4c4e05cb8708f6ff6390447314";

    //Key from KV
    aes_key.kv_intf = TRUE;
    aes_key.kv_id = tag_kv_id;
    VPRINTF(LOW, "Key Stored in KV ID %d\n", tag_kv_id);

    //Common values
    hex_to_uint32_array(key_str, key, &key_size);
    key_len = key_size == 32 ? AES_256 :
              key_size == 16 ? AES_128 : AES_192;
    hex_to_uint32_array(iv_str128, iv, &iv_length);

    //full block plaintext
    hex_to_uint32_array(plaintext_str_ECB, plaintext, &plaintext_length);

    //CASE1
    VPRINTF(LOW, "Test Case 1 - ECB\n");
    op = AES_ENC;
    mode = AES_ECB;
    hex_to_uint32_array(ciphertext_str_ECB, ciphertext, &ciphertext_length);

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;
    //Run ENC
    aes_flow(op, mode, key_len, aes_input);
    op = AES_DEC;
    //Run DEC
    aes_flow(op, mode, key_len, aes_input);

    //CASE2
    VPRINTF(LOW, "Test Case 2 - CBC\n");
    op = AES_ENC;
    mode = AES_CBC;
    hex_to_uint32_array(ciphertext_str_CBC, ciphertext, &ciphertext_length);

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;
    //Run ENC
    aes_flow(op, mode, key_len, aes_input);
    op = AES_DEC;
    //Run DEC
    aes_flow(op, mode, key_len, aes_input);

    //Non-full block plaintext
    hex_to_uint32_array(plaintext_str, plaintext, &plaintext_length);

    //CASE3
    VPRINTF(LOW, "Test Case 3 - CFB\n");
    op = AES_ENC;
    mode = AES_CFB;
    hex_to_uint32_array(ciphertext_str_CFB, ciphertext, &ciphertext_length);

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;
    //Run ENC
    aes_flow(op, mode, key_len, aes_input);
    op = AES_DEC;
    //Run DEC
    aes_flow(op, mode, key_len, aes_input);

    //CASE4
    VPRINTF(LOW, "Test Case 4 - OFB\n");
    op = AES_ENC;
    mode = AES_OFB;
    hex_to_uint32_array(ciphertext_str_OFB, ciphertext, &ciphertext_length);

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;
    //Run ENC
    aes_flow(op, mode, key_len, aes_input);
    op = AES_DEC;
    //Run DEC
    aes_flow(op, mode, key_len, aes_input);

    //CASE5
    VPRINTF(LOW, "Test Case 5 - CTR\n");
    op = AES_ENC;
    mode = AES_CTR;
    hex_to_uint32_array(ciphertext_str_CTR, ciphertext, &ciphertext_length);

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;
    //Run ENC
    aes_flow(op, mode, key_len, aes_input);
    op = AES_DEC;
    //Run DEC
    aes_flow(op, mode, key_len, aes_input);

    //CASE6
    VPRINTF(LOW, "Test Case 6 - GCM 256\n");
    op = AES_ENC;
    mode = AES_GCM;
    hex_to_uint32_array(ciphertext_str_GCM, ciphertext, &ciphertext_length);
    hex_to_uint32_array(aad_str, aad, &aad_length);
    hex_to_uint32_array(iv_str96, iv, &iv_length);
    hex_to_uint32_array(tag_str, tag, &tag_length);

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;
    //Run ENC
    aes_flow(op, mode, key_len, aes_input);
    op = AES_DEC;
    //Run DEC
    aes_flow(op, mode, key_len, aes_input);

    //CASE7
    VPRINTF(LOW, "Test Case 7 - GCM 128\n");
    key_len = AES_128;
    op = AES_ENC;
    mode = AES_GCM;
    hex_to_uint32_array(ciphertext_str_GCM_128, ciphertext, &ciphertext_length);
    hex_to_uint32_array(tag_str_128, tag, &tag_length);
    hex_to_uint32_array(iv_str96, iv, &iv_length);

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;
    //Run ENC
    aes_flow(op, mode, key_len, aes_input);
    op = AES_DEC;
    //Run DEC
    aes_flow(op, mode, key_len, aes_input);


    //End Test
    SEND_STDOUT_CTRL( 0xff);
    while(1);

}