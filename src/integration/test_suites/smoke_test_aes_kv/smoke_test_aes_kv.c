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


void main() {

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
    printf("%c", key384_inject_cmd);

    hmac384_flow(hmac384_key, hmac384_block, hmac384_lfsr_seed, hmac384_tag, TRUE);
    hmac_zeroize();

    printf("----------------------------------\n");
    printf(" Run AES GCM using key in KV\n");
    printf("----------------------------------\n");

    aes_flow_t aes_input;
    aes_op_e op = AES_ENC;
    aes_mode_e mode = AES_GCM;
    aes_key_len_e key_len;

//actual value in key init d
//{db7c_04fe, 5539_e002, 7416_087f, a65d_79d4, f705_55ac, 9e01_82cb, d860_db3e, 4183_3b5a}

//{db7c04fe5539e0027416087fa65d79d4f70555ac9e0182cbd860db3e41833b5a}

//fe047cdb02e039557f081674d4795da6ac5505f7cb82019e3edb60d85a3b8341
//41833b5ad860db3e9e0182cbf70555aca65d79d47416087f5539e002db7c04fe

//db7c04fe5539e0027416087fa65d79d4f70555ac9e0182cbd860db3e41833b5a
//5a3b83413edb60d8cb82019eac5505f7d4795da67f08167402e03955fe047cdb
    const char key_str1[] = "5a3b83413edb60d8cb82019eac5505f7d4795da67f08167402e03955fe047cdb";
    const char key_str2[] = "5a3b83413edb60d8cb82019eac5505f7d4795da67f08167402e03955fe047cdb";
    const char key_str3[] = "5a3b83413edb60d8cb82019eac5505f7d4795da67f08167402e03955fe047cdb";
    const char key_str4[] = "5a3b83413edb60d8cb82019eac5505f7d4795da67f08167402e03955fe047cdb";
    uint32_t key[8];
    uint32_t key_size;

    const char iv_str1[] = "000000000000000000000000";
    const char iv_str2[] = "000000000000000000000000";
    const char iv_str3[] = "cafebabefacedbaddecaf888";
    const char iv_str4[] = "91a824c5e023283959858062";
    uint32_t iv[4]; 
    uint32_t iv_length;

    const char plaintext_str1[] = "";
    const char plaintext_str2[] = "00000000000000000000000000000000";
    const char plaintext_str3[] = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    const char plaintext_str4[] = "fc23e07b4018460279f8392e86423ecfe465b25b60382f58995ef5fa1f9ca235e4bf87112554aa0e72836831d7b5f39125df11518b8aeb1809d804419beb05ae013482213012e4ce980ddd1c58e11608b775d12b450ecace83e678c69d2c5d";
    uint32_t plaintext[32]; //arbitrary length here
    uint32_t plaintext_length;

    const char ciphertext_str1[] = "";
    const char ciphertext_str2[] = "232baa49e03f03c22d1248197abcf347";
    const char ciphertext_str3[] = "9322e63c89841dea46ec9bffa8d6e57017f441a9a48de4ce09774c7113749a2462293e5f72b6fbbf0e51cef4c4534c9439b6a596f006096a3dda05fc";
    const char ciphertext_str4[] = "a9b939f06d2302005aaf25a12b416fac91fd374753fe16c9b4dbd6d977fb569fe1278bb2d6fa72caad3b81a430535eb0bbe982e7a33213bcae8b0c1947364e2ba1ad19c673867d9bb1b3b5e8219e28b11135c8fbe12d6634e3c892c47a50e7";
    uint32_t ciphertext[32]; //arbitrary length here
    uint32_t ciphertext_length;

    const char aad_str1[] = "";
    const char aad_str2[] = "";
    const char aad_str3[] = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    const char aad_str4[] = "b3a1db2d467780480f166859e0e7aab212738b85e88237c2782496c9c503347de02f3dad6bfc671fda71a04ff1e4661767c11303daa0c36d944346d39e3e29ec63d695cdcd83b2b57181582c5ac692b13e4299ab5e86c59d09c2dc6194ebe9";
    uint32_t aad[32]; //arbitrary length here
    uint32_t aad_length;
                    
    const char tag_str1[] = "a8bea3e6f12dbcb0be716466e8f35eb8";
    const char tag_str2[] = "c48450921ce2b1a033ab31814747adcf";
    const char tag_str3[] = "c6403b3a21fff33ed60cf6590d2efe14";
    const char tag_str4[] = "e4e3906bddc4ccc3a0c6d6faec9bf3be";
    uint32_t tag[4]; 
    uint32_t tag_length;

    aes_key_t aes_key;

    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " AES-GCM smoke test\n"               );
    VPRINTF(LOW, "----------------------------------\n");

    //CASE1
    VPRINTF(LOW, "Test Case 1\n");
    hex_to_uint32_array(key_str1, key, &key_size);
    key_len = key_size == 32 ? AES_256 :
              key_size == 16 ? AES_128 : AES_192;
    hex_to_uint32_array(iv_str1, iv, &iv_length);
    hex_to_uint32_array(plaintext_str1, plaintext, &plaintext_length);
    hex_to_uint32_array(ciphertext_str1, ciphertext, &ciphertext_length);
    hex_to_uint32_array(aad_str1, aad, &aad_length);
    hex_to_uint32_array(tag_str1, tag, &tag_length);

    aes_key.kv_intf = TRUE;
    aes_key.kv_id = tag_kv_id;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;

    aes_flow(op, mode, key_len, aes_input);

    //CASE2
    VPRINTF(LOW, "Test Case 2\n");
    hex_to_uint32_array(key_str2, key, &key_size);
    key_len = key_size == 32 ? AES_256 :
              key_size == 16 ? AES_128 : AES_192;
    hex_to_uint32_array(iv_str2, iv, &iv_length);
    hex_to_uint32_array(plaintext_str2, plaintext, &plaintext_length);
    hex_to_uint32_array(ciphertext_str2, ciphertext, &ciphertext_length);
    hex_to_uint32_array(aad_str2, aad, &aad_length);
    hex_to_uint32_array(tag_str2, tag, &tag_length);

    aes_key.kv_intf = TRUE;
    aes_key.kv_id = tag_kv_id;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;

    aes_flow(op, mode, key_len, aes_input);

    //CASE3
    VPRINTF(LOW, "Test Case 3\n");
    hex_to_uint32_array(key_str3, key, &key_size);
    key_len = key_size == 32 ? AES_256 :
              key_size == 16 ? AES_128 : AES_192;
    hex_to_uint32_array(iv_str3, iv, &iv_length);
    hex_to_uint32_array(plaintext_str3, plaintext, &plaintext_length);
    hex_to_uint32_array(ciphertext_str3, ciphertext, &ciphertext_length);
    hex_to_uint32_array(aad_str3, aad, &aad_length);
    hex_to_uint32_array(tag_str3, tag, &tag_length);

    aes_key.kv_intf = TRUE;
    aes_key.kv_id = tag_kv_id;

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;

    aes_flow(op, mode, key_len, aes_input);

    //CASE4
    VPRINTF(LOW, "Test Case 4\n");
    hex_to_uint32_array(key_str4, key, &key_size);
    key_len = key_size == 32 ? AES_256 :
              key_size == 16 ? AES_128 : AES_192;
    hex_to_uint32_array(iv_str4, iv, &iv_length);
    hex_to_uint32_array(plaintext_str4, plaintext, &plaintext_length);
    hex_to_uint32_array(ciphertext_str4, ciphertext, &ciphertext_length);
    hex_to_uint32_array(aad_str4, aad, &aad_length);
    hex_to_uint32_array(tag_str4, tag, &tag_length);

    aes_key.kv_intf = TRUE;
    aes_key.kv_id = tag_kv_id;

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;

    aes_flow(op, mode, key_len, aes_input);

    SEND_STDOUT_CTRL( 0xff);
    while(1);

}