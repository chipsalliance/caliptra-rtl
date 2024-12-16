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
#include "aes.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

/*
//CASE1
Cipher = AES-256-GCM
Key = 0000000000000000000000000000000000000000000000000000000000000000
IV = 000000000000000000000000
Plaintext =
Ciphertext =
AAD =
Tag = 530f8afbc74536b9a963b4f1c4cb738b
//CASE2
Cipher = AES-256-GCM
Key = 0000000000000000000000000000000000000000000000000000000000000000
IV = 000000000000000000000000
Plaintext = 00000000000000000000000000000000
Ciphertext = cea7403d4d606b6e074ec5d3baf39d18
AAD =
Tag = d0d1c8a799996bf0265b98b5d48ab919
//CASE3
Cipher = AES-256-GCM
Key = feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308
IV = cafebabefacedbaddecaf888
Plaintext = d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39
Ciphertext = 522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662
AAD = feedfacedeadbeeffeedfacedeadbeefabaddad2
Tag = 76fc6ece0f4e1768cddf8853bb2d551b
//CASE4
Cipher = AES-128-GCM
Key = feffe9928665731c6d6a8f9467308308
IV = cafebabefacedbaddecaf888
Plaintext = d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39
Ciphertext = 42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091
AAD = feedfacedeadbeeffeedfacedeadbeefabaddad2
Tag = 5bc94fbc3221a5db94fae95ae7121a47
*/

void main() {

    aes_flow_t aes_input;
    aes_op_e op = AES_ENC;
    aes_mode_e mode = AES_GCM;
    aes_key_len_e key_len;

    const char key_str1[] = "0000000000000000000000000000000000000000000000000000000000000000";
    const char key_str2[] = "0000000000000000000000000000000000000000000000000000000000000000";
    const char key_str3[] = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    const char key_str4[] = "feffe9928665731c6d6a8f9467308308";
    uint32_t key[8];
    uint32_t key_size;
                    
    const char iv_str1[] = "000000000000000000000000";
    const char iv_str2[] = "000000000000000000000000";
    const char iv_str3[] = "cafebabefacedbaddecaf888";
    const char iv_str4[] = "cafebabefacedbaddecaf888";
    uint32_t iv[4]; 
    uint32_t iv_length;

    const char plaintext_str1[] = "";
    const char plaintext_str2[] = "00000000000000000000000000000000";
    const char plaintext_str3[] = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    const char plaintext_str4[] = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    uint32_t plaintext[32]; //arbitrary length here
    uint32_t plaintext_length;

    const char ciphertext_str1[] = "";
    const char ciphertext_str2[] = "cea7403d4d606b6e074ec5d3baf39d18";
    const char ciphertext_str3[] = "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662";
    const char ciphertext_str4[] = "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091";
    uint32_t ciphertext[32]; //arbitrary length here
    uint32_t ciphertext_length;

    const char aad_str1[] = "";
    const char aad_str2[] = "";
    const char aad_str3[] = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    const char aad_str4[] = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    uint32_t aad[32]; //arbitrary length here
    uint32_t aad_length;
                    
    const char tag_str1[] = "530f8afbc74536b9a963b4f1c4cb738b";
    const char tag_str2[] = "d0d1c8a799996bf0265b98b5d48ab919";
    const char tag_str3[] = "76fc6ece0f4e1768cddf8853bb2d551b";
    const char tag_str4[] = "5bc94fbc3221a5db94fae95ae7121a47";
    uint32_t tag[4]; 
    uint32_t tag_length;

    aes_key_t aes_key;

    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " AES-GCM smoke test !!\n"            );
    VPRINTF(LOW, "----------------------------------\n");

    //CASE1
    VPRINTF(LOW, "Test Case 1\n");
    hex_to_uint32_array(key_str1, key, &key_size);
    key_len = key_size == 8 ? AES_256 :
              key_size == 4 ? AES_128 : AES_192;
    hex_to_uint32_array(iv_str1, iv, &iv_length);
    hex_to_uint32_array(plaintext_str1, plaintext, &plaintext_length);
    hex_to_uint32_array(ciphertext_str1, ciphertext, &ciphertext_length);
    hex_to_uint32_array(aad_str1, aad, &aad_length);
    hex_to_uint32_array(tag_str1, tag, &tag_length);

    aes_key.kv_intf = FALSE;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length*4; //convert length to bytes
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length*4; //convert length to bytes
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;

    aes_flow(op, mode, key_len, aes_input);

    //CASE2
    VPRINTF(LOW, "Test Case 2\n");
    hex_to_uint32_array(key_str2, key, &key_size);
    key_len = key_size == 8 ? AES_256 :
              key_size == 4 ? AES_128 : AES_192;
    hex_to_uint32_array(iv_str2, iv, &iv_length);
    hex_to_uint32_array(plaintext_str2, plaintext, &plaintext_length);
    hex_to_uint32_array(ciphertext_str2, ciphertext, &ciphertext_length);
    hex_to_uint32_array(aad_str2, aad, &aad_length);
    hex_to_uint32_array(tag_str2, tag, &tag_length);

    aes_key.kv_intf = FALSE;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length*4; //convert length to bytes
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length*4; //convert length to bytes
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;

    aes_flow(op, mode, key_len, aes_input);

    //CASE3
    VPRINTF(LOW, "Test Case 3\n");
    hex_to_uint32_array(key_str3, key, &key_size);
    key_len = key_size == 8 ? AES_256 :
              key_size == 4 ? AES_128 : AES_192;
    hex_to_uint32_array(iv_str3, iv, &iv_length);
    hex_to_uint32_array(plaintext_str3, plaintext, &plaintext_length);
    hex_to_uint32_array(ciphertext_str3, ciphertext, &ciphertext_length);
    hex_to_uint32_array(aad_str3, aad, &aad_length);
    hex_to_uint32_array(tag_str3, tag, &tag_length);

    aes_key.kv_intf = FALSE;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length*4; //convert length to bytes
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length*4; //convert length to bytes
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;

    aes_flow(op, mode, key_len, aes_input);

    //CASE4
    VPRINTF(LOW, "Test Case 4\n");
    hex_to_uint32_array(key_str4, key, &key_size);
    key_len = key_size == 8 ? AES_256 :
              key_size == 4 ? AES_128 : AES_192;
    hex_to_uint32_array(iv_str4, iv, &iv_length);
    hex_to_uint32_array(plaintext_str4, plaintext, &plaintext_length);
    hex_to_uint32_array(ciphertext_str4, ciphertext, &ciphertext_length);
    hex_to_uint32_array(aad_str4, aad, &aad_length);
    hex_to_uint32_array(tag_str4, tag, &tag_length);

    aes_key.kv_intf = FALSE;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length*4; //convert length to bytes
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length*4; //convert length to bytes
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;

    aes_flow(op, mode, key_len, aes_input);

    SEND_STDOUT_CTRL( 0xff);
    while(1);

}