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
Cipher = AES-256-GCM
Key = feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308
IV = cafebabefacedbaddecaf888
Plaintext = d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39
Ciphertext = 522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662
AAD = feedfacedeadbeeffeedfacedeadbeefabaddad2
Tag = 76fc6ece0f4e1768cddf8853bb2d551b
*/

void main() {

    aes_flow_t aes_input;
    aes_op_e op = AES_ENC;
    aes_mode_e mode = AES_GCM;
    aes_key_len_e key_len;

    const char key_str[] = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    uint32_t key[8];
    uint32_t key_size;
    hex_to_uint32_array(key_str, key, &key_size);
    key_len = key_size == 8 ? AES_256 :
              key_size == 4 ? AES_128 : AES_192;

    VPRINTF(LOW, "Key Size: 0x%x\n", key_size);
                    
    const char iv_str[] = "cafebabefacedbaddecaf888";
    uint32_t iv[4]; 
    uint32_t iv_length;
    hex_to_uint32_array(iv_str, iv, &iv_length);

    const char plaintext_str[] = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    uint32_t plaintext[32]; //arbitrary length here
    uint32_t plaintext_length;
    hex_to_uint32_array(plaintext_str, plaintext, &plaintext_length);
                    
    const char ciphertext_str[] = "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662";
    uint32_t ciphertext[32]; //arbitrary length here
    uint32_t ciphertext_length;
    hex_to_uint32_array(ciphertext_str, ciphertext, &ciphertext_length);

    const char aad_str[] = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    uint32_t aad[32]; //arbitrary length here
    uint32_t aad_length;
    if (aad_str != "") {
        hex_to_uint32_array(aad_str, aad, &aad_length);
    }
                    
    const char tag_str[] = "76fc6ece0f4e1768cddf8853bb2d551b";
    uint32_t tag[4]; 
    uint32_t tag_length;
    hex_to_uint32_array(tag_str, tag, &tag_length);

    aes_key_t aes_key;

    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " AES-GCM smoke test !!\n"            );
    VPRINTF(LOW, "----------------------------------\n");

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