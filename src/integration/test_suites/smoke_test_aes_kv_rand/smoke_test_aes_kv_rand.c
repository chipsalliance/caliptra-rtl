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

/* HMAC384 test vector
    KEY = 0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
    BLOCK = 4869205468657265800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000440
    LFSR_SEED = C8F518D4F3AA1BD46ED56C1C3C9E16FB800AF504
    TAG = b6a8d5636f5c6a7224f9977dcf7ee6c7fb6d0c48cbdee9737a959796489bddbc4c5df61d5b3297b4fb68dab9f1b582c2
*/

void main() {

    // Initialize rand num generator
    VPRINTF(LOW,"\nUsing random seed = %u\n\n", (uint32_t) MY_RANDOM_SEED);
    srand((uint32_t) MY_RANDOM_SEED);

    printf("----------------------------------\n");
    printf(" Run HMAC 384 to generate a key in KV !!\n");
    printf("----------------------------------\n");

    //Call interrupt init
    init_interrupts();

    uint32_t hmac_key[12] = {0x0b0b0b0b,
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

    uint32_t hmac_block[32] =   {0x48692054,
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
    uint32_t hmac_lfsr[12] =  {0xC8F518D4,
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

    uint32_t hmac_tag[12] =   {0xb6a8d563,
                                    0x6f5c6a72,
                                    0x24f9977d,
                                    0xcf7ee6c7,
                                    0xfb6d0c48,
                                    0xcbdee973,
                                    0x7a959796,
                                    0x489bddbc,
                                    0x4c5df61d,
                                    0x5b3297b4,
                                    0xfb68dab9,
                                    0xf1b582c2}; 

    uint8_t hmackey_kv_id       = 0x2;
    uint8_t tag_kv_id           = rand() % 24; //generated key goes in a random slot

    hmac_io hmac384_key;
    hmac_io hmac384_block;
    hmac_io hmac384_lfsr_seed;
    hmac_io hmac384_tag;

    //Run once and get the tag out from API
    hmac384_key.kv_intf = FALSE;
    hmac384_key.kv_id = hmackey_kv_id;
    hmac384_key.data_size = 12;
    for (int i = 0; i < hmac384_key.data_size; i++)
        hmac384_key.data[i] = hmac_key[i];

    hmac384_block.kv_intf = FALSE;
    hmac384_block.kv_id = 0;
    hmac384_block.data_size = 32;
    for (int i = 0; i < hmac384_block.data_size; i++)
        hmac384_block.data[i] = hmac_block[i];

    hmac384_lfsr_seed.kv_intf = FALSE;
    hmac384_lfsr_seed.data_size = 12;
    for (int i = 0; i < hmac384_lfsr_seed.data_size; i++)
        hmac384_lfsr_seed.data[i] = hmac_lfsr[i];

    hmac384_tag.kv_intf = FALSE;
    hmac384_tag.kv_id = tag_kv_id;
    hmac384_tag.data_size = 12;
    for (int i = 0; i < hmac384_tag.data_size; i++)
        hmac384_tag.data[i] = hmac_tag[i];
    
    hmac384_flow(hmac384_key, hmac384_block, hmac384_lfsr_seed, hmac384_tag, TRUE, FALSE);
    hmac_zeroize();

    //Run again, but put the tag in keyvault
    hmac384_key.kv_intf = TRUE;
    hmac384_key.kv_id = hmackey_kv_id;

    hmac384_block.kv_intf = FALSE;
    hmac384_block.kv_id = 0;
    hmac384_block.data_size = 32;
    for (int i = 0; i < hmac384_block.data_size; i++)
        hmac384_block.data[i] = hmac_block[i];

    hmac384_lfsr_seed.kv_intf = FALSE;
    hmac384_lfsr_seed.data_size = 12;
    for (int i = 0; i < hmac384_lfsr_seed.data_size; i++)
        hmac384_lfsr_seed.data[i] = hmac_lfsr[i];

    hmac384_tag.kv_intf = TRUE;
    hmac384_tag.kv_id = tag_kv_id;
    hmac384_tag.data_size = 12;
    for (int i = 0; i < hmac384_tag.data_size; i++)
        hmac384_tag.data[i] = hmac_tag[i];


    //inject hmac384_key to kv key reg (in RTL)
    uint8_t key384_inject_cmd = 0xa0 + (hmac384_key.kv_id & 0x7);
    printf("%c", key384_inject_cmd);

    hmac384_flow(hmac384_key, hmac384_block, hmac384_lfsr_seed, hmac384_tag, TRUE, FALSE);
    hmac_zeroize();

    printf("----------------------------------\n");
    printf(" Reseed AES entropy interface \n");
    printf("----------------------------------\n");

    // After reseeding the state of the Trivium stream cipher primitive with
    // the seed below, it will produce the following key stream:
    //
    //   128'h7258_8CB7_89E3_8615_0DFC_DA03_BDA3_A5AE,
    //   128'h2F98_426C_4C75_C0F1_3BFB_6B2D_E2DD_6E54,
    //   128'hB8F0_AB03_51B7_F538_3C17_FAC1_E8B0_913B,
    //   128'h1838_E884_56D9_D2D0_ADCB_4B13_C510_94DE
    //
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_0, 0xB39511C4);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_1, 0xD8C04C75);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_2, 0xBC975171);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_3, 0xA15A3958);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_4, 0x0BADDAD5);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_5, 0xF21B0322);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_6, 0xC198620D);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_7, 0xEB4814D1);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_8, 0xE843DB60);

    printf("----------------------------------\n");
    printf(" Run AES using key in KV\n");
    printf("----------------------------------\n");

    aes_flow_t aes_input;
    aes_input.data_src_mode = AES_DATA_DIRECT;
    aes_input.dma_transfer_data = (dma_transfer_data_t){0};
    
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

    const char key_str[] = "b6a8d5636f5c6a7224f9977dcf7ee6c7fb6d0c48cbdee9737a959796489bddbc";

    const char iv_str128[] = "1234567891a824c5e023283959858062";
    const char iv_str96[]  = "91a824c5e02328395985806200000000";
    
    const char plaintext_str[] = "fc23e07b4018460279f8392e86423ecfe465b25b60382f58995ef5fa1f9ca235e4bf87112554aa0e72836831d7b5f39125df11518b8aeb1809d804419beb05ae013482213012e4ce980ddd1c58e11608b775d12b450ecace83e678c69d2c5d";
    const char plaintext_str_ECB[] = "fc23e07b4018460279f8392e86423ecfe465b25b60382f58995ef5fa1f9ca235e4bf87112554aa0e72836831d7b5f39125df11518b8aeb1809d804419beb05ae013482213012e4ce980ddd1c58e11608";
    const char aad_str[] = "b3a1db2d467780480f166859e0e7aab212738b85e88237c2782496c9c503347de02f3dad6bfc671fda71a04ff1e4661767c11303daa0c36d944346d39e3e29ec63d695cdcd83b2b57181582c5ac692b13e4299ab5e86c59d09c2dc6194ebe9";

    const char ciphertext_str_ECB[] = "294645de9db599fc87c89addcc4d2b2c3cbb855d32efd4ba0e885b0bd69218497822dc61260e767e0220911263b5ece06ee7d06dc4618cb014791390780931b39ac63768b28fe148c937f3fee63afa1fb2244382980b01da1d5c6b6657aa4250";
    const char ciphertext_str_CBC[] = "0d14d00d157f3381a8e85a6348fa6b3aebc79bbad0aae732f6b1376a4ba5daa60e314acb51865bb82e32cfb6d54fbc60cc83e641b5166da3913164f478d894bc0f355fb1c92a3d8d574ad88ac09f8b7f51e4c7a7c07bdecd52331172b0508325"; 
    const char ciphertext_str_CFB[] = "2ea4ca977176ebb032748adee0bafd06e6783fc7b8969b3b67ce623c7eb43a2d89034afda7bbef834a5b426d94e05474dfcc1e572c4f4e026f643215bccb9632edb37e0569a8c17e12d46d6fe6818da583a67317f69d4f8b6c3c6c92af3e94";
    const char ciphertext_str_OFB[] = "2ea4ca977176ebb032748adee0bafd06b1b92e0ee1dff90c3818d80238e7c8672a4ef70ffd28ecda2097cc39829783b67c8f0b9a334208911c84b17391470dfec8c73ebf403e14749c6013133f38759c20a33faa707f564b32b2a369a4d6a6";
    const char ciphertext_str_CTR[] = "2ea4ca977176ebb032748adee0bafd06e7dff005c5693781e9304ef63013153bf0173c4b62916cb686c11e9632abbc4f31cb6297a018e2d50c9752a6bbde1f3b78b7ba66f9fc1828b262380f8821fa5dbc8fc44985e9b77a533bb43edfa2ca";
    const char ciphertext_str_GCM[] = "f7313f90bc3394d66a39e1e560fcb8c89483aa0bdd00bc909a466f55e788d2da05e89b536356240717136ac8fe15a3e6064936bcc6ea7098da0488a5d4689ca01bd66d605c7e7ad1714916cbfb37e1ceff0182f7ca9763c463f0528565ce9e";
    const char ciphertext_str_GCM_128[] = "480f91d08e219a72dc9ea427e3a616f02c6f43dbc4b7f8e21e90c2076532b5b34e026006a03bdcb0807b80f50e83ee59fbae56418ca6df73086a66659a47d65df50416a7b8444d4618647548cd8ae84312811f1cc74cfdae10a09d17d97820";

    const char tag_str[] = "a6722f6434c72c8dbd598360d804af39";
    const char tag_str_128[] = "51a88221d6054c43ed3600482ae50245";

    //Key from KV
    aes_key.kv_intf = TRUE;
    aes_key.kv_id = tag_kv_id;
    VPRINTF(LOW, "Key Stored in KV ID %d\n", tag_kv_id);

    //Common values
    hex_to_uint32_array(key_str, key, &key_size);
    key_len = key_size == 32 ? AES_256 :
              key_size == 16 ? AES_128 : AES_192;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

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
