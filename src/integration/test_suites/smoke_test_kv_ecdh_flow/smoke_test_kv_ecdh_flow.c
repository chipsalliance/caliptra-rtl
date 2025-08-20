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
#include <stdint.h>
#include "printf.h"
#include "ecc.h"
#include "aes.h"
#include "hmac.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#ifdef MY_RANDOM_SEED
    unsigned time = (unsigned) MY_RANDOM_SEED;
#else
    unsigned time = 0;
#endif

    // const uint32_t ecc_seed[] =        {0x8FA8541C,0x82A392CA,0x74F23ED1,0xDBFD7354,0x1C596639,0x1B97EA73,0xD744B0E3,0x4B9DF59E,0xD0158063,0xE39C09A5,0xA055371E,0xDF7A5441};
    const uint32_t ecc_nonce[] =          {0x1B7EC5E5,0x48E8AAA9,0x2EC77097,0xCA9551C9,0x783CE682,0xCA18FB1E,0xDBD9F1E5,0x0BC382DB,0x8AB39496,0xC8EE423F,0x8CA105CB,0xBA7B6588};
    // const uint32_t ecc_privkey[] =     {0xF274F69D,0x163B0C9F,0x1FC3EBF4,0x292AD1C4,0xEB3CEC1C,0x5A7DDE6F,0x80C14292,0x934C2055,0xE087748D,0x0A169C77,0x2483ADEE,0x5EE70E17};
    const uint32_t expected_pubkey_x[] =  {0xD79C6D97,0x2B34A1DF,0xC916A7B6,0xE0A99B6B,0x5387B34D,0xA2187607,0xC1AD0A4D,0x1A8C2E41,0x72AB5FA5,0xD9AB58FE,0x45E43F56,0xBBB66BA4};
    const uint32_t expected_pubkey_y[] =  {0x5A736393,0x2B06B4F2,0x23BEF0B6,0x0A639026,0x5112DBBD,0x0AAE67FE,0xF26B465B,0xE935B48E,0x451E68D1,0x6F1118F2,0xB32B4C28,0x608749ED};    

    const uint32_t clinet_pubkey_x_dh[] = {0x793148F1,0X787634D5,0XDA4C6D90,0X74417D05,0XE057AB62,0XF82054D1,0X0EE6B040,0X3D627954,0X7E6A8EA9,0XD1FD7742,0X7D016FE2,0X7A8B8C66};
    const uint32_t clinet_pubkey_y_dh[] = {0xC6C41294,0X331D23E6,0XF480F4FB,0X4CD40504,0XC947392E,0X94F4C3F0,0X6B8F398B,0XB29E4236,0X8F7A6859,0X23DE3B67,0XBACED214,0XA1A1D128};
    const uint32_t ecc_sharedkey_dh[] =   {0xe7f1293c,0X6f23a532,0X89143df1,0X399e784c,0Xb71180e3,0X830c3869,0Xfd725fe7,0X8f0b6480,0X559d6344,0Xedc1aaf6,0X4b7d0701,0Xe78672d2};
    
    // HMAC_KEY   = 00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    // HMAC_BLOCK = e7f1293c6f23a53289143df1399e784cb71180e3830c3869fd725fe78f0b6480559d6344edc1aaf64b7d0701e78672d2
    // HMAC_TAG   = 1947aa97a847975f1022e42b0cc924e20d0f94821f1ceaeb151cc3341ae1b3f5a63ed1237907dfc73fa79bf0f7d8845d8429fe6441702dc604acf14670c3a580

void kv_ecc_flow(uint8_t seed_kv_id, uint8_t privkey_kv_id, uint8_t sharedkey_kv_id){
    ecc_io seed;
    ecc_io nonce;
    ecc_io iv;
    ecc_io privkey;
    ecc_io pubkey_x;
    ecc_io pubkey_y;
    ecc_io pubkey_x_dh;
    ecc_io pubkey_y_dh;
    ecc_io sharedkey_dh;

    seed.kv_intf = TRUE;
    seed.kv_id = seed_kv_id;

    nonce.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        nonce.data[i] = ecc_nonce[i];
    
    iv.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        iv.data[i] = rand() % 0xffffffff;
    
    privkey.kv_intf = TRUE;
    privkey.kv_id = privkey_kv_id;

    pubkey_x.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        pubkey_x.data[i] = expected_pubkey_x[i];
    
    pubkey_y.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        pubkey_y.data[i] = expected_pubkey_y[i];

    //inject seed to kv key reg (in RTL)
    VPRINTF(LOW, "Inject SEED into KV ID %d\n", seed_kv_id);
    lsu_write_32(STDOUT, (seed_kv_id << 8) | 0x80);

    ecc_keygen_flow(seed, nonce, iv, privkey, pubkey_x, pubkey_y);
    cptra_intr_rcv.ecc_notif = 0;
    VPRINTF(LOW, "Stored ECC Privkey into KV ID %d\n", privkey_kv_id);

    ecc_zeroize();

    pubkey_x_dh.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        pubkey_x_dh.data[i] = clinet_pubkey_x_dh[i];  

    pubkey_y_dh.kv_intf = FALSE;
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        pubkey_y_dh.data[i] = clinet_pubkey_y_dh[i];  
    
    for (int i = 0; i < ECC_INPUT_SIZE; i++)
        iv.data[i] = rand() % 0xffffffff;

    sharedkey_dh.kv_intf = TRUE;
    sharedkey_dh.kv_id = sharedkey_kv_id;

    ecc_sharedkey_flow(iv, privkey, pubkey_x_dh, pubkey_y_dh, sharedkey_dh);
    cptra_intr_rcv.ecc_notif = 0;
    VPRINTF(LOW, "Stored ECDH sharedkey into KV ID %d\n", sharedkey_kv_id);

    ecc_zeroize();
}

//******************************************************************
// HMAC(OBF_KEY , FE)
//****************************************************************** 
void kv_hmac512_flow(uint8_t block_id, uint8_t tag_id){
    VPRINTF(LOW,"\n\nHMAC flow\n");
    hmac_io hmac512_key;
    hmac_io hmac512_block;
    hmac_io hmac512_lfsr_seed;
    hmac_io hmac512_tag;

    hmac512_key.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_KEY_SIZE; i++)
        hmac512_key.data[i] = 0;

    hmac512_block.kv_intf = TRUE;
    hmac512_block.kv_id = block_id;  // ECDH sharedkey
    VPRINTF(LOW,"hmac block kv id = %x\n", hmac512_block.kv_id);

    hmac512_lfsr_seed.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_LFSR_SEED_SIZE; i++)
        hmac512_lfsr_seed.data[i] = rand() % 0xffffffff;

    hmac512_tag.kv_intf = TRUE;
    hmac512_tag.kv_id = tag_id;
    VPRINTF(LOW,"hmac tag kv id = %x\n", hmac512_tag.kv_id);

    hmac512_flow(hmac512_key, hmac512_block, hmac512_lfsr_seed, hmac512_tag, TRUE);
    hmac_zeroize();
}

kv_aes_flow(uint8_t aes_kv_id, const char *plaintext_str, const char *ciphertext_str){
    VPRINTF(LOW, "\n\nEncryption in ECB mode\n");
    aes_op_e op = AES_ENC;
    aes_mode_e mode = AES_ECB;
    aes_key_len_e key_len = AES_256;
    aes_key_t aes_key;
    aes_flow_t aes_input;

    uint32_t plaintext[32]; //arbitrary length here
    uint32_t plaintext_length;
    uint32_t ciphertext[32]; //arbitrary length here
    uint32_t ciphertext_length;

    hex_to_uint32_array(ciphertext_str, ciphertext, &ciphertext_length);
    hex_to_uint32_array(plaintext_str, plaintext, &plaintext_length);

    //Key from KV
    aes_key.kv_intf = TRUE;
    aes_key.kv_reuse_key = FALSE;
    aes_key.kv_expect_err = FALSE;
    aes_key.kv_id = aes_kv_id;
    VPRINTF(LOW, "Key Stored in KV ID %d\n", aes_key.kv_id);

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.data_src_mode = AES_DATA_DIRECT;

    //Run ENC
    aes_flow(op, mode, key_len, aes_input);

}

void main(){

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " KV Smoke Test With ECDH flow !!  \n");
    VPRINTF(LOW, "----------------------------------\n");

    //Call interrupt init
    init_interrupts();

    srand(time);

    uint8_t seed_kv_id = rand() % 0x8; 
    uint8_t privkey_kv_id = rand() % 0x17;
    uint8_t sharedkey_kv_id = rand() % 0x17;
    uint8_t hmac_tag_kv_id = rand() % 0x17;

    /* RUN ECDH to generate a shared key */
    kv_ecc_flow(seed_kv_id, privkey_kv_id, sharedkey_kv_id);
    
    // AES_KEY = e7f1293c6f23a53289143df1399e784cb71180e3830c3869fd725fe78f0b6480
    const char plaintext_str_ECB0[]  = "2ea4ca977176ebb032748adee0bafd06e7dff005c5693781e9304ef63013153bf0173c4b62916cb686c11e9632abbc4f31cb6297a018e2d50c9752a6bbde1f3b78b7ba66f9fc1828b262380f8821fa5dbc8fc44985e9b77a533bb43edfa2ca45";
    const char ciphertext_str_ECB0[] = "0aa9a935b694b29dd3d3e251084e7c4d393eebd18438b8d2dd609513eb21b039e27a20ca93a08897c4de30ce248867eac0e67fc54595a2559df10d8fb49fd7e1767410960f39e2339ebc793f55ef170e438e9e1061b1b17cbdf39dbd84e7f2db";
    /* RUN AES to encrypt a data*/
    kv_aes_flow(sharedkey_kv_id, plaintext_str_ECB0, ciphertext_str_ECB0);

    // VPRINTF(LOW, "Inject HMAC BLOCK into KV ID 4\n");
    // uint8_t hmac_block_inject_cmd = 0xb0;
    // SEND_STDOUT_CTRL(hmac_block_inject_cmd);

    /* RUN HMAC512(0, sharedkey) to generate AES key*/
    kv_hmac512_flow(sharedkey_kv_id, hmac_tag_kv_id);

    // AES_KEY = 1947aa97a847975f1022e42b0cc924e20d0f94821f1ceaeb151cc3341ae1b3f5
    const char plaintext_str_ECB1[]  = "fc23e07b4018460279f8392e86423ecfe465b25b60382f58995ef5fa1f9ca235e4bf87112554aa0e72836831d7b5f39125df11518b8aeb1809d804419beb05ae013482213012e4ce980ddd1c58e11608";
    const char ciphertext_str_ECB1[] = "a0d013ed77917d48f900d75235425543dbf8fc9f1892263f3dc1362b6af5581e5ffde30a334205baa52184d5f6295098acfbad9724bd09ba0dc52e122fe1f7b7e4e645188d431a2734da344ab616238b";
    /* RUN AES to encrypt a data*/
    kv_aes_flow(hmac_tag_kv_id, plaintext_str_ECB1, ciphertext_str_ECB1);
    
    SEND_STDOUT_CTRL(0xff); //End the test
}
