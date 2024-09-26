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
#include "ecc.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
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
    .axi_dma_error    = 0,
    .axi_dma_notif    = 0,
};

void main() {
    printf("----------------------------------\n");
    printf(" KV Smoke Test With hmac384 flow !!\n");
    printf("----------------------------------\n");

    //Call interrupt init
    init_interrupts();

    uint32_t block1[32] =   {0x00000000,
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
                             0x00000000,
                             0x00000000,
                             0x00000000};

    uint32_t block2[32] =   {0x80000000,
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
                             0x00000000,
                             0x00000000,
                             0x00000800};

    //this is a random lfsr_seed
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

    uint32_t expected_tag[12] =    {0xd0a3c3b9,
                                    0x9971a651,
                                    0x73b83116,
                                    0xaf89678f,
                                    0x3fea4219,
                                    0x40c8728b,
                                    0x3496a9ed,
                                    0x08479c4a,
                                    0xeda828b6,
                                    0x99929015,
                                    0x68d2a9c8,
                                    0xcbfd31b9}; 

    uint32_t expected_sign_r[] =   {0xB3F46F0A,
                                    0x732812F1,
                                    0x50E2D1EC,
                                    0x8B09340C,
                                    0xAA758D8C,
                                    0xD95CC1A0,
                                    0xF8CE6A17,
                                    0x646A7D61,
                                    0xAD50316A,
                                    0x05BA79D5,
                                    0xC94098EE,
                                    0xF8F9C3C3};

    uint32_t expected_sign_s[] =   {0xABB6AA85,
                                    0x5DD68A8D,
                                    0x6900D6CB,
                                    0x6477CDF7,
                                    0xE39AF7DA,
                                    0xE6A60EC2,
                                    0x65FBFF84,
                                    0xDEB82CF7,
                                    0xD5787E22,
                                    0x626E0703,
                                    0x56D1B743,
                                    0x702C57B7};

    uint32_t ecc_iv[] =            {0x3401CEFA,
                                    0xE20A7376,
                                    0x49073AC1,
                                    0xA351E329,
                                    0x26DB9ED0,
                                    0xDB6B1CFF,
                                    0xAB0493DA,
                                    0xAFB93DDD,
                                    0xD83EDEA2,
                                    0x8A803D0D,
                                    0x003B2633,
                                    0xB9D0F1BF};

    uint8_t hmackey_kv_id       = 0x2;
    uint8_t hmacblock_kv_id     = 0x1;
    uint8_t store_to_kv         = 0x1;
    uint8_t tag_kv_id           = 0x0;

    hmac_io hmac384_key;
    hmac_io hmac_block1;
    hmac_io hmac_block2;
    hmac_io hmac_lfsr_seed;
    hmac_io hmac384_tag;

    uint8_t privkey_kv_id = 0x0;

    ecc_io iv;
    ecc_io privkey;
    ecc_io msg;
    ecc_io sign_r;
    ecc_io sign_s;

    hmac384_key.kv_intf = TRUE;
    hmac384_key.kv_id = hmackey_kv_id;

    hmac_block1.kv_intf = FALSE;
    hmac_block1.kv_id = hmacblock_kv_id;
    hmac_block1.data_size = 32;
    for (int i = 0; i < hmac_block1.data_size; i++)
        hmac_block1.data[i] = block1[i];

    hmac_block2.kv_intf = FALSE;
    hmac_block2.kv_id = hmacblock_kv_id;
    hmac_block2.data_size = 32;
    for (int i = 0; i < hmac_block2.data_size; i++)
        hmac_block2.data[i] = block2[i];

    hmac_lfsr_seed.kv_intf = FALSE;
    hmac_lfsr_seed.data_size = 12;
    for (int i = 0; i < hmac_lfsr_seed.data_size; i++)
        hmac_lfsr_seed.data[i] = lfsr_seed_data[i];

    hmac384_tag.kv_intf = TRUE;
    hmac384_tag.kv_id = tag_kv_id;
    hmac384_tag.data_size = 12;
    for (int i = 0; i < hmac384_tag.data_size; i++)
        hmac384_tag.data[i] = expected_tag[i];

    
    iv.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        iv.data[i] = ecc_iv[i];
    
    msg.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        msg.data[i] = 0;

    privkey.kv_intf = TRUE;
    privkey.kv_id = privkey_kv_id;
    
    sign_r.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        sign_r.data[i] = expected_sign_r[i];
    
    sign_s.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        sign_s.data[i] = expected_sign_s[i];

    //inject hmac384_key to kv key reg (in RTL)
    uint8_t key_inject_cmd = 0xa0 + (hmac384_key.kv_id & 0x7);
    printf("%c", key_inject_cmd);

    hmac384_flow(hmac384_key, hmac_block1, hmac_lfsr_seed, hmac384_tag, TRUE);
    hmac384_flow(hmac384_key, hmac_block2, hmac_lfsr_seed, hmac384_tag, FALSE);
    hmac_zeroize();

    //sign with the generated key
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s);
    cptra_intr_rcv.ecc_notif = 0;

    ecc_zeroize();

    printf("%c",0xff); //End the test
    
}
