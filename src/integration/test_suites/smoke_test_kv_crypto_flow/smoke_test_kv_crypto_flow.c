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
#include <stdlib.h>

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t rst_count __attribute__((section(".dccm.persistent"))) = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#ifdef RNG_SEED
    unsigned time = (unsigned) RNG_SEED;
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
};

/* DOE test vector
    IV_UDS  = 2eb94297772851963dd39a1eb95d438f
    UDS     = dff9f0021e1ab0bda2781e1a709cafdb341953bdbd6836d9c1ea520a6043041daf7218b19ce98302a5f8f95a6b51f5c1
    IV_FE   = 144516246a752c329056d884daf3c89d
    FE      = cfc155a3967de347f58fa2e8bbeb4183d6d32f7427155e6ab39cddf2e627c572
*/

/* HMAC384 test vector
    KEY =   dff9f0021e1ab0bda2781e1a709cafdb341953bdbd6836d9c1ea520a6043041daf7218b19ce98302a5f8f95a6b51f5c1
    BLOCK = cfc155a3967de347f58fa2e8bbeb4183d6d32f7427155e6ab39cddf2e627c572800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000500
    LFSR_SEED = C8F518D4F3AA1BD46ED56C1C3C9E16FB800AF504
    TAG = AF2799D01F135A1EF963DFD059F99604B0E33BE1CA38E70C9B2C10731F17173AD8F2681CA64AEAC5F5A4B368457460DC
*/

/* ECC test vector:
    MSG      = BEB065251497FCE1D4C430928BC09E147B250CF325A40258784262F6858B8056D68C6A23D4CC5CBDCEAD7EBF8F6A97E6
    PRIVKEY  = 11F76A67B9855B59969D52CEA8A8FC50E5B3593C21521060CBA024FEAD80735AB825F3933B3454835755AB52535F5DDD
    PUBKEY_X = FD7AF45F67D9C371B75E8AB6DEC6E5B5D7394102B27C4461DEC50209F06DE791F90E0587ED93DA6203D3797192DA0C21
    PUBKEY_Y = 4EEA9748933318742AC8A06EE3557B9189E15FCC1DB75754F26CA763711440B7AD9A08F9C15788875D39B31AD0CD2D83
    SEED     = AF2799D01F135A1EF963DFD059F99604B0E33BE1CA38E70C9B2C10731F17173AD8F2681CA64AEAC5F5A4B368457460DC
    NONCE    = 1B7EC5E548E8AAA92EC77097CA9551C9783CE682CA18FB1EDBD9F1E50BC382DB8AB39496C8EE423F8CA105CBBA7B6588
    SIGN_R   = 2F404A52A35A4BE85059D38BE429D2221A4D57EBCA4D268054691CB4EB9845CB62D94F1FBE2C3EDFCCD79C1FD10505B1
    SIGN_S   = 09FD9A770EA13FB57150DFB7539715B66C14A6F558346A4CD303950F7D171A580C1212BDA7DF30C56269A5A13A6A32A7
    IV       = BD372F61CBEC31CD5F07A7380B0CC2D10E53A51B1B9D36AE2B437C65D5ACAC1E4B7ABC204A25E423033CA6C96E9C6BC1

*/

//******************************************************************
// DOE(IV_OBF, IV_FE)
//****************************************************************** 
void kv_doe(uint8_t doe_fe_dest_id){
    
    uint32_t iv_data_uds[]  = {0x2eb94297,0x77285196,0x3dd39a1e,0xb95d438f};
    uint32_t iv_data_fe[]   = {0x14451624,0x6a752c32,0x9056d884,0xdaf3c89d};

    doe_init(iv_data_uds, iv_data_fe, doe_fe_dest_id);
    VPRINTF(LOW,"doe_fe kv id = %x\n", doe_fe_dest_id);

    doe_clear_secrets();
}

//******************************************************************
// HMAC(OBF_KEY , FE)
//****************************************************************** 
void kv_hmac(uint8_t key_id, uint8_t block_id, uint8_t tag_id){
    
    hmac_io hmac_key;
    hmac_io hmac_block;
    hmac_io hmac_lfsr_seed;
    hmac_io hmac_tag;

        
    uint32_t key_data[]     = {0xdff9f002,0x1e1ab0bd,0xa2781e1a,0x709cafdb,0x341953bd,0xbd6836d9,0xc1ea520a,0x6043041d,0xaf7218b1,0x9ce98302,0xa5f8f95a,0x6b51f5c1};
    uint32_t block[]        = {0xcfc155a3,0x967de347,0xf58fa2e8,0xbbeb4183,0xd6d32f74,0x27155e6a,0xb39cddf2,0xe627c572,0x80000000,0x00000000,0x00000000,0x00000000,
                               0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,
                               0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000500};    
    uint32_t lfsr_seed_data[]={0xC8F518D4,0xF3AA1BD4,0x6ED56C1C,0x3C9E16FB,0x800AF504}; //this is a random lfsr_seed 160-bit
    uint32_t expected_tag[] = {0xaf2799d0,0x1f135a1e,0xf963dfd0,0x59f99604,0xb0e33be1,0xca38e70c,0x9b2c1073,0x1f17173a,0xd8f2681c,0xa64aeac5,0xf5a4b368,0x457460dc};

    hmac_key.kv_intf = TRUE;
    hmac_key.kv_id = key_id; // UDS from DOE
    VPRINTF(LOW,"hmac key kv id = %x\n", hmac_key.kv_id);

    hmac_block.kv_intf = TRUE;
    hmac_block.kv_id = block_id;  // FE from DOE
    VPRINTF(LOW,"hmac block kv id = %x\n", hmac_block.kv_id);

    hmac_lfsr_seed.kv_intf = FALSE;
    hmac_lfsr_seed.data_size = 5;
    for (int i = 0; i < hmac_lfsr_seed.data_size; i++)
        hmac_lfsr_seed.data[i] = rand() % 0xffffffff;

    hmac_tag.kv_intf = TRUE;
    hmac_tag.kv_id = tag_id;
    /*hmac_tag.data_size = 12;
    for (int i = 0; i < hmac_tag.data_size; i++)
        hmac_tag.data[i] = expected_tag[i];
    VPRINTF(LOW,"hmac tag kv id = %x\n", hmac_tag.kv_id);
    */

    //inject hmac_key to kv key reg (in RTL)
    //uint8_t key_inject_cmd = 0xa0 + (hmac_key.kv_id & 0x1f);
    //printf("%c", key_inject_cmd);

    hmac_flow(hmac_key, hmac_block, hmac_lfsr_seed, hmac_tag);
    //printf("%c", 0x1);
}

void kv_ecc(uint8_t seed_id, uint8_t privkey_id){

    ecc_io seed;
    ecc_io nonce;
    ecc_io iv;
    ecc_io privkey;
    ecc_io pubkey_x;
    ecc_io pubkey_y;
    ecc_io msg;
    ecc_io sign_r;
    ecc_io sign_s;

    uint32_t ecc_msg[]      = {0xBEB06525,0x1497FCE1,0xD4C43092,0x8BC09E14,0x7B250CF3,0x25A40258,0x784262F6,0x858B8056,0xD68C6A23,0xD4CC5CBD,0xCEAD7EBF,0x8F6A97E6};
    uint32_t ecc_privkey[]  = {0x11F76A67,0xB9855B59,0x969D52CE,0xA8A8FC50,0xE5B3593C,0x21521060,0xCBA024FE,0xAD80735A,0xB825F393,0x3B345483,0x5755AB52,0x535F5DDD};
    uint32_t ecc_pubkey_x[] = {0xFD7AF45F,0x67D9C371,0xB75E8AB6,0xDEC6E5B5,0xD7394102,0xB27C4461,0xDEC50209,0xF06DE791,0xF90E0587,0xED93DA62,0x03D37971,0x92DA0C21};
    uint32_t ecc_pubkey_y[] = {0x4EEA9748,0x93331874,0x2AC8A06E,0xE3557B91,0x89E15FCC,0x1DB75754,0xF26CA763,0x711440B7,0xAD9A08F9,0xC1578887,0x5D39B31A,0xD0CD2D83};
    uint32_t ecc_seed[]     = {0xAF2799D0,0x1F135A1E,0xF963DFD0,0x59F99604,0xB0E33BE1,0xCA38E70C,0x9B2C1073,0x1F17173A,0xD8F2681C,0xA64AEAC5,0xF5A4B368,0x457460DC};
    uint32_t ecc_nonce[]    = {0x1B7EC5E5,0x48E8AAA9,0x2EC77097,0xCA9551C9,0x783CE682,0xCA18FB1E,0xDBD9F1E5,0x0BC382DB,0x8AB39496,0xC8EE423F,0x8CA105CB,0xBA7B6588};
    uint32_t ecc_sign_r[]   = {0x2F404A52,0xA35A4BE8,0x5059D38B,0xE429D222,0x1A4D57EB,0xCA4D2680,0x54691CB4,0xEB9845CB,0x62D94F1F,0xBE2C3EDF,0xCCD79C1F,0xD10505B1};
    uint32_t ecc_sign_s[]   = {0x09FD9A77,0x0EA13FB5,0x7150DFB7,0x539715B6,0x6C14A6F5,0x58346A4C,0xD303950F,0x7D171A58,0x0C1212BD,0xA7DF30C5,0x6269A5A1,0x3A6A32A7};
    uint32_t ecc_iv[]       = {0xBD372F61,0xCBEC31CD,0x5F07A738,0x0B0CC2D1,0x0E53A51B,0x1B9D36AE,0x2B437C65,0xD5ACAC1E,0x4B7ABC20,0x4A25E423,0x033CA6C9,0x6E9C6BC1};

    //******************************************************************
    // ECC_KEYGEN(HMAC_TAG, NONCE, IV)
    //******************************************************************     

    seed.kv_intf = TRUE;
    seed.kv_id = seed_id;
    VPRINTF(LOW,"ecc seed kv id = %x\n", seed.kv_id);

    nonce.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        nonce.data[i] = ecc_nonce[i];
    
    iv.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        iv.data[i] = ecc_iv[i];

    privkey.kv_intf = TRUE;
    privkey.kv_id = privkey_id;
    VPRINTF(LOW,"ecc privkey kv id = %x\n", privkey.kv_id);

    pubkey_x.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        pubkey_x.data[i] = ecc_pubkey_x[i];
    
    pubkey_y.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        pubkey_y.data[i] = ecc_pubkey_y[i];

    ecc_keygen_flow(seed, nonce, iv, privkey, pubkey_x, pubkey_y);
    cptra_intr_rcv.ecc_notif = 0;

    //******************************************************************
    // ECC_SIGN(MSG, PRIVKEY, IV)
    //******************************************************************    
    privkey.kv_intf = TRUE;
    privkey.kv_id = privkey.kv_id; 
    VPRINTF(LOW,"ecc privkey kv id = %x\n", privkey.kv_id);

    msg.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        msg.data[i] = ecc_msg[i];
    
    iv.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        iv.data[i] = rand() % 0xffffffff;

    sign_r.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        sign_r.data[i] = ecc_sign_r[i];
    
    sign_s.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        sign_s.data[i] = ecc_sign_s[i];
    
    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s);
    cptra_intr_rcv.ecc_notif = 0;
}

void random_generator(uint8_t *fe_id, uint8_t *uds_id, uint8_t *privkey_id, uint8_t *cdi_id){

    /* Intializes random number generator */  //TODO    
    srand(time);

    do {
        *fe_id = rand() & 0x1f;   // FE kv id
    } while(*fe_id == 0);

    do {
        *uds_id = rand() & 0x1f; 
    } while((*uds_id == 0) | (*uds_id == *fe_id));
    
    do {
        *cdi_id = rand() & 0x1f;
    } while((*cdi_id == 0) | (*cdi_id == *fe_id) | (*cdi_id == *uds_id));

    do {
        *privkey_id = rand() & 0x1f;
    } while((*privkey_id == 0) | (*privkey_id == *fe_id) | (*privkey_id == *uds_id) | (*privkey_id == *cdi_id));
}

void main(){

    printf("----------------------------------\n");
    printf(" KV Smoke Test With Crypto flow !!\n");
    printf("----------------------------------\n");

    uint8_t doe_fe_dest_id;
    uint8_t uds_key_id;
    uint8_t idevid_privkey_id;
    uint8_t cdi_ldevid_id;

    //Call interrupt init
    //init_interrupts();

    random_generator(&doe_fe_dest_id, &uds_key_id, &idevid_privkey_id, &cdi_ldevid_id);
    printf("%x, %x, %x, %x\n",doe_fe_dest_id, uds_key_id, idevid_privkey_id, cdi_ldevid_id);

    if(rst_count == 0) {
        VPRINTF(LOW, "1st FE flow + warm reset\n");
        
        kv_doe(doe_fe_dest_id);
        
        //issue zeroize
        ecc_zeroize();
        hmac_zeroize();
        sha512_zeroize();
        sha256_zeroize();

        //Issue warm reset
        rst_count++;
        printf("%c",0xf6);
    }
    else if(rst_count == 1) {
        VPRINTF(LOW, "2nd FE flow + warm reset\n");

        kv_doe(doe_fe_dest_id);
        
        //Issue timed warm reset :TODO
        rst_count++;
        printf("%c",0xf6);
    }
    else if(rst_count == 2){
        VPRINTF(LOW, "3rd FE flow + Cold reset\n");
        rst_count++;
        printf("%c",0xf5); //Issue cold reset and see lock_FE_flow getting reset
    }
    else if(rst_count == 3) {
        VPRINTF(LOW, "4th FE flow after cold reset\n");

        kv_doe(doe_fe_dest_id);

        kv_hmac(0, doe_fe_dest_id, uds_key_id);

        kv_ecc(uds_key_id, idevid_privkey_id);

        kv_hmac(uds_key_id, doe_fe_dest_id, cdi_ldevid_id);

        //issue zeroize
        ecc_zeroize();
        hmac_zeroize();
        sha512_zeroize();
        sha256_zeroize();

        printf("%c",0xff); //End the test
    }
}