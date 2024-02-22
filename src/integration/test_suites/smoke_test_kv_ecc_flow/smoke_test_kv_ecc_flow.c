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

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
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
};

/* ECC test vector:
    MSG      = C8F518D4F3AA1BD46ED56C1C3C9E16FB800AF504DB98843548C5F623EE115F73D4C62ABC06D303B5D90D9A175087290D
    PRIVKEY  = F274F69D163B0C9F1FC3EBF4292AD1C4EB3CEC1C5A7DDE6F80C14292934C2055E087748D0A169C772483ADEE5EE70E17
    PUBKEY_X = D79C6D972B34A1DFC916A7B6E0A99B6B5387B34DA2187607C1AD0A4D1A8C2E4172AB5FA5D9AB58FE45E43F56BBB66BA4
    PUBKEY_Y = 5A7363932B06B4F223BEF0B60A6390265112DBBD0AAE67FEF26B465BE935B48E451E68D16F1118F2B32B4C28608749ED
    SEED     = 8FA8541C82A392CA74F23ED1DBFD73541C5966391B97EA73D744B0E34B9DF59ED0158063E39C09A5A055371EDF7A5441
    NONCE    = 1B7EC5E548E8AAA92EC77097CA9551C9783CE682CA18FB1EDBD9F1E50BC382DB8AB39496C8EE423F8CA105CBBA7B6588
    Sign_R   = 871E6EA4DDC5432CDDAA60FD7F055472D3C4DD41A5BFB26709E88C311A97093599A7C8F55B3974C19E4F5A7BFC1DD2AC
    SIGN_S   = 3E5552DE6403350EE70AD74E4B854D2DC4126BBF9C153A5D7A07BD4B85D06E45F850920E898FB7D34F80796DAE29365C
    IV       = 3401CEFAE20A737649073AC1A351E32926DB9ED0DB6B1CFFAB0493DAAFB93DDDD83EDEA28A803D0D003B2633B9D0F1BF
*/

void main(){

    printf("----------------------------------\n");
    printf(" KV Smoke Test With ECC flow !!\n");
    printf("----------------------------------\n");

    uint32_t ecc_msg[] =           {0xC8F518D4,
                                    0xF3AA1BD4,
                                    0x6ED56C1C,
                                    0x3C9E16FB,
                                    0x800AF504,
                                    0xDB988435,
                                    0x48C5F623,
                                    0xEE115F73,
                                    0xD4C62ABC,
                                    0x06D303B5,
                                    0xD90D9A17,
                                    0x5087290D};

    uint32_t expected_pubkey_x[] = {0xD79C6D97,
                                    0x2B34A1DF,
                                    0xC916A7B6,
                                    0xE0A99B6B,
                                    0x5387B34D,
                                    0xA2187607,
                                    0xC1AD0A4D,
                                    0x1A8C2E41,
                                    0x72AB5FA5,
                                    0xD9AB58FE,
                                    0x45E43F56,
                                    0xBBB66BA4};

    uint32_t expected_pubkey_y[] = {0x5A736393,
                                    0x2B06B4F2,
                                    0x23BEF0B6,
                                    0x0A639026,
                                    0x5112DBBD,
                                    0x0AAE67FE,
                                    0xF26B465B,
                                    0xE935B48E,
                                    0x451E68D1,
                                    0x6F1118F2,
                                    0xB32B4C28,
                                    0x608749ED};

    uint32_t ecc_nonce[] =         {0x1B7EC5E5,
                                    0x48E8AAA9,
                                    0x2EC77097,
                                    0xCA9551C9,
                                    0x783CE682,
                                    0xCA18FB1E,
                                    0xDBD9F1E5,
                                    0x0BC382DB,
                                    0x8AB39496,
                                    0xC8EE423F,
                                    0x8CA105CB,
                                    0xBA7B6588};

    uint32_t expected_sign_r[] =   {0x871E6EA4,
                                    0xDDC5432C,
                                    0xDDAA60FD,
                                    0x7F055472,
                                    0xD3C4DD41,
                                    0xA5BFB267,
                                    0x09E88C31,
                                    0x1A970935,
                                    0x99A7C8F5,
                                    0x5B3974C1,
                                    0x9E4F5A7B,
                                    0xFC1DD2AC};

    uint32_t expected_sign_s[] =   {0x3E5552DE,
                                    0x6403350E,
                                    0xE70AD74E,
                                    0x4B854D2D,
                                    0xC4126BBF,
                                    0x9C153A5D,
                                    0x7A07BD4B,
                                    0x85D06E45,
                                    0xF850920E,
                                    0x898FB7D3,
                                    0x4F80796D,
                                    0xAE29365C};

    
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

    uint32_t ecc_privkey_dh[] =    {0x52D1791F,
                                    0xDB4B70F8,
                                    0x9C0F00D4,
                                    0x56C2F702,
                                    0x3B612526,
                                    0x2C36A7DF,
                                    0x1F802311,
                                    0x21CCE3D3,
                                    0x9BE52E00,
                                    0xC194A413,
                                    0x2C4A6C76,
                                    0x8BCD94D2};

    uint32_t ecc_pubkey_x_dh[] =   {0x793148F1,0X787634D5,0XDA4C6D90,0X74417D05,0XE057AB62,0XF82054D1,0X0EE6B040,0X3D627954,0X7E6A8EA9,0XD1FD7742,0X7D016FE2,0X7A8B8C66};
    uint32_t ecc_pubkey_y_dh[] =   {0xC6C41294,0X331D23E6,0XF480F4FB,0X4CD40504,0XC947392E,0X94F4C3F0,0X6B8F398B,0XB29E4236,0X8F7A6859,0X23DE3B67,0XBACED214,0XA1A1D128};
    uint32_t ecc_sharedkey_dh[] =  {0x5EA1FC4A,0XF7256D20,0X55981B11,0X0575E0A8,0XCAE53160,0X137D904C,0X59D926EB,0X1B8456E4,0X27AA8A45,0X40884C37,0XDE159A58,0X028ABC0E};                                

    //Call interrupt init
    init_interrupts();

    uint8_t seed_kv_id = 0x1;
    uint8_t privkey_kv_id = 0x2;
    uint8_t sharedkey_kv_id = 0x7;

    ecc_io seed;
    ecc_io nonce;
    ecc_io iv;
    ecc_io privkey;
    ecc_io pubkey_x;
    ecc_io pubkey_y;
    ecc_io msg;
    ecc_io sign_r;
    ecc_io sign_s;
    ecc_io privkey_dh;
    ecc_io pubkey_x_dh;
    ecc_io pubkey_y_dh;
    ecc_io sharedkey_dh;

    privkey_dh.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        privkey_dh.data[i] = ecc_privkey_dh[i];

    pubkey_x_dh.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        pubkey_x_dh.data[i] = ecc_pubkey_x_dh[i];  

    pubkey_y_dh.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        pubkey_y_dh.data[i] = ecc_pubkey_y_dh[i];  

    sharedkey_dh.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        sharedkey_dh.data[i] = ecc_sharedkey_dh[i];

    seed.kv_intf = TRUE;
    seed.kv_id = seed_kv_id;

    nonce.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        nonce.data[i] = ecc_nonce[i];
    
    iv.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        iv.data[i] = ecc_iv[i];
    
    msg.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        msg.data[i] = ecc_msg[i];

    privkey.kv_intf = TRUE;
    privkey.kv_id = privkey_kv_id;

    pubkey_x.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        pubkey_x.data[i] = expected_pubkey_x[i];
    
    pubkey_y.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        pubkey_y.data[i] = expected_pubkey_y[i];
    
    sign_r.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        sign_r.data[i] = expected_sign_r[i];
    
    sign_s.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        sign_s.data[i] = expected_sign_s[i];

    //inject seed to kv key reg (in RTL)
    printf("Inject SEED into KV\n");
    uint8_t seed_inject_cmd = 0x80 + (seed_kv_id & 0x7);
    printf("%c", seed_inject_cmd);

    ecc_keygen_flow(seed, nonce, iv, privkey, pubkey_x, pubkey_y);
    cptra_intr_rcv.ecc_notif = 0;

    ecc_sharedkey_flow(nonce, iv, privkey_dh, pubkey_x_dh, pubkey_y_dh, sharedkey_dh);
    cptra_intr_rcv.ecc_notif = 0;

    sharedkey_dh.kv_intf = TRUE;
    sharedkey_dh.kv_id = sharedkey_kv_id;

    privkey_dh.kv_intf = TRUE;
    privkey_dh.kv_id = privkey_kv_id;

    ecc_sharedkey_flow(nonce, iv, privkey_dh, pubkey_x_dh, pubkey_y_dh, sharedkey_dh);
    cptra_intr_rcv.ecc_notif = 0;

    ecc_signing_flow(privkey, msg, iv, sign_r, sign_s);
    cptra_intr_rcv.ecc_notif = 0;

    ecc_zeroize();

    printf("%c",0xff); //End the test
}
