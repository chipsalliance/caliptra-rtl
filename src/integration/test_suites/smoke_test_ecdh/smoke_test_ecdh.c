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

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

/* ECC test vector (P-384):
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

/* P-256 ECDH KAT (vector 0 from src/ecc/tb/test_vectors/secp256_realdrbg_kat.hex,
   same KAT consumed by block-level ecc_p256_ecdh_test). 256-bit values packed
   MSW-first into dwords [4..11]; upper 4 dwords zeroed.
    PRIVKEY    = E5C64BE9E359BE4480D43C9F5674AEFF188B9536B438F4F54B48E5C0EF43CB0E   (privkeyB)
    PUBKEY_X   = C45FB65AD3FD376EC42D26E46948B804CF03C342ED8280E6ADDF370B7ADEEE33   (peer A)
    PUBKEY_Y   = 075E51802556AC1F194E1CEAEE7EEE233A3CD1B6525A7CD76C4E7F0398167731   (peer A)
    IV         = A9E48008266C0F419E450539DC4F94E1FEC8188130BDB07C794878891B1F0983
    SHAREDKEY  = A7BFBCAC01067AECB2B9D19D82CF09DD62EE9335EA26AC76BBE2B1E7C77F7760
*/

void main() {
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Running ECC Smoke Test (P-384 + P-256 ECDH) !!\n");
    VPRINTF(LOW, "----------------------------------\n");

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
    
    uint32_t ecc_privkey[] =       {0xF274F69D,
                                    0x163B0C9F,
                                    0x1FC3EBF4,
                                    0x292AD1C4,
                                    0xEB3CEC1C,
                                    0x5A7DDE6F,
                                    0x80C14292,
                                    0x934C2055,
                                    0xE087748D,
                                    0x0A169C77,
                                    0x2483ADEE,
                                    0x5EE70E17};

    uint32_t ecc_pubkey_x[] =      {0xD79C6D97,
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

    uint32_t ecc_pubkey_y[] =      {0x5A736393,
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

    uint32_t ecc_seed[] =          {0x8FA8541C,
                                    0x82A392CA,
                                    0x74F23ED1,
                                    0xDBFD7354,
                                    0x1C596639,
                                    0x1B97EA73,
                                    0xD744B0E3,
                                    0x4B9DF59E,
                                    0xD0158063,
                                    0xE39C09A5,
                                    0xA055371E,
                                    0xDF7A5441};

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

    uint32_t ecc_sign_r[] =        {0x871E6EA4,
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

    uint32_t ecc_sign_s[] =        {0x3E5552DE,
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

    // P-256 ECDH KAT (vector 0 from secp256_realdrbg_kat.hex). Upper 4 dwords zero.
    uint32_t ecc_privkey_p256_dh[]   = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xE5C64BE9,0xE359BE44,0x80D43C9F,0x5674AEFF,
                                        0x188B9536,0xB438F4F5,0x4B48E5C0,0xEF43CB0E};
    uint32_t ecc_pubkey_x_p256_dh[]  = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xC45FB65A,0xD3FD376E,0xC42D26E4,0x6948B804,
                                        0xCF03C342,0xED8280E6,0xADDF370B,0x7ADEEE33};
    uint32_t ecc_pubkey_y_p256_dh[]  = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0x075E5180,0x2556AC1F,0x194E1CEA,0xEE7EEE23,
                                        0x3A3CD1B6,0x525A7CD7,0x6C4E7F03,0x98167731};
    uint32_t ecc_iv_p256[]           = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xA9E48008,0x266C0F41,0x9E450539,0xDC4F94E1,
                                        0xFEC81881,0x30BDB07C,0x79487889,0x1B1F0983};
    uint32_t ecc_sharedkey_p256_dh[] = {0x00000000,0x00000000,0x00000000,0x00000000,
                                        0xA7BFBCAC,0x01067AEC,0xB2B9D19D,0x82CF09DD,
                                        0x62EE9335,0xEA26AC76,0xBBE2B1E7,0xC77F7760};

    //Call interrupt init
    init_interrupts();

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

    seed.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        seed.data[i] = ecc_seed[i];

    nonce.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        nonce.data[i] = ecc_nonce[i];
    
    iv.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        iv.data[i] = ecc_iv[i];
    
    msg.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        msg.data[i] = ecc_msg[i];
    
    privkey.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        privkey.data[i] = ecc_privkey[i];

    pubkey_x.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        pubkey_x.data[i] = ecc_pubkey_x[i];
    
    pubkey_y.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        pubkey_y.data[i] = ecc_pubkey_y[i];
    
    sign_r.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        sign_r.data[i] = ecc_sign_r[i];
    
    sign_s.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        sign_s.data[i] = ecc_sign_s[i];

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

    uint8_t curve_sel = 0;
    ecc_sharedkey_flow(iv, privkey_dh, pubkey_x_dh, pubkey_y_dh, sharedkey_dh, curve_sel);
    cptra_intr_rcv.ecc_notif = 0;

    ecc_zeroize();

    // ---------------- P-256 ECDH ----------------
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Running ECC P-256 ECDH !!\n");
    VPRINTF(LOW, "----------------------------------\n");

    for (int i = 0; i < 12; i++) privkey_dh.data[i]   = ecc_privkey_p256_dh[i];
    for (int i = 0; i < 12; i++) pubkey_x_dh.data[i]  = ecc_pubkey_x_p256_dh[i];
    for (int i = 0; i < 12; i++) pubkey_y_dh.data[i]  = ecc_pubkey_y_p256_dh[i];
    for (int i = 0; i < 12; i++) iv.data[i]           = ecc_iv_p256[i];
    for (int i = 0; i < 12; i++) sharedkey_dh.data[i] = ecc_sharedkey_p256_dh[i];

    curve_sel = 1;
    ecc_sharedkey_flow(iv, privkey_dh, pubkey_x_dh, pubkey_y_dh, sharedkey_dh, curve_sel);
    cptra_intr_rcv.ecc_notif = 0;

    ecc_zeroize();

    SEND_STDOUT_CTRL(0xff); //End the test
    
}


