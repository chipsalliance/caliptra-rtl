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

/* ECC negative verification test.

   Reuses the known-answer vector from smoke_test_ecc_verify:

    MSG      = C8F518D4F3AA1BD46ED56C1C3C9E16FB800AF504DB98843548C5F623EE115F73D4C62ABC06D303B5D90D9A175087290D
    PUBKEY_X = D79C6D972B34A1DFC916A7B6E0A99B6B5387B34DA2187607C1AD0A4D1A8C2E4172AB5FA5D9AB58FE45E43F56BBB66BA4
    PUBKEY_Y = 5A7363932B06B4F223BEF0B60A6390265112DBBD0AAE67FEF26B465BE935B48E451E68D16F1118F2B32B4C28608749ED
    Sign_R   = 871E6EA4DDC5432CDDAA60FD7F055472D3C4DD41A5BFB26709E88C311A97093599A7C8F55B3974C19E4F5A7BFC1DD2AC
    SIGN_S   = 3E5552DE6403350EE70AD74E4B854D2DC4126BBF9C153A5D7A07BD4B85D06E45F850920E898FB7D34F80796DAE29365C

   The positive direction is already covered by smoke_test_ecc_verify, so this test
   only exercises the failure direction: the least significant bit of MSG is flipped
   before verification. MSG is deliberately the mutated input: it is the only VERIFY
   operand with no validity check in ecc_dsa_ctrl.sv (it is only reduced modulo
   GROUP_ORDER and contributes no term to error_flag), so the mutation is guaranteed
   to reach the ordinary comparison and yield VERIFY_PASS = 0 rather than steering the
   design into the already covered error path.
*/

void main() {
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Running ECC Verify Failure Test !!\n");
    VPRINTF(LOW, "----------------------------------\n");

    uint32_t ecc_msg[] =        {0xC8F518D4,
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

    uint32_t ecc_pubkey_x[] =   {0xD79C6D97,
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

    uint32_t ecc_pubkey_y[] =   {0x5A736393,
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

    uint32_t ecc_sign_r[] =     {0x871E6EA4,
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

    uint32_t ecc_sign_s[] =     {0x3E5552DE,
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

    //Call interrupt init
    init_interrupts();

    ecc_io pubkey_x;
    ecc_io pubkey_y;
    ecc_io bad_msg;
    ecc_io sign_r;
    ecc_io sign_s;

    // Corrupt the message only. Signature and public key stay in range so error_flag
    // cannot assert and the design must take the comparison mismatch path.
    bad_msg.kv_intf = FALSE;
    for (int i = 0; i < 12; i++)
        bad_msg.data[i] = ecc_msg[i];
    bad_msg.data[11] ^= 0x00000001;

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

    // Step 1: verify the corrupted message. The flow asserts that no error was raised
    // and that ECC_STATUS.VERIFY_PASS reads back as 0.
    ecc_verifying_flow_expect_fail(bad_msg, pubkey_x, pubkey_y, sign_r, sign_s);
    cptra_intr_rcv.ecc_notif = 0;

    // Step 2: a following zeroize must leave the FAIL verdict cleared.
    ecc_zeroize();
    ecc_check_verify_pass(0);

    VPRINTF(LOW, "ECC verify failure reported correctly through ECC_STATUS.VERIFY_PASS\n");

    SEND_STDOUT_CTRL(0xff); //End the test

}
