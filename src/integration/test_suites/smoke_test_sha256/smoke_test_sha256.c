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
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "sha256.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count       = 0;

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


void main() {

    uint32_t block_data[] = {0x61626380,
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
                             0x00000018};
    uint32_t block_data_test[] = {0x9ae630b6,
                                  0x793179f2,
                                  0xa7d966d8,
                                  0xcd080611,
                                  0xec6cb36b,
                                  0x91757f66,
                                  0x7e915f72,
                                  0x27cdcbcf,
                                  0x285ba74b,
                                  0x84800000,
                                  0x00000000,
                                  0x00000000,
                                  0x00000000,
                                  0x00000000,
                                  0x00000000,
                                  0x00000128};
    uint32_t expected_digest[] =   {0xBA7816BF,
                                    0x8F01CFEA,
                                    0x414140DE,
                                    0x5DAE2223,
                                    0xB00361A3,
                                    0x96177A9C,
                                    0xB410FF61,
                                    0xF20015AD};
    uint32_t expected_digest_test[] = {0xfc6daf01,
                                    0xc7eb60ea,
                                    0x21282001,
                                    0x216dddcd,
                                    0x04a33463,
                                    0x93b26a15,
                                    0x5fd35490,
                                    0xa3f03ffe};

    uint32_t expected_wntz_digest_w1_256[] = { 0xba7816bf,
                                        0x8f01cfea,
                                        0x414140de,
                                        0x5dae2223,
                                        0xb00361a3,
                                        0x96177a9c,
                                        0xb410ff61,
                                        0xf20015ad};

    uint32_t expected_wntz_digest_w2_256[] = { 0x1abdf685,
                                        0x6e4cdf18,
                                        0x146c6177,
                                        0xcd5968ab,
                                        0xd20795da,
                                        0x2a787c72,
                                        0x6bc77346,
                                        0x18fa944c};

    uint32_t expected_wntz_digest_w4_256[] = { 0x878c3a97,
                                        0x60a60fc2,
                                        0x52a91561,
                                        0xdba6f179,
                                        0xc9dc0292,
                                        0xaa1733c6,
                                        0x60c4a965,
                                        0x03780f5f};

    uint32_t expected_wntz_digest_w8_256[] = { 0xc625ea15,
                                        0x97b6d15a,
                                        0xcaf48a17,
                                        0x06dfaa5c,
                                        0xe6efee36,
                                        0x05d68e7a,
                                        0x83f90d36,
                                        0x4020542e};

    
    uint32_t expected_wntz_digest_w1_192[] = { 0xba7816bf,
                                        0x8f01cfea,
                                        0x414140de,
                                        0x5dae2223,
                                        0xb00361a3,
                                        0x96177a9c,
                                        0x00000000,
                                        0x00000000};

    uint32_t expected_wntz_digest_w2_192[] = { 0x084016e3,
                                        0xe81ec95f,
                                        0x86c87e81,
                                        0x65d76ed5,
                                        0x857e1b44,
                                        0x79b63cc3,
                                        0x00000000,
                                        0x00000000};

    uint32_t expected_wntz_digest_w4_192[] = { 0x70f30884,
                                        0x56d63307,
                                        0x4ec50460,
                                        0x0db5e4ed,
                                        0x16761114,
                                        0x80a15717,
                                        0x00000000,
                                        0x00000000};

    uint32_t expected_wntz_digest_w8_192[] = { 0x04a8e0b8,
                                        0xc9ab79ee,
                                        0xe186636e,
                                        0x61441571,
                                        0x56c44204,
                                        0x0278a626,
                                        0x00000000,
                                        0x00000000};


    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " SHA256 smoke test !!\n"             );
    VPRINTF(LOW, "----------------------------------\n");

    // Call interrupt init
    init_interrupts();

    sha256_io sha256_block;
    sha256_io sha256_digest;

    sha256_block.data_size = 16;
    for (int i = 0; i < sha256_block.data_size; i++)
        sha256_block.data[i] = block_data[i];

    // sha256_block.data_size = 16;
    // for (int i = 0; i < sha256_block.data_size; i++)
    //     sha256_block.data[i] = block_data_test[i];

    sha256_digest.data_size = 8;
    for (int i = 0; i < sha256_digest.data_size; i++)
        sha256_digest.data[i] = expected_wntz_digest_w1_256[i];

    sha256_flow(sha256_block, SHA256_MODE_SHA_256, 1, 1, sha256_digest);
    sha256_zeroize();

    sha256_digest.data_size = 8;
    for (int i = 0; i < sha256_digest.data_size; i++)
        sha256_digest.data[i] = expected_wntz_digest_w2_256[i];

    sha256_flow(sha256_block, SHA256_MODE_SHA_256, 2, 1, sha256_digest);
    sha256_zeroize();

    sha256_digest.data_size = 8;
    for (int i = 0; i < sha256_digest.data_size; i++)
        sha256_digest.data[i] = expected_wntz_digest_w4_256[i];

    sha256_flow(sha256_block, SHA256_MODE_SHA_256, 4, 1, sha256_digest);
    sha256_zeroize();

    sha256_digest.data_size = 8;
    for (int i = 0; i < sha256_digest.data_size; i++)
        sha256_digest.data[i] = expected_wntz_digest_w8_256[i];

    sha256_flow(sha256_block, SHA256_MODE_SHA_256, 8, 1, sha256_digest);
    sha256_zeroize();

    //--------------------------------------------------------------------

    sha256_digest.data_size = 8;
    for (int i = 0; i < sha256_digest.data_size; i++)
        sha256_digest.data[i] = expected_wntz_digest_w1_192[i];

    sha256_flow(sha256_block, SHA256_MODE_SHA_256, 1, 0, sha256_digest);
    sha256_zeroize();

    // sha256_digest.data_size = 8;
    for (int i = 0; i < sha256_digest.data_size; i++)
        sha256_digest.data[i] = expected_wntz_digest_w2_192[i];

    sha256_flow(sha256_block, SHA256_MODE_SHA_256, 2, 0, sha256_digest);
    sha256_zeroize();

    sha256_digest.data_size = 8;
    for (int i = 0; i < sha256_digest.data_size; i++)
        sha256_digest.data[i] = expected_wntz_digest_w4_192[i];

    sha256_flow(sha256_block, SHA256_MODE_SHA_256, 4, 0, sha256_digest);
    sha256_zeroize();

    sha256_digest.data_size = 8;
    for (int i = 0; i < sha256_digest.data_size; i++)
        sha256_digest.data[i] = expected_wntz_digest_w8_192[i];

    sha256_flow(sha256_block, SHA256_MODE_SHA_256, 8, 0, sha256_digest);
    sha256_zeroize();

    // Write 0xff to STDOUT for TB to terminate test.
    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
