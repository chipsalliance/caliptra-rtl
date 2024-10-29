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
#include "sha512.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

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
    .sha512_error     = 0,
    .sha512_notif     = 0,
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

    uint32_t block1_data[] =   {0x61626364,
                                0x65666768,
                                0x62636465,
                                0x66676869,
                                0x63646566,
                                0x6768696A,
                                0x64656667,
                                0x68696A6B,
                                0x65666768,
                                0x696A6B6C,
                                0x66676869,
                                0x6A6B6C6D,
                                0x6768696A,
                                0x6B6C6D6E,
                                0x68696A6B,
                                0x6C6D6E6F,
                                0x696A6B6C,
                                0x6D6E6F70,
                                0x6A6B6C6D,
                                0x6E6F7071,
                                0x6B6C6D6E,
                                0x6F707172,
                                0x6C6D6E6F,
                                0x70717273,
                                0x6D6E6F70,
                                0x71727374,
                                0x6E6F7071,
                                0x72737475,
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
                                0x00000000,
                                0x00000000,
                                0x00000000,
                                0x00000000,
                                0x00000000,
                                0x00000000,
                                0x00000380
                                };

    uint32_t expected10_digest[] = {0x4319017A,
                                    0x2B706E69,
                                    0xCD4B0593,
                                    0x8BAE5E89,
                                    0x0186BF19,
                                    0x9F30AA95,
                                    0x6EF8B71D,
                                    0x2F810585,
                                    0xD787D676,
                                    0x4B20BDA2,
                                    0xA2601447,
                                    0x09736920,
                                    0x00EC057F,
                                    0x37D14B8E,
                                    0x06ADD5B5,
                                    0x0E671C72};
                                    

    uint32_t expected11_digest[] = {0x8E959B75,
                                    0xDAE313DA,
                                    0x8CF4F728,
                                    0x14FC143F,
                                    0x8F7779C6,
                                    0xEB9F7FA1,
                                    0x7299AEAD,
                                    0xB6889018,
                                    0x501D289E,
                                    0x4900F7E4,
                                    0x331B99DE,
                                    0xC4B5433A,
                                    0xC7D329EE,
                                    0xB6DD2654,
                                    0x5E96E55B,
                                    0x874BE909};



    uint32_t block2_data[] = {0x61626380,
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
                             0x00000018};

    uint32_t expected2_digest[] =   {0xDDAF35A1,
                                    0x93617ABA,
                                    0xCC417349,
                                    0xAE204131,
                                    0x12E6FA4E,
                                    0x89A97EA2,
                                    0x0A9EEEE6,
                                    0x4B55D39A,
                                    0x2192992A,
                                    0x274FC1A8,
                                    0x36BA3C23,
                                    0xA3FEEBBD,
                                    0x454D4423,
                                    0x643CE80E,
                                    0x2A9AC94F,
                                    0xA54CA49F};

    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " SHA512 Restore smoke test !!\n"     );
    VPRINTF(LOW, "----------------------------------\n");

    // Call interrupt init
    init_interrupts();

    sha512_io sha512_block;
    sha512_io sha512_digest;
    sha512_io sha512_intermediate_digest;
    sha512_io sha512_final_digest;

    sha512_block.data_size = 32;
    for (int i = 0; i < sha512_block.data_size; i++)
        sha512_block.data[i] = block1_data[i];

    sha512_intermediate_digest.data_size = 16;
    for (int i = 0; i < sha512_intermediate_digest.data_size; i++)
        sha512_intermediate_digest.data[i] = expected10_digest[i];

    sha512_flow(sha512_block, SHA512_512_MODE, sha512_intermediate_digest);
    sha512_zeroize();


    for (int i = 0; i < sha512_block.data_size; i++)
        sha512_block.data[i] = block2_data[i];

    sha512_digest.data_size = 16;
    for (int i = 0; i < sha512_digest.data_size; i++)
        sha512_digest.data[i] = expected2_digest[i];

    sha512_flow(sha512_block, SHA512_512_MODE, sha512_digest);
    sha512_zeroize();

    for (int i = 0; i < sha512_block.data_size; i++)
        sha512_block.data[i] = block1_data[32+i];

    sha512_final_digest.data_size = 16;
    for (int i = 0; i < sha512_final_digest.data_size; i++)
        sha512_final_digest.data[i] = expected11_digest[i];

    sha512_restore_flow(sha512_block, SHA512_512_MODE, sha512_intermediate_digest, sha512_final_digest);

    // Write 0xff to STDOUT for TB to terminate test.
    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
