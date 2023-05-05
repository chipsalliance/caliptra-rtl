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
    uint32_t expected_digest[] =   {0xBA7816BF,
                                    0x8F01CFEA,
                                    0x414140DE,
                                    0x5DAE2223,
                                    0xB00361A3,
                                    0x96177A9C,
                                    0xB410FF61,
                                    0xF20015AD};
                                    


    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " SHA256 smoke test !!\n"             );
    VPRINTF(LOW, "----------------------------------\n");

    // Call interrupt init
    //init_interrupts();

    sha256_io sha256_block;
    sha256_io sha256_digest;

    sha256_block.data_size = 16;
    for (int i = 0; i < sha256_block.data_size; i++)
        sha256_block.data[i] = block_data[i];

    sha256_digest.data_size = 8;
    for (int i = 0; i < sha256_digest.data_size; i++)
        sha256_digest.data[i] = expected_digest[i];

    sha256_flow(sha256_block, SHA256_MODE_SHA_256, sha256_digest);
    sha256_zeroize();

    // Write 0xff to STDOUT for TB to terminate test.
    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
