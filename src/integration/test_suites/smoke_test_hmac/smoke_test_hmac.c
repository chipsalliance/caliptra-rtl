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
#include "hmac.h"

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

    //this is the key 384-bit
    uint32_t key_data[] = {0x0b0b0b0b,
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
    uint32_t block_data[] = {0x48692054,
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
    uint32_t expected_tag[] = {0xb6a8d563,
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
    //this is a random lfsr_seed 160-bit
    uint32_t lfsr_seed_data[] = {0xC8F518D4,
                                 0xF3AA1BD4,
                                 0x6ED56C1C,
                                 0x3C9E16FB,
                                 0x800AF504};                               


    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC smoke test !!\n"               );
    VPRINTF(LOW, "----------------------------------\n");

    // Call interrupt init
    init_interrupts();

    hmac_io hmac_key;
    hmac_io hmac_block;
    hmac_io hmac_lfsr_seed;
    hmac_io hmac_tag;

    hmac_key.kv_intf = FALSE;
    hmac_key.data_size = 12;
    for (int i = 0; i < hmac_key.data_size; i++)
        hmac_key.data[i] = key_data[i];

    hmac_block.kv_intf = FALSE;
    hmac_block.data_size = 32;
    for (int i = 0; i < hmac_block.data_size; i++)
        hmac_block.data[i] = block_data[i];

    hmac_lfsr_seed.kv_intf = FALSE;
    hmac_lfsr_seed.data_size = 5;
    for (int i = 0; i < hmac_lfsr_seed.data_size; i++)
        hmac_lfsr_seed.data[i] = lfsr_seed_data[i];

    hmac_tag.kv_intf = FALSE;
    hmac_tag.data_size = 12;
    for (int i = 0; i < hmac_tag.data_size; i++)
        hmac_tag.data[i] = expected_tag[i];


    hmac_flow(hmac_key, hmac_block, hmac_lfsr_seed, hmac_tag);

    // Write 0xff to STDOUT for TB to terminate test.
    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
