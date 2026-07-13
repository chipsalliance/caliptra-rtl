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

// Single-block HMAC-SHA-256 with RFC 4231 test case 1:
//   key = 0x0b * 20   (padded with zeros to 64 bytes)
//   msg = "Hi There"  (8 bytes)
//   tag = b0344c61 d8db3853 5ca8afce af0bf12b
//         881dc200 c9833da7 26e9376c 2e32cff7

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "hmac256.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile uint32_t* stdout     = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {

    uint32_t key_data[HMAC256_KEY_SIZE] = {
        0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
        0x0b0b0b0b, 0x00000000, 0x00000000, 0x00000000
    };

    uint32_t block_data[HMAC256_BLOCK_SIZE] = {
        0x48692054, 0x68657265, 0x80000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000240
    };

    uint32_t expected_tag[HMAC256_TAG_SIZE] = {
        0xb0344c61, 0xd8db3853, 0x5ca8afce, 0xaf0bf12b,
        0x881dc200, 0xc9833da7, 0x26e9376c, 0x2e32cff7
    };

    uint32_t lfsr_seed_data[HMAC256_LFSR_SEED_SIZE] = {
        0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C
    };

    SEND_STDOUT_CTRL(0x7F);

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC-SHA-256 smoke test !!\n"       );
    VPRINTF(LOW, "----------------------------------\n");

    init_interrupts();

    hmac256_io key;
    hmac256_io block;
    hmac256_io lfsr_seed;
    hmac256_io tag;

    key.data_size = HMAC256_KEY_SIZE;
    for (int i = 0; i < HMAC256_KEY_SIZE; i++)
        key.data[i] = key_data[i];

    block.data_size = HMAC256_BLOCK_SIZE;
    for (int i = 0; i < HMAC256_BLOCK_SIZE; i++)
        block.data[i] = block_data[i];

    lfsr_seed.data_size = HMAC256_LFSR_SEED_SIZE;
    for (int i = 0; i < HMAC256_LFSR_SEED_SIZE; i++)
        lfsr_seed.data[i] = lfsr_seed_data[i];

    tag.data_size = HMAC256_TAG_SIZE;
    for (int i = 0; i < HMAC256_TAG_SIZE; i++)
        tag.data[i] = expected_tag[i];

    hmac256_flow(key, block, lfsr_seed, tag, TRUE, TRUE, TRUE);
    hmac256_zeroize();

    VPRINTF(LOW, "* TESTCASE PASSED\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
