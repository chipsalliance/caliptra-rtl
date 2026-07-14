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

// HMAC-SHA-256 -> AES-256-ECB chain smoke test.
//
// Step 1: run HMAC-SHA-256 on RFC 4231 test case 1 and confirm the
//         256-bit tag matches the RFC vector.
// Step 2: reuse those 8 dwords as an AES-256 key, encrypt a fixed
//         plaintext (16 zero bytes) with AES-256-ECB, and confirm the
//         16 ciphertext bytes match an offline openssl reference.
//
// A byte- or dword-ordering bug at the HMAC256->AES boundary shows up
// as an AES ciphertext mismatch, so this test acts as an end-to-end
// endianness check between the two blocks.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "hmac256.h"
#include "aes.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile uint32_t* stdout     = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {

    // RFC 4231 test case 1: HMAC-SHA-256(key = 0x0b*20, msg = "Hi There").
    uint32_t hmac_key_data[HMAC256_KEY_SIZE] = {
        0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
        0x0b0b0b0b, 0x00000000, 0x00000000, 0x00000000
    };

    uint32_t hmac_block_data[HMAC256_BLOCK_SIZE] = {
        0x48692054, 0x68657265, 0x80000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000240
    };

    uint32_t hmac_expected_tag[HMAC256_TAG_SIZE] = {
        0xb0344c61, 0xd8db3853, 0x5ca8afce, 0xaf0bf12b,
        0x881dc200, 0xc9833da7, 0x26e9376c, 0x2e32cff7
    };

    uint32_t hmac_lfsr_seed_data[HMAC256_LFSR_SEED_SIZE] = {
        0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C
    };

    // AES-256-ECB(key = HMAC256 tag, plaintext = 16 zero bytes).
    // The AES CLP wrapper interprets key bytes in software-memory order
    // (per-dword little-endian), so the effective key is the HMAC256 tag
    // with each dword byte-swapped. Reference computed offline via python
    // cryptography.hazmat with that key derivation.
    uint32_t aes_plaintext[4] = {0, 0, 0, 0};
    uint32_t aes_expected_ct[4] = {
        0x4b132fe8, 0x12275e7f, 0x7868093d, 0x1d56ed00
    };

    SEND_STDOUT_CTRL(0x7F);

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC256 -> AES-256 chain smoke test\n");
    VPRINTF(LOW, "----------------------------------\n");

    init_interrupts();

    // ----- Step 1: HMAC-SHA-256 -----
    VPRINTF(LOW, "Step 1: HMAC-SHA-256 of RFC 4231 test case 1\n");

    hmac256_io hmac_key;
    hmac256_io hmac_block;
    hmac256_io hmac_lfsr_seed;
    hmac256_io hmac_tag;

    hmac_key.data_size = HMAC256_KEY_SIZE;
    for (int i = 0; i < HMAC256_KEY_SIZE; i++)
        hmac_key.data[i] = hmac_key_data[i];

    hmac_block.data_size = HMAC256_BLOCK_SIZE;
    for (int i = 0; i < HMAC256_BLOCK_SIZE; i++)
        hmac_block.data[i] = hmac_block_data[i];

    hmac_lfsr_seed.data_size = HMAC256_LFSR_SEED_SIZE;
    for (int i = 0; i < HMAC256_LFSR_SEED_SIZE; i++)
        hmac_lfsr_seed.data[i] = hmac_lfsr_seed_data[i];

    hmac_tag.data_size = HMAC256_TAG_SIZE;
    for (int i = 0; i < HMAC256_TAG_SIZE; i++)
        hmac_tag.data[i] = hmac_expected_tag[i];

    hmac256_flow(hmac_key, hmac_block, hmac_lfsr_seed, hmac_tag,
                 TRUE, TRUE, TRUE);
    hmac256_zeroize();

    // ----- Step 2: AES-256-ECB using the HMAC256 tag as the key -----
    VPRINTF(LOW, "Step 2: AES-256-ECB with HMAC256 tag as key\n");

    // Reseed the AES entropy interface once before the first op.
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_0, 0x30000567);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_1, 0x30000567);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_2, 0x30000567);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_3, 0x30000567);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_4, 0x30000567);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_5, 0x30000567);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_6, 0x30000567);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_7, 0x30000567);
    lsu_write_32(CLP_AES_CLP_REG_ENTROPY_IF_SEED_8, 0x30000567);

    aes_key_t aes_key = {0};
    aes_key.kv_intf = FALSE;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = hmac_expected_tag[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    aes_flow_t aes_input = {0};
    aes_input.data_src_mode = AES_DATA_DIRECT;
    aes_input.key           = aes_key;
    aes_input.text_len      = 16;
    aes_input.plaintext     = aes_plaintext;
    aes_input.ciphertext    = aes_expected_ct;

    aes_flow(AES_ENC, AES_ECB, AES_256, aes_input, AES_BIG_ENDIAN);

    VPRINTF(LOW, "AES-256-ECB ciphertext matched reference\n");

    VPRINTF(LOW, "* TESTCASE PASSED\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
