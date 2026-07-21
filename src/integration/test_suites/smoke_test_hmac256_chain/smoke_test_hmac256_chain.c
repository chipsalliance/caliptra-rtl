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

// SHA-256 -> HMAC-SHA-256 -> AES-256-ECB chain smoke test.
//
// Step 1: SHA-256("SmokeCPT") produces a 256-bit digest. The 8-byte
//         message plus FIPS-180 padding fills one SHA-256 block.
// Step 2: run HMAC-SHA-256 with the Step 1 digest as the key and
//         RFC 4231 test case 1 message ("Hi There") as the payload,
//         and confirm the 256-bit tag matches the offline reference.
// Step 3: reuse those 8 tag dwords as an AES-256 key, encrypt a fixed
//         plaintext (16 zero bytes) with AES-256-ECB, and confirm the
//         16 ciphertext bytes match an offline openssl reference.
//
// A byte- or dword-ordering bug at the SHA256->HMAC256 or HMAC256->AES
// boundary shows up as a downstream mismatch, so this test acts as an
// end-to-end endianness check across all three blocks.
//
/* SHA-256 test vector (Step 1)
BLOCK = 536d6f6b65435054800000000000000000000000000000000000000000000000
        000000000000000000000000000000000000000000000000000000000000000000000040
DIGEST = 31af9dbff003ff14e16953e1dc0688f9f8d21237f9e2b03bc4508a484372e69c
*/
//
/* HMAC-SHA-256 test vector (Step 2)
KEY    = 31af9dbff003ff14e16953e1dc0688f9f8d21237f9e2b03bc4508a484372e69c
BLOCK  = 4869205468657265800000000000000000000000000000000000000000000000
         000000000000000000000000000000000000000000000000000000000000000000000240
TAG    = 3e1981bf1d687b16422648e3bfdb4d15f9f453149461f8bfaac2ddc7e70faf2f
*/
//
/* AES-256-ECB test vector (Step 3)
KEY_BE = 3e1981bf1d687b16422648e3bfdb4d15f9f453149461f8bfaac2ddc7e70faf2f
   (AES CLP consumes bytes in per-dword little-endian order, so the
    effective key is the tag with each dword byte-swapped)
PT     = 00000000000000000000000000000000
CT     = 229a7f3d7d466ad5abfc1d5c0ea62a01
*/

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "sha256.h"
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

    // ----- Step 1 inputs -----
    // SHA-256 of the 8-byte ASCII message "SmokeCPT" ({0x53, 0x6d, 0x6f,
    // 0x6b, 0x65, 0x43, 0x50, 0x54}), padded into one 512-bit block per
    // FIPS 180-4 https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf.
    // Length field = 0x40 (64 bits).
    uint32_t sha256_block_data[16] = {
        0x536d6f6b, 0x65435054, 0x80000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000040
    };

    // Reference from python hashlib.sha256(b"SmokeCPT").
    uint32_t sha256_expected_digest[8] = {
        0x31af9dbf, 0xf003ff14, 0xe16953e1, 0xdc0688f9,
        0xf8d21237, 0xf9e2b03b, 0xc4508a48, 0x4372e69c
    };

    // ----- Step 2 inputs -----
    // HMAC-SHA-256 payload: RFC 4231 test case 1 message "Hi There"
    // ({0x48, 0x69, 0x20, 0x54, 0x68, 0x65, 0x72, 0x65}), padded and
    // tagged with the FIPS-180 length. The HMAC core prepends its own
    // K_ipad block internally, so the length field is 0x240
    // (K_ipad 512 b + msg 64 b = 576 b).
    // See RFC 4231 https://datatracker.ietf.org/doc/html/rfc4231.
    uint32_t hmac_block_data[HMAC256_BLOCK_SIZE] = {
        0x48692054, 0x68657265, 0x80000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000, 0x00000240
    };

    // Reference from python hmac.new(sha256_expected_digest,
    // b"Hi There", hashlib.sha256).
    uint32_t hmac_expected_tag[HMAC256_TAG_SIZE] = {
        0x3e1981bf, 0x1d687b16, 0x422648e3, 0xbfdb4d15,
        0xf9f45314, 0x9461f8bf, 0xaac2ddc7, 0xe70faf2f
    };

    uint32_t hmac_lfsr_seed_data[HMAC256_LFSR_SEED_SIZE] = {
        0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C
    };

    // ----- Step 3 inputs -----
    // AES-256-ECB(key = HMAC256 tag, plaintext = 16 zero bytes). The
    // AES CLP wrapper interprets key bytes in software-memory order
    // (per-dword little-endian), so the effective key is the HMAC256
    // tag with each dword byte-swapped. Reference from python
    // cryptography.hazmat AES-256-ECB with that byte-swapped key.
    uint32_t aes_plaintext[4] = {0, 0, 0, 0};
    uint32_t aes_expected_ct[4] = {
        0x229a7f3d, 0x7d466ad5, 0xabfc1d5c, 0x0ea62a01
    };

    SEND_STDOUT_CTRL(0x7F);

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " SHA256 -> HMAC256 -> AES chain smoke test\n");
    VPRINTF(LOW, "----------------------------------\n");

    init_interrupts();

    // ----- Step 1: SHA-256 of "SmokeCPT" -----
    VPRINTF(LOW, "Step 1: SHA-256 of \"SmokeCPT\"\n");

    sha256_io sha_block;
    sha256_io sha_digest;

    sha_block.data_size = 16;
    for (int i = 0; i < 16; i++)
        sha_block.data[i] = sha256_block_data[i];

    sha_digest.data_size = 8;
    // sha256_flow() reads the DUT digest and compares against sha_digest.data,
    // so pass the offline reference here as the expected value.
    for (int i = 0; i < 8; i++)
        sha_digest.data[i] = sha256_expected_digest[i];

    sha256_flow(sha_block, SHA256_MODE_SHA_256, 0, 0, 0, sha_digest);

    // Read the SHA-256 digest produced by the DUT so it can drive Step 2.
    uint32_t sha256_digest[8];
    volatile uint32_t *sha_reg = (volatile uint32_t *) CLP_SHA256_REG_SHA256_DIGEST_0;
    for (int i = 0; i < 8; i++)
        sha256_digest[i] = sha_reg[i];

    // ----- Step 2: HMAC-SHA-256 keyed with the Step 1 digest -----
    VPRINTF(LOW, "Step 2: HMAC-SHA-256 with SHA-256 digest as key\n");

    hmac256_io hmac_key;
    hmac256_io hmac_block;
    hmac256_io hmac_lfsr_seed;
    hmac256_io hmac_tag;

    hmac_key.data_size = HMAC256_KEY_SIZE;
    for (int i = 0; i < HMAC256_KEY_SIZE; i++)
        hmac_key.data[i] = sha256_digest[i];

    hmac_block.data_size = HMAC256_BLOCK_SIZE;
    for (int i = 0; i < HMAC256_BLOCK_SIZE; i++)
        hmac_block.data[i] = hmac_block_data[i];

    hmac_lfsr_seed.data_size = HMAC256_LFSR_SEED_SIZE;
    for (int i = 0; i < HMAC256_LFSR_SEED_SIZE; i++)
        hmac_lfsr_seed.data[i] = hmac_lfsr_seed_data[i];

    hmac_tag.data_size = HMAC256_TAG_SIZE;
    // hmac256_flow() reads the DUT tag and compares against hmac_tag.data,
    // so pass the offline reference here as the expected value.
    for (int i = 0; i < HMAC256_TAG_SIZE; i++)
        hmac_tag.data[i] = hmac_expected_tag[i];

    hmac256_flow(hmac_key, hmac_block, hmac_lfsr_seed, hmac_tag,
                 TRUE, TRUE, TRUE);

    // Read the HMAC-256 tag produced by the DUT so it can drive Step 3.
    uint32_t hmac256_tag[HMAC256_TAG_SIZE];
    volatile uint32_t *tag_reg = (volatile uint32_t *) CLP_HMAC256_REG_HMAC256_TAG_0;
    for (int i = 0; i < HMAC256_TAG_SIZE; i++)
        hmac256_tag[i] = tag_reg[i];

    hmac256_zeroize();

    // ----- Step 3: AES-256-ECB using the HMAC256 tag as the key -----
    VPRINTF(LOW, "Step 3: AES-256-ECB with HMAC256 tag as key\n");

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
        aes_key.key_share0[i] = hmac256_tag[i];
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
