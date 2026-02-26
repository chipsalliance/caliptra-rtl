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
// ML-KEM KV Endianness Validation Smoke Test
//
// PURPOSE:
//   End-to-end validation: HMAC-512 → ML-KEM-1024 → AES-256-ECB
//   All intermediate and final values verified against Python reference.
//
// FLOW:
//   Step 0: HMAC-512(key, msg) → 64-byte tag → seed_d || seed_z
//   Phase 1 (API path - reference):
//     1. ML-KEM keygen + encaps via API → shared_key
//     2. Verify shared key matches EXPECTED_SHARED_KEY
//     3. AES-256-ECB encrypt (key from SW registers) → verify ciphertext
//   Phase 2 (KV path - under test):
//     1. ML-KEM keygen_decaps → shared_key to KV slot
//     2. AES reads key from KV → verify ciphertext matches same reference

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"
#include "mlkem.h"
#include "hmac.h"
#include "aes.h"

// =====================================================================
// TEST VECTORS — Edit this section to update inputs and expected outputs
// =====================================================================

// HMAC-512 key (64 bytes / 16 DWORDs) — tag → seed_d || seed_z
#define HMAC_KEY { \
    0x00000000, 0x00000000, 0x00000000, 0x00000000, \
    0x00000000, 0x00000000, 0x00000000, 0x00000000, \
    0x00000000, 0x00000000, 0x00000000, 0x00000000, \
    0x00000000, 0x00000000, 0x00000000, 0x00000000  \
}

// HMAC-512 message block (128 bytes / 32 DWORDs, including SHA-512 padding)
// Message: 64 bytes of 0x0b, then 0x80 pad, zeros, length=0x600 (1536 bits)
#define HMAC_DATA { \
    0x0B0B0B0B, 0x0B0B0B0B, 0x0B0B0B0B, 0x0B0B0B0B, \
    0x0B0B0B0B, 0x0B0B0B0B, 0x0B0B0B0B, 0x0B0B0B0B, \
    0x0B0B0B0B, 0x0B0B0B0B, 0x0B0B0B0B, 0x0B0B0B0B, \
    0x0B0B0B0B, 0x0B0B0B0B, 0x0B0B0B0B, 0x0B0B0B0B, \
    0x80000000, 0x00000000, 0x00000000, 0x00000000, \
    0x00000000, 0x00000000, 0x00000000, 0x00000000, \
    0x00000000, 0x00000000, 0x00000000, 0x00000000, \
    0x00000000, 0x00000000, 0x00000000, 0x00000600  \
}

// Expected HMAC-512 tag (16 DWORDs, as raw register values)
// First 8 DWORDs = seed_d, last 8 DWORDs = seed_z
#define EXPECTED_HMAC_TAG { \
    0x5C314DBB, 0x03AD6ADE, 0x28E553C4, 0x8F3D56E2, \
    0x56846963, 0x73B7200C, 0x945C50DB, 0xC76ED0E5, \
    0x7A9B2F51, 0x0FE4FDF8, 0xE0329268, 0xFE10D3D1, \
    0x75ABC56E, 0xB547EBEC, 0x8AC23033, 0xEF81CFF8  \
}

// ML-KEM encaps message (32 bytes / 8 DWORDs)
#define MLKEM_MSG { \
    0xB0104BC6, 0xBF6074CA, 0x38E31533, 0xDC84BB45, \
    0xF7397831, 0x33F70918, 0xEFDE949F, 0xB0D51DDC  \
}

// AES plaintext (hex string, must be multiple of 16 bytes)
#define AES_PLAINTEXT \
    "a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5" \
    "a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5" \
    "a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5" \
    "a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5"

// Expected ML-KEM shared key from encaps (8 DWORDs, as raw register values)
#define EXPECTED_SHARED_KEY { \
    0xE63090BD, 0x96F1C12B, 0x251F5F9A, 0x586881DD, \
    0x68BFA668, 0xC059931B, 0x25274778, 0xEB60C9CC  \
}

// Expected AES-256-ECB ciphertext (hex string, same length as plaintext)
// NOTE: hex strings are parsed by hex_to_uint32_array which byte-swaps;
//       AES driver uses the same convention so this is self-consistent.
#define EXPECTED_CIPHERTEXT \
    "b67a93ed1822858c50c5c3e3f2d77605" \
    "b67a93ed1822858c50c5c3e3f2d77605" \
    "b67a93ed1822858c50c5c3e3f2d77605" \
    "b67a93ed1822858c50c5c3e3f2d77605"

// KV slot assignments
#define KV_HMAC_TAG_SLOT    0   // HMAC tag → ML-KEM seed (16 DWORDs)
#define KV_SHARED_KEY_SLOT  2   // ML-KEM shared key → AES key (8 DWORDs)

// =====================================================================

// Byte-swap macro: HMAC registers are big-endian, ML-KEM registers are
// little-endian.  When feeding HMAC tag DWORDs into ML-KEM seed/msg
// registers via the FW path we must reverse the byte order within each
// DWORD so the ML-KEM core sees the correct byte stream.
#define BSWAP32(x) ( \
    (((x) << 24) & 0xFF000000U) | \
    (((x) <<  8) & 0x00FF0000U) | \
    (((x) >>  8) & 0x0000FF00U) | \
    (((x) >> 24) & 0x000000FFU)   \
)

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

uint32_t abr_entropy[ABR_ENTROPY_SIZE] = {
    0x3401CEFA, 0xE20A7376, 0x49073AC1, 0xA351E329,
    0x26DB9ED0, 0xDB6B1CFF, 0xAB0493DA, 0xAFB93DDD,
    0xD83EDEA2, 0x8A803D0D, 0x003B2633, 0xB9D0F1BF,
    0x3401CEFA, 0xE20A7376, 0x49073AC1, 0xA351E329
};

void main() {
    uint8_t fail_cmd = 0x1;

    // HMAC variables
    hmac_io hmac_key_io = {0};
    hmac_io hmac_block_io = {0};
    hmac_io hmac_lfsr_seed = {0};
    hmac_io hmac_tag_io = {0};
    uint32_t actual_tag[HMAC512_TAG_SIZE];
    const uint32_t hmac_key_data[HMAC512_KEY_SIZE] = HMAC_KEY;
    const uint32_t hmac_block_data[HMAC512_BLOCK_SIZE] = HMAC_DATA;
    const uint32_t expected_tag[HMAC512_TAG_SIZE] = EXPECTED_HMAC_TAG;

    // ML-KEM variables
    mlkem_seed seed;
    mlkem_msg msg;
    mlkem_shared_key shared_key;
    mlkem_shared_key kv_shared_key;
    uint32_t actual_ek[MLKEM_EK_SIZE];
    uint32_t actual_dk[MLKEM_DK_SIZE];
    uint32_t actual_ciphertext[MLKEM_CIPHERTEXT_SIZE];
    uint32_t actual_sharedkey[MLKEM_SHAREDKEY_SIZE];
    const uint32_t msg_data[MLKEM_MSG_SIZE] = MLKEM_MSG;

    // AES variables
    aes_op_e op = AES_ENC;
    aes_mode_e mode = AES_ECB;
    aes_key_len_e key_len = AES_256;
    aes_flow_t aes_input = {0};
    aes_input.data_src_mode = AES_DATA_DIRECT;
    aes_input.dma_transfer_data = (dma_transfer_data_t){0};

    const char plaintext_str[] = AES_PLAINTEXT;
    const char expected_ct_str[] = EXPECTED_CIPHERTEXT;
    const uint32_t expected_sk[MLKEM_SHAREDKEY_SIZE] = EXPECTED_SHARED_KEY;
    uint32_t plaintext[32];
    uint32_t plaintext_length;
    uint32_t expected_ct[32];
    uint32_t expected_ct_length;

    VPRINTF(LOW, "----------------------------------------------\n");
    VPRINTF(LOW, " HMAC→ML-KEM→AES KV Endianness Smoke Test\n");
    VPRINTF(LOW, "----------------------------------------------\n");

    init_interrupts();

    // Parse expected values
    hex_to_uint32_array(plaintext_str, plaintext, &plaintext_length);
    hex_to_uint32_array(expected_ct_str, expected_ct, &expected_ct_length);

    // Common HMAC setup
    hmac_key_io.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_KEY_SIZE; i++)
        hmac_key_io.data[i] = hmac_key_data[i];

    hmac_block_io.kv_intf = FALSE;
    hmac_block_io.data_size = HMAC512_BLOCK_SIZE;
    for (int i = 0; i < HMAC512_BLOCK_SIZE; i++)
        hmac_block_io.data[i] = hmac_block_data[i];

    hmac_lfsr_seed.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_LFSR_SEED_SIZE; i++)
        hmac_lfsr_seed.data[i] = 0;

    // ML-KEM msg (same for both phases, byte-swapped to LE)
    msg.kv_intf = FALSE;
    for (int i = 0; i < MLKEM_MSG_SIZE; i++)
        msg.data[i] = BSWAP32(msg_data[i]);

    // ================================================================
    // PHASE 1: API reference path (all FW registers)
    //   HMAC → tag via FW → seed_d/z → ML-KEM → shared key → AES
    // ================================================================
    VPRINTF(LOW, "\n--- Phase 1: All-FW reference path ---\n");

    // HMAC-512 → tag via FW registers
    VPRINTF(LOW, "Phase 1: HMAC-512 → tag via FW\n");
    hmac_tag_io.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_TAG_SIZE; i++)
        hmac_tag_io.data[i] = expected_tag[i];

    hmac512_flow_return(hmac_key_io, hmac_block_io, hmac_lfsr_seed,
                        hmac_tag_io, TRUE, actual_tag);
    hmac_zeroize();
    cptra_intr_rcv.hmac_notif = 0;

    // Verify HMAC tag
    for (int i = 0; i < HMAC512_TAG_SIZE; i++) {
        VPRINTF(LOW, "HMAC tag[%d]: 0x%x\n", i, actual_tag[i]);
        if (actual_tag[i] != expected_tag[i]) {
            VPRINTF(FATAL, "ERROR: HMAC tag mismatch at [%d]: got 0x%x, expected 0x%x\n",
                    i, actual_tag[i], expected_tag[i]);
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }
    }
    VPRINTF(LOW, "HMAC tag matches expected reference\n");

    // Split tag → seed_d (first 8 DWORDs), seed_z (last 8 DWORDs)
    // BSWAP32: HMAC is big-endian, ML-KEM is little-endian
    seed.kv_intf = FALSE;
    for (int i = 0; i < MLKEM_SEED_SIZE; i++) {
        seed.data[0][i] = BSWAP32(actual_tag[i]);                    // seed_d
        seed.data[1][i] = BSWAP32(actual_tag[MLKEM_SEED_SIZE + i]);  // seed_z
    }

    shared_key.kv_intf = FALSE;
    for (int i = 0; i < MLKEM_SHAREDKEY_SIZE; i++)
        shared_key.data[i] = 0;

    // ML-KEM keygen (FW seeds)
    VPRINTF(LOW, "Phase 1: ML-KEM keygen (FW seeds)\n");
    mlkem_keygen_flow(seed, abr_entropy, actual_ek, actual_dk);
    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    // ML-KEM encaps → shared key via FW
    VPRINTF(LOW, "Phase 1: ML-KEM encaps (FW) → shared key\n");
    mlkem_encaps_flow(actual_ek, msg, abr_entropy, actual_ciphertext,
                      shared_key, actual_sharedkey);

    for (int i = 0; i < MLKEM_SHAREDKEY_SIZE; i++)
        VPRINTF(LOW, "Shared Key[%d]: 0x%x\n", i, actual_sharedkey[i]);

    // Verify shared key against independent reference
    // ML-KEM register returns LE DWORDs; expected_sk is BE (Python byte order)
    for (int i = 0; i < MLKEM_SHAREDKEY_SIZE; i++) {
        if (actual_sharedkey[i] != BSWAP32(expected_sk[i])) {
            VPRINTF(FATAL, "ERROR: Shared key mismatch at [%d]: got 0x%x, expected 0x%x\n",
                    i, actual_sharedkey[i], BSWAP32(expected_sk[i]));
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }
    }
    VPRINTF(LOW, "Phase 1: Shared key matches expected reference\n");

    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    // AES-256-ECB with FW key
    // Both ML-KEM and AES registers are LE — no byte-swap needed
    VPRINTF(LOW, "Phase 1: AES-ECB encrypt (FW key)\n");
    aes_key_t aes_key_api = {0};
    aes_key_api.kv_intf = FALSE;
    for (int i = 0; i < MLKEM_SHAREDKEY_SIZE; i++) {
        aes_key_api.key_share0[i] = actual_sharedkey[i];
        aes_key_api.key_share1[i] = 0;
    }

    aes_input.key = aes_key_api;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = expected_ct;
    aes_input.aad_len = 0;

    aes_flow(op, mode, key_len, aes_input, AES_LITTLE_ENDIAN);
    VPRINTF(LOW, "Phase 1 PASS: All FW path matches reference\n");

    // ================================================================
    // PHASE 2: KV path (under test)
    //   HMAC → tag to KV → ML-KEM keygen_decaps (seed from KV) →
    //   shared key to KV → AES
    // ================================================================
    VPRINTF(LOW, "\n--- Phase 2: All-KV path (under test) ---\n");

    // HMAC-512 → tag to KV slot
    VPRINTF(LOW, "Phase 2: HMAC-512 → tag to KV slot %d\n", KV_HMAC_TAG_SLOT);
    hmac_tag_io.kv_intf = TRUE;
    hmac_tag_io.kv_id = KV_HMAC_TAG_SLOT;

    hmac512_flow(hmac_key_io, hmac_block_io, hmac_lfsr_seed,
                 hmac_tag_io, TRUE);
    hmac_zeroize();
    cptra_intr_rcv.hmac_notif = 0;

    // ML-KEM keygen_decaps with seed from KV
    VPRINTF(LOW, "Phase 2: ML-KEM keygen_decaps (seed from KV slot %d)\n", KV_HMAC_TAG_SLOT);
    seed.kv_intf = TRUE;
    seed.kv_id = KV_HMAC_TAG_SLOT;

    kv_shared_key.kv_intf = TRUE;
    kv_shared_key.kv_id = KV_SHARED_KEY_SLOT;
    kv_shared_key.exp_kv_err = FALSE;
    kv_shared_key.skip_kv_check = TRUE;  // skip TB 0xb3 assertion (our vectors differ from TB random)
    for (int i = 0; i < MLKEM_SHAREDKEY_SIZE; i++)
        kv_shared_key.data[i] = 0;

    // ML-KEM keygen + decaps → shared key to KV
    // Uses ciphertext from Phase 1 encaps
    VPRINTF(LOW, "Phase 2: ML-KEM keygen_decaps (KV seed → KV shared key)\n");
    mlkem_keygen_decaps_flow(seed, actual_ciphertext, abr_entropy,
                             kv_shared_key);
    mlkem_zeroize();
    cptra_intr_rcv.abr_notif = 0;

    // AES-256-ECB with key from KV
    VPRINTF(LOW, "Phase 2: AES-ECB encrypt (key from KV slot %d)\n", KV_SHARED_KEY_SLOT);
    aes_key_t aes_key_kv = {0};
    aes_key_kv.kv_intf = TRUE;
    aes_key_kv.kv_reuse_key = FALSE;
    aes_key_kv.kv_expect_err = FALSE;
    aes_key_kv.kv_id = kv_shared_key.kv_id;

    aes_input.key = aes_key_kv;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = expected_ct;

    // If KV seed endianness is wrong, ML-KEM sees wrong seeds →
    // different keys → decaps fails → wrong shared key → AES mismatch → FAIL
    aes_flow(op, mode, key_len, aes_input, AES_LITTLE_ENDIAN);

    VPRINTF(LOW, "\n--- PASS: KV path matches FW reference ---\n");
    VPRINTF(LOW, "HMAC→KV→ML-KEM(seed)→KV→AES endianness is correct.\n");

    SEND_STDOUT_CTRL(0xff);
}
