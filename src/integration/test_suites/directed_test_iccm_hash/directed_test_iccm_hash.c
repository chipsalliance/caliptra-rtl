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
// directed_test_iccm_hash.c
// Multi-sequence directed test for ICCM write hash --> PCR4 feature.
// Performs 5 different ICCM write sequences separated by fw_update_reset,
// verifying PCR4 is cleared and re-computed correctly each time.
//
// Sequence 1: 64 words  (256 bytes, multi-block)          --> lock --> check PCR4 --> fw_update_reset
// Sequence 2: 28 words  (112 bytes, extra pad block)      --> lock --> check PCR4 --> fw_update_reset
// Sequence 3: 0 words   (zero-length hash)                --> lock --> check PCR4 --> fw_update_reset
// Sequence 4: 32 words  (128 bytes, exact block boundary) --> lock --> check PCR4 --> fw_update_reset
// Sequence 5: 260 words (1040 bytes, large >1KB)          --> lock --> check PCR4 --> fw_update_reset
// Sequence 6: 64 words  tight memcpy (adjacent sw pairs   --> lock --> check PCR4 --> PASS
//             to trigger LSU bus buffer dword merging)

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "iccm_hash.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Persistent state across fw_update_reset (DCCM survives reset)
static uint32_t iteration __attribute__ ((section(".dccm.persistent"))) = 0;

// Expected SHA-384 PCR4 extend digests for each sequence.
// PCR4 is cleared to zero before each extend, so:
//   PCR4 = SHA-384(48_bytes_of_zeros || SHA-384(iccm_write_stream))
// The ICCM write stream is hashed as little-endian 32-bit words (no byte swap).

// Sequence 1: 64 words {0x10..0x4F} - 256 bytes
static const uint32_t expected_seq1[12] = {
    0x73c26a32, 0x28bce060, 0x94b092a6, 0x4d3c6007,
    0xbe359bab, 0xa1b76c71, 0x812f325a, 0x99a13504,
    0x665282d5, 0xa2df5e62, 0xf00187ff, 0x61da0cd0
};

// Sequence 2: 28 words {0xBB00..0xBB1B} - 112 bytes
static const uint32_t expected_seq2[12] = {
    0xbd1c801b, 0x247dd517, 0x3ddff4e1, 0xf4336345,
    0x177dd7d3, 0xf7803a8b, 0x25e87434, 0x3811fde4,
    0x5aee0f9b, 0x0012e968, 0xf5cee942, 0x1941d55e
};

// Sequence 3: 0 words - 0 bytes (extend of zero-length iccm digest)
static const uint32_t expected_seq3[12] = {
    0x21b9efbc, 0x18480766, 0x2e966d34, 0xf3908213,
    0x09eeac68, 0x02309798, 0x826296bf, 0x3e8bec7c,
    0x10edb309, 0x48c90ba6, 0x7310f7b9, 0x64fc500a
};

// Sequence 4: 32 words {0xC000..0xC01F} - 128 bytes
static const uint32_t expected_seq4[12] = {
    0x01c32e80, 0x6e0812d2, 0x3d2cf9c7, 0xd716f30f,
    0xaf590d10, 0x167979cf, 0x8e8ff08d, 0x1f7c1e42,
    0xfb0ccb85, 0x86552358, 0x0ab4d913, 0xa9bd6004
};

// Sequence 5: 260 words {0xD000..0xD103} - 1040 bytes
static const uint32_t expected_seq5[12] = {
    0x701ae631, 0xa53f6b61, 0x2ab9b1f4, 0xc6fc4f35,
    0x318ccd0c, 0x4a25076c, 0x0ce764ad, 0x51716b58,
    0xcce93c4d, 0x14657f8e, 0x68c2d716, 0x045a289d
};

// Sequence 6: 64 words {0x10..0x4F} via tight memcpy (same data as seq1)
static const uint32_t expected_seq6[12] = {
    0x73c26a32, 0x28bce060, 0x94b092a6, 0x4d3c6007,
    0xbe359bab, 0xa1b76c71, 0x812f325a, 0x99a13504,
    0x665282d5, 0xa2df5e62, 0xf00187ff, 0x61da0cd0
};


// Wait for SHA512 controller STATUS.READY
static uint8_t wait_sha512_ctrl_ready(void) {
    uint32_t timeout = 20000;
    while (timeout--) {
        if (lsu_read_32(CLP_SHA512_REG_SHA512_STATUS) & SHA512_REG_SHA512_STATUS_READY_MASK)
            return 1;
    }
    return 0;
}

// Wait for SHA512 controller STATUS.VALID
static uint8_t wait_sha512_ctrl_valid(void) {
    uint32_t timeout = 20000;
    while (timeout--) {
        if (lsu_read_32(CLP_SHA512_REG_SHA512_STATUS) & SHA512_REG_SHA512_STATUS_VALID_MASK)
            return 1;
    }
    return 0;
}

// Recompute SHA-384 of the ICCM word stream using the SHA512 *controller*
// (the same peripheral used to extend PCR0 via sha_ctrl_extend)
// The SHA512 controller interprets its BLOCK registers as a
// big-endian byte stream (standard SHA-512), whereas the ICCM hash is defined
// over the little-endian bytes of each 32-bit ICCM word. Each ICCM word is
// therefore byte-swapped before being written to a BLOCK register so the
// controller hashes the same little-endian byte stream the HW snoop does.
// Firmware performs the SHA-512 padding by hand (append 0x80..., zero-fill,
// 128-bit big-endian bit length in the final block) and drives the multi-block
// init/next/last sequence. Writes the 12-dword (384-bit) digest into
// digest_out. Returns 1 on success, 0 on timeout.
static uint8_t sha512_ctrl_hash_iccm(uint32_t num_words, uint32_t *digest_out) {
    volatile uint32_t *iccm = (volatile uint32_t *)RV_ICCM_SADR;
    const uint32_t WORDS_PER_BLOCK = 32;                 // 1024-bit SHA-512 block
    uint32_t k = num_words + 1;                          // message words + 0x80 marker word
    uint32_t total_blocks = ((k + 4) + (WORDS_PER_BLOCK - 1)) / WORDS_PER_BLOCK;
    uint32_t total_words = total_blocks * WORDS_PER_BLOCK;
    uint64_t bitlen = (uint64_t)num_words * 32;          // each ICCM word contributes 32 bits

    for (uint32_t b = 0; b < total_blocks; b++) {
        if (!wait_sha512_ctrl_ready()) return 0;

        // Load one 1024-bit block into BLOCK[0:31], applying padding as needed.
        for (uint32_t j = 0; j < WORDS_PER_BLOCK; j++) {
            uint32_t w = b * WORDS_PER_BLOCK + j;
            uint32_t val;
            if (w < num_words) {
                // Byte-swap so the controller's big-endian BLOCK interpretation
                // hashes the little-endian bytes of the ICCM word.
                val = __builtin_bswap32(iccm[w]);        // message word (read back from ICCM)
            } else if (w == num_words) {
                val = 0x80000000;                        // SHA padding: 1 bit followed by zeros
            } else if (w >= total_words - 4) {
                // 128-bit big-endian message bit length in the final 4 words.
                uint32_t from_end = total_words - 1 - w; // 3,2,1,0
                if (from_end == 0)      val = (uint32_t)bitlen;
                else if (from_end == 1) val = (uint32_t)(bitlen >> 32);
                else                    val = 0x00000000; // upper 64 bits of the length
            } else {
                val = 0x00000000;                        // zero padding
            }
            lsu_write_32(CLP_SHA512_REG_SHA512_BLOCK_0 + (j * 4), val);
        }

        // Drive INIT on the first block, NEXT on subsequent blocks, with LAST
        // asserted on the final block so the core finalizes the digest.
        uint32_t ctrl = (2 << SHA512_REG_SHA512_CTRL_MODE_LOW); // SHA-384 mode
        if (b == 0) ctrl |= (1 << SHA512_REG_SHA512_CTRL_INIT_LOW);
        else        ctrl |= (1 << SHA512_REG_SHA512_CTRL_NEXT_LOW);
        if (b == total_blocks - 1) ctrl |= (1 << SHA512_REG_SHA512_CTRL_LAST_LOW);
        lsu_write_32(CLP_SHA512_REG_SHA512_CTRL, ctrl);
    }

    if (!wait_sha512_ctrl_valid()) return 0;

    volatile uint32_t *digest = (volatile uint32_t *)CLP_SHA512_REG_SHA512_DIGEST_0;
    for (int i = 0; i < ICCM_HASH_PCR_DWORDS; i++) {
        digest_out[i] = digest[i];
    }
    return 1;
}

// Independent readback cross-check of the HW ICCM hash result:
//   1. Read the ICCM contents back and recompute
//      iccm_digest = SHA-384(LE bytes of the ICCM words) using the SHA512
//      CONTROLLER (the same peripheral used to extend PCR0), independent of
//      the ICCM-hash snoop engine.
//   2. Clear spare PCR0 and extend it from zero with iccm_digest via the
//      regular SHA512 controller (pcr_hash_extend), reproducing the same
//      PCR = SHA-384(48_zeros || iccm_digest) computation the HW performs.
//   3. Confirm PCR0 == expected test vector AND PCR0 == PCR4.
// num_words is the number of ICCM dwords that were hashed by HW.
// Returns 1 on pass, 0 on fail.
static uint8_t iccm_readback_cross_check(uint32_t num_words,
                                         const uint32_t *expected,
                                         uint32_t iter) {
    // The controller streaming path used here does not cover the zero-length
    // case; the primary PCR4 check already validates it.
    if (num_words == 0) {
        VPRINTF(LOW, "Readback cross-check skipped for zero-length sequence\n");
        return 1;
    }

    // Clear spare PCR0 so it extends from zero.
    lsu_write_32(CLP_PV_REG_PCR_CTRL_0, PV_REG_PCR_CTRL_0_CLEAR_MASK);
    if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_0_0, 0)) {
        VPRINTF(ERROR, "FAIL: PCR0 not cleared before cross-check\n");
        return 0;
    }

    // Recompute the ICCM digest with the SHA512 controller (reads ICCM back
    // from memory), independently of the HW snoop.
    uint32_t iccm_digest[ICCM_HASH_PCR_DWORDS];
    if (!sha512_ctrl_hash_iccm(num_words, iccm_digest)) {
        VPRINTF(ERROR, "FAIL: SHA512 controller digest did not complete\n");
        return 0;
    }

    // Extend spare PCR0 from zero: PCR0 = SHA-384(48_zeros || iccm_digest).
    if (!sha_ctrl_extend(0, iccm_digest)) {
        VPRINTF(ERROR, "FAIL: sha_ctrl_extend of PCR0 timed out\n");
        return 0;
    }

    // PCR0 must equal the expected golden vector (proves readback + recompute
    // reproduces the golden hash) ...
    if (!check_pcr_match(CLP_PV_REG_PCR_ENTRY_0_0, expected, 0, iter)) {
        VPRINTF(ERROR, "FAIL: readback PCR0 != expected vector\n");
        return 0;
    }
    // ... and must equal PCR4 (proves the HW snoop hashed the same ICCM data).
    volatile uint32_t *pcr0 = (volatile uint32_t *)CLP_PV_REG_PCR_ENTRY_0_0;
    volatile uint32_t *pcr4 = (volatile uint32_t *)CLP_PV_REG_PCR_ENTRY_4_0;
    for (int i = 0; i < ICCM_HASH_PCR_DWORDS; i++) {
        if (pcr0[i] != pcr4[i]) {
            VPRINTF(ERROR, "FAIL: readback PCR0[%d]=0x%x != PCR4[%d]=0x%x\n",
                    i, pcr0[i], i, pcr4[i]);
            return 0;
        }
    }
    VPRINTF(LOW, "PASS: readback cross-check PCR0 == expected == PCR4\n");
    return 1;
}


void main(void) {

    uint8_t fail_cmd = 0x1;

    VPRINTF(LOW, "------------------------------------------\n");
    VPRINTF(LOW, " ICCM Hash Directed Test - Iteration %d\n", iteration);
    VPRINTF(LOW, "------------------------------------------\n");

    init_interrupts();

    // Check if subsystem mode is active (ICCM hash feature only in SS mode)
    uint32_t hw_config = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
    uint32_t ss_mode = (hw_config >> SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_LOW) & 0x1;

    if (!ss_mode) {
        // Passive mode: ICCM hash feature not present.
        // Verify PCR4 remains zero and pass.
        VPRINTF(LOW, "Passive mode: verifying PCR4 stays zero...\n");
        volatile uint32_t *pcr4 = (volatile uint32_t *)CLP_PV_REG_PCR_ENTRY_4_0;
        for (int i = 0; i < 12; i++) {
            if (pcr4[i] != 0) {
                VPRINTF(ERROR, "ERROR: PCR4[%d] = 0x%x (expected 0 in passive mode)\n",
                        i, pcr4[i]);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
        }
        VPRINTF(LOW, "PASS: PCR4 is zero (passive mode, feature not present)\n");
        SEND_STDOUT_CTRL(0xff);
        return;
    }

    // Subsystem mode: full ICCM hash test sequence
    volatile uint32_t *iccm = (volatile uint32_t *)RV_ICCM_SADR;

    // After fw_update_reset, iccm_unlock should have fired.
    // Verify PCR4 is cleared (except on first boot where it starts at 0).
    if (iteration > 0) {
        VPRINTF(LOW, "Checking PCR4 cleared after fw_update_reset...\n");
        if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_4_0, 4)) {
            VPRINTF(ERROR, "FAIL: PCR4 not cleared after iccm_unlock!\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }
        VPRINTF(LOW, "PCR4 confirmed cleared\n");
    }

    // HW auto-arms ICCM hash on the first ICCM write (or on iccm_lock for
    // the zero-length case), so no SHA acc lock acquire or MODE write is
    // needed from firmware.

    if (iteration == 0) {
        // Sequence 1: 64 words (256 bytes, spans 2 SHA-384 blocks)
        VPRINTF(LOW, "Seq1: Writing 64 words to ICCM...\n");
        for (uint32_t i = 0; i < 64; i++) {
            iccm[i] = 0x10 + i;
        }
    } else if (iteration == 1) {
        // Sequence 2: 28 words (112 bytes, forces extra padding block)
        VPRINTF(LOW, "Seq2: Writing 28 words to ICCM...\n");
        for (uint32_t i = 0; i < 28; i++) {
            iccm[i] = 0xBB00 + i;
        }
    } else if (iteration == 2) {
        // Sequence 3: 0 words (zero-length hash, lock immediately)
        VPRINTF(LOW, "Seq3: Zero-length ICCM hash (no writes)...\n");
    } else if (iteration == 3) {
        // Sequence 4: 32 words (128 bytes, exact SHA block boundary)
        VPRINTF(LOW, "Seq4: Writing 32 words to ICCM (exact block)...\n");
        for (uint32_t i = 0; i < 32; i++) {
            iccm[i] = 0xC000 + i;
        }
    } else if (iteration == 4) {
        // Sequence 5: 260 words (1040 bytes, large >1KB)
        VPRINTF(LOW, "Seq5: Writing 260 words to ICCM (large)...\n");
        for (uint32_t i = 0; i < 260; i++) {
            iccm[i] = 0xD000 + i;
        }
    } else {
        // Sequence 6: 64 words via tight back-to-back stores
        // Same data as Seq1 {0x10..0x4F}, but written as adjacent pairs
        // to maximize LSU bus buffer dword merging opportunities.
        // Uses volatile asm to prevent compiler reordering.
        VPRINTF(LOW, "Seq6: Tight memcpy 64 words (testing LSU merge)...\n");
        uint32_t base = (uint32_t)iccm;
        for (uint32_t i = 0; i < 64; i += 2) {
            uint32_t val0 = 0x10 + i;
            uint32_t val1 = 0x10 + i + 1;
            uint32_t addr0 = base + (i * 4);
            // Back-to-back sw to adjacent words -- LSU may merge into one 64-bit AXI txn
            __asm__ volatile (
                "sw %0, 0(%2)\n\t"
                "sw %1, 4(%2)\n\t"
                : : "r"(val0), "r"(val1), "r"(addr0) : "memory"
            );
        }
    }

    // Lock ICCM --> triggers hash finalization
    VPRINTF(LOW, "Locking ICCM...\n");
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK,
                 SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK);

    // Wait for PCR4 write
    if (!wait_pcr4_ready()) {
        VPRINTF(ERROR, "FAIL: Timed out waiting for PCR4 (iteration %d)\n", iteration);
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }

    // Verify PCR4
    const uint32_t *expected;
    uint32_t num_words;
    if (iteration == 0)      { expected = expected_seq1; num_words = 64;  }
    else if (iteration == 1) { expected = expected_seq2; num_words = 28;  }
    else if (iteration == 2) { expected = expected_seq3; num_words = 0;   }
    else if (iteration == 3) { expected = expected_seq4; num_words = 32;  }
    else if (iteration == 4) { expected = expected_seq5; num_words = 260; }
    else                     { expected = expected_seq6; num_words = 64;  }

    if (!check_pcr_match(CLP_PV_REG_PCR_ENTRY_4_0, expected, 4, iteration + 1)) {
        VPRINTF(ERROR, "FAIL: PCR4 mismatch on iteration %d\n", iteration);
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }
    VPRINTF(LOW, "PASS: Iteration %d PCR4 matches expected hash\n", iteration);

    // Independent cross-check: read ICCM back, recompute the hash with the
    // SHA accelerator, extend spare PCR0, and confirm it equals both the
    // expected vector and PCR4.
    if (!iccm_readback_cross_check(num_words, expected, iteration + 1)) {
        VPRINTF(ERROR, "FAIL: ICCM readback cross-check failed on iteration %d\n", iteration);
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }

    iteration++;

    if (iteration < 6) {
        // Trigger fw_update_reset -- boots back into main() with iccm_unlock
        VPRINTF(LOW, "Triggering fw_update_reset...\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET,
                     SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK);
        while(1); // Wait for reset
    }

    // All 6 sequences passed
    VPRINTF(LOW, "=== ALL 6 SEQUENCES PASSED ===\n");
    SEND_STDOUT_CTRL(0xff);
}
