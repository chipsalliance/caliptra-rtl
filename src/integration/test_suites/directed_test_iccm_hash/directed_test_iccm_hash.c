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

// ICCM_MODE field (bit 2 of MODE register)
#ifndef SHA512_ACC_CSR_MODE_ICCM_MODE_MASK
#define SHA512_ACC_CSR_MODE_ICCM_MODE_MASK (0x4)
#endif

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

// Acquire SHA acc lock: release reset-default lock, then read-to-acquire
static void acquire_sha_lock(void) {
    uint32_t reg;
    lsu_write_32(CLP_SHA512_ACC_CSR_LOCK, SHA512_ACC_CSR_LOCK_LOCK_MASK);
    do {
        reg = lsu_read_32(CLP_SHA512_ACC_CSR_LOCK);
    } while (reg & SHA512_ACC_CSR_LOCK_LOCK_MASK);
}

// Wait for PCR4 to be written (poll dword[0] non-zero)
static uint8_t wait_pcr4_ready(void) {
    uint32_t timeout = 20000;
    while (timeout--) {
        if (lsu_read_32(CLP_PV_REG_PCR_ENTRY_4_0) != 0) return 1;
    }
    return 0;
}

// Verify PCR4 against expected digest
static uint8_t check_pcr4(const uint32_t *expected, uint32_t seq_num) {
    volatile uint32_t *pcr4 = (volatile uint32_t *)CLP_PV_REG_PCR_ENTRY_4_0;
    uint8_t pass = 1;
    for (int i = 0; i < 12; i++) {
        uint32_t actual = pcr4[i];
        if (actual != expected[i]) {
            VPRINTF(ERROR, "ERROR: Seq%d PCR4[%d] mismatch! Got 0x%x, expected 0x%x\n",
                    seq_num, i, actual, expected[i]);
            pass = 0;
        }
    }
    return pass;
}

// Verify PCR4 is all zeros (cleared after iccm_unlock)
static uint8_t check_pcr4_cleared(void) {
    volatile uint32_t *pcr4 = (volatile uint32_t *)CLP_PV_REG_PCR_ENTRY_4_0;
    for (int i = 0; i < 12; i++) {
        if (pcr4[i] != 0) {
            VPRINTF(ERROR, "ERROR: PCR4[%d] not cleared! Got 0x%x\n", i, pcr4[i]);
            return 0;
        }
    }
    return 1;
}

void main(void) {

    uint8_t fail_cmd = 0x1;

    VPRINTF(LOW, "------------------------------------------\n");
    VPRINTF(LOW, " ICCM Hash Directed Test - Iteration %d\n", iteration);
    VPRINTF(LOW, "------------------------------------------\n");

    init_interrupts();

    volatile uint32_t *iccm = (volatile uint32_t *)RV_ICCM_SADR;

    // After fw_update_reset, iccm_unlock should have fired.
    // Verify PCR4 is cleared (except on first boot where it starts at 0).
    if (iteration > 0) {
        VPRINTF(LOW, "Checking PCR4 cleared after fw_update_reset...\n");
        if (!check_pcr4_cleared()) {
            VPRINTF(ERROR, "FAIL: PCR4 not cleared after iccm_unlock!\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }
        VPRINTF(LOW, "PCR4 confirmed cleared\n");
    }

    // Acquire SHA acc lock and set ICCM_MODE
    acquire_sha_lock();
    lsu_write_32(CLP_SHA512_ACC_CSR_MODE, SHA512_ACC_CSR_MODE_ICCM_MODE_MASK);

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
    if (iteration == 0) expected = expected_seq1;
    else if (iteration == 1) expected = expected_seq2;
    else if (iteration == 2) expected = expected_seq3;
    else if (iteration == 3) expected = expected_seq4;
    else if (iteration == 4) expected = expected_seq5;
    else expected = expected_seq6;

    if (!check_pcr4(expected, iteration + 1)) {
        VPRINTF(ERROR, "FAIL: PCR4 mismatch on iteration %d\n", iteration);
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }
    VPRINTF(LOW, "PASS: Iteration %d PCR4 matches expected hash\n", iteration);

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
