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
// Sequence 5: 260 words (1040 bytes, large >1KB)          --> lock --> check PCR4 --> PASS

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

// Expected SHA-384 digests for each sequence (LE byte order into SHA)
// Sequence 1: 64 words {0x10..0x4F} - 256 bytes (multi-block, 2 SHA-384 blocks)
static const uint32_t expected_seq1[12] = {
    0xf845605a, 0x4d8bbb7b, 0x8d4101db, 0xec07b679,
    0x848dc298, 0x46dbdf5c, 0x42406eea, 0xe55e7daa,
    0xa8b7e273, 0xd804e6b9, 0x98ed5e16, 0x0dd2fb8b
};

// Sequence 2: 28 words {0xBB00..0xBB1B} - 112 bytes (forces extra padding block)
static const uint32_t expected_seq2[12] = {
    0xdd4f6152, 0x7ff8693f, 0x8d2862ae, 0xdcf878fd,
    0xa9e9bc21, 0x34e8749f, 0x8ea2e3e4, 0x6bab5729,
    0xb8ee6dd8, 0x94a590ff, 0x9c5a259e, 0x25c2c64c
};

// Sequence 3: 0 words - 0 bytes (zero-length SHA-384)
static const uint32_t expected_seq3[12] = {
    0x38b060a7, 0x51ac9638, 0x4cd9327e, 0xb1b1e36a,
    0x21fdb711, 0x14be0743, 0x4c0cc7bf, 0x63f6e1da,
    0x274edebf, 0xe76f65fb, 0xd51ad2f1, 0x4898b95b
};

// Sequence 4: 32 words {0xC000..0xC01F} - 128 bytes (exact SHA-384 block boundary)
static const uint32_t expected_seq4[12] = {
    0xc95e0b92, 0xd0adead5, 0x3cd89140, 0x4f52b384,
    0xebd27444, 0x8d01157f, 0xb4352919, 0x1d6e9240,
    0xb0133c4d, 0x66c97a0a, 0x3caeceba, 0x699d1be9
};

// Sequence 5: 260 words {0xD000..0xD103} - 1040 bytes (large, >1KB)
static const uint32_t expected_seq5[12] = {
    0xa1531b27, 0xd65234c0, 0xb28cdb72, 0x52f090a6,
    0x7e151e14, 0xe1ca70e8, 0x60738d63, 0xff244a0f,
    0xcddb352a, 0xa2e62f2f, 0xb2a7a5cf, 0x2f35c7e2
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
    } else {
        // Sequence 5: 260 words (1040 bytes, large >1KB)
        VPRINTF(LOW, "Seq5: Writing 260 words to ICCM (large)...\n");
        for (uint32_t i = 0; i < 260; i++) {
            iccm[i] = 0xD000 + i;
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
    else expected = expected_seq5;

    if (!check_pcr4(expected, iteration + 1)) {
        VPRINTF(ERROR, "FAIL: PCR4 mismatch on iteration %d\n", iteration);
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }
    VPRINTF(LOW, "PASS: Iteration %d PCR4 matches expected hash\n", iteration);

    iteration++;

    if (iteration < 5) {
        // Trigger fw_update_reset -- boots back into main() with iccm_unlock
        VPRINTF(LOW, "Triggering fw_update_reset...\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET,
                     SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK);
        while(1); // Wait for reset
    }

    // All 5 sequences passed
    VPRINTF(LOW, "=== ALL 5 SEQUENCES PASSED ===\n");
    SEND_STDOUT_CTRL(0xff);
}
