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
// directed_test_iccm_hash_sizes.c
// ICCM hash size-boundary directed test. Closes coverpoint and cross bins
// in iccm_hash_cov_grp that the existing test set never reaches:
//
// Seq A: 1 word    (4 bytes)    -> iccm_byte_count_cp.min_write,
//                                  iccm_byte_countXextra_pad.(min_write,0)
// Seq B: 60 words  (240 bytes)  -> iccm_byte_countXextra_pad.(multi_block,1)
//                                  (last block remainder 112 forces extra pad)
// Seq C: 284 words (1136 bytes) -> iccm_byte_countXextra_pad.(large_sz,1)
//                                  (last block remainder 112 forces extra pad)

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

// Persistent state across fw_update_reset
static uint32_t iteration __attribute__ ((section(".dccm.persistent"))) = 0;

// PCR4 = SHA-384(48_bytes_of_zeros || SHA-384(iccm_write_stream))
// iccm_write_stream is LE-packed 32-bit words (no byte swap).

// Seq A: 1 word {0xA0000001} - 4 bytes
static const uint32_t expected_min_write_1w[12] = {
    0x1b7e3bed, 0x5ed70671, 0x2c2cfdf1, 0xe3e7bd11,
    0x0b04a176, 0x49e930ef, 0x55cfe8a6, 0x1a198c22,
    0xd3213334, 0xae16fb88, 0xd49841e1, 0x474a89d0
};

// Seq B: 60 words {0xB0000000..0xB000003B} - 240 bytes
static const uint32_t expected_multi_extra_pad_60w[12] = {
    0x24c7846c, 0xad2615f9, 0xfabd075a, 0xcb9a0f7f,
    0x75ab8c14, 0x3a1b9019, 0x995ff767, 0x160943e0,
    0x8cecdcdf, 0x74d0ae45, 0x960ccc7f, 0x79343063
};

// Seq C: 284 words {0xC0000000..0xC000011B} - 1136 bytes
static const uint32_t expected_large_extra_pad_284w[12] = {
    0x7014fa7e, 0xf4305fd3, 0xfbc23e87, 0x59a03f3d,
    0xd5b41b66, 0x96a882e2, 0xb661bb02, 0x6c3f5fa4,
    0xad8b309f, 0x2a8a768f, 0x8d903431, 0xa83fdd79
};

void main(void) {

    uint8_t fail_cmd = 0x1;

    VPRINTF(LOW, "------------------------------------------\n");
    VPRINTF(LOW, " ICCM Hash Sizes Test - Iteration %d\n", iteration);
    VPRINTF(LOW, "------------------------------------------\n");

    init_interrupts();

    uint32_t hw_config = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
    uint32_t ss_mode = (hw_config >> SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_LOW) & 0x1;

    if (!ss_mode) {
        VPRINTF(LOW, "Passive mode: ICCM hash not present, skipping. PASS\n");
        SEND_STDOUT_CTRL(0xff);
        return;
    }

    volatile uint32_t *iccm = (volatile uint32_t *)RV_ICCM_SADR;

    // After fw_update_reset, PCR4 should be cleared by iccm_unlock
    if (iteration > 0) {
        VPRINTF(LOW, "Checking PCR4 cleared after fw_update_reset...\n");
        if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_4_0, 4)) {
            VPRINTF(ERROR, "FAIL: PCR4 not cleared after iccm_unlock!\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }
        VPRINTF(LOW, "PCR4 confirmed cleared\n");
    }

    const uint32_t *expected;

    if (iteration == 0) {
        // Seq A: 1 word -> min_write bin
        VPRINTF(LOW, "SeqA: Writing 1 word to ICCM (min_write)...\n");
        iccm[0] = 0xA0000001;
        expected = expected_min_write_1w;
    } else if (iteration == 1) {
        // Seq B: 60 words = 240 bytes (240 mod 128 = 112, forces extra pad)
        VPRINTF(LOW, "SeqB: Writing 60 words to ICCM (multi_block + extra_pad)...\n");
        for (uint32_t i = 0; i < 60; i++) {
            iccm[i] = 0xB0000000 + i;
        }
        expected = expected_multi_extra_pad_60w;
    } else {
        // Seq C: 284 words = 1136 bytes (1136 mod 128 = 112, forces extra pad)
        VPRINTF(LOW, "SeqC: Writing 284 words to ICCM (large_sz + extra_pad)...\n");
        for (uint32_t i = 0; i < 284; i++) {
            iccm[i] = 0xC0000000 + i;
        }
        expected = expected_large_extra_pad_284w;
    }

    // Lock ICCM -> hash finalization
    VPRINTF(LOW, "Locking ICCM...\n");
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK,
                 SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK);

    if (!wait_pcr4_ready()) {
        VPRINTF(ERROR, "FAIL: Timed out waiting for PCR4 (iteration %d)\n", iteration);
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }

    if (!check_pcr_match(CLP_PV_REG_PCR_ENTRY_4_0, expected, 4, iteration + 1)) {
        VPRINTF(ERROR, "FAIL: PCR4 mismatch on iteration %d\n", iteration);
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }
    VPRINTF(LOW, "PASS: Iteration %d PCR4 matches expected hash\n", iteration);

    iteration++;

    if (iteration < 3) {
        VPRINTF(LOW, "Triggering fw_update_reset...\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET,
                     SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK);
        while(1);
    }

    VPRINTF(LOW, "=== ALL 3 SIZE SEQUENCES PASSED ===\n");
    SEND_STDOUT_CTRL(0xff);
}
