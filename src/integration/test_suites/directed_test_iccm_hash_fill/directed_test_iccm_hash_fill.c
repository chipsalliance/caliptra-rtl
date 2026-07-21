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
// directed_test_iccm_hash_fill.c
// Directed test: fill the ENTIRE ICCM (exact ICCM size) with a simple
// incrementing dword-address pattern and verify PCR4 (Current) and PCR5
// (Journey) both contain the expected extend-from-zero digest.
//
// The ICCM is 256 KiB = 65536 dwords. To avoid shipping a giant test
// vector, each dword address i is written with value i. The HW ICCM-write
// snoop hashes the full write stream {0, 1, ..., 65535}.
//
//   iccm_digest = SHA-384(LE bytes of {0, 1, ..., ICCM_NUM_WORDS-1})
//   PCR4 = PCR5 = SHA-384(48_zeros || iccm_digest)   (extend from zero)
//
// This is a single-shot measurement (no fw_update_reset), so PCR4 and PCR5
// both extend from zero and are therefore equal.
//
// NOTE: This is a LONG test (65536 ICCM writes + full-ICCM SHA-384).

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

// Total ICCM size in dwords (256 KiB / 4).
#define ICCM_NUM_WORDS ((RV_ICCM_SIZE * 1024u) / 4u)

// Expected PCR4/PCR5 after extend-from-zero of the full-ICCM write stream
// {0, 1, ..., 65535}. Precomputed to match the RTL hashing convention
// (LE 32-bit words, no byte swap; PCR = SHA-384(48_zeros || iccm_digest)).
static const uint32_t expected_hash[12] = {
    0xb4165a3c, 0xed946423, 0x93ec24f4, 0x3b419452,
    0x24b396b7, 0x9c026ad9, 0x906b028d, 0xcc62018d,
    0xf1e00c0b, 0xaa85e4e3, 0x73592331, 0xf74dfbd7
};

void main(void) {

    uint8_t fail_cmd = 0x1;

    VPRINTF(LOW, "-------------------------------------------\n");
    VPRINTF(LOW, " ICCM Hash Fill Test (exact ICCM size)\n");
    VPRINTF(LOW, "-------------------------------------------\n");

    init_interrupts();

    // ICCM hash feature only exists in subsystem mode.
    uint32_t hw_config = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
    uint32_t ss_mode = (hw_config >> SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_LOW) & 0x1;

    if (!ss_mode) {
        // Passive mode: feature not present. Verify PCR4/PCR5 stay zero.
        VPRINTF(LOW, "Passive mode: verifying PCR4/PCR5 stay zero...\n");
        if (!check_pcr_zero(CLP_PV_REG_PCR_ENTRY_4_0, 4) ||
            !check_pcr_zero(CLP_PV_REG_PCR_ENTRY_5_0, 5)) {
            VPRINTF(ERROR, "ERROR: PCR4/PCR5 not zero in passive mode\n");
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }
        VPRINTF(LOW, "PASS: PCR4/PCR5 zero (passive mode, feature not present)\n");
        SEND_STDOUT_CTRL(0xff);
        return;
    }

    // Subsystem mode: fill the entire ICCM.
    volatile uint32_t *iccm = (volatile uint32_t *)RV_ICCM_SADR;

    VPRINTF(LOW, "Filling ICCM: %u dwords (incrementing pattern)...\n", ICCM_NUM_WORDS);
    for (uint32_t i = 0; i < ICCM_NUM_WORDS; i++) {
        iccm[i] = i;
    }

    // Lock ICCM --> triggers hash finalization + PCR4/PCR5 extend.
    VPRINTF(LOW, "Locking ICCM...\n");
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK,
                 SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK);

    if (!wait_pcr5_ready()) {
        VPRINTF(ERROR, "FAIL: Timed out waiting for PCR5\n");
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }

    // Dump expected vs actual PCR4/PCR5 for visibility.
    volatile uint32_t *pcr4 = (volatile uint32_t *)CLP_PV_REG_PCR_ENTRY_4_0;
    volatile uint32_t *pcr5 = (volatile uint32_t *)CLP_PV_REG_PCR_ENTRY_5_0;
    for (int i = 0; i < 12; i++) {
        VPRINTF(LOW, "PCR4[%2d] expected=0x%08x actual=0x%08x | PCR5[%2d] expected=0x%08x actual=0x%08x\n",
                i, expected_hash[i], pcr4[i], i, expected_hash[i], pcr5[i]);
    }

    // Verify PCR4 (Current) and PCR5 (Journey) both match. For a single-shot
    // measurement from cold boot, both extend from zero and are equal.
    if (!check_pcr_match(CLP_PV_REG_PCR_ENTRY_4_0, expected_hash, 4, 1)) {
        VPRINTF(ERROR, "FAIL: PCR4 mismatch (fill)\n");
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }
    if (!check_pcr_match(CLP_PV_REG_PCR_ENTRY_5_0, expected_hash, 5, 1)) {
        VPRINTF(ERROR, "FAIL: PCR5 mismatch (fill)\n");
        SEND_STDOUT_CTRL(fail_cmd);
        while(1);
    }

    VPRINTF(LOW, "=== PASS: ICCM fill PCR4 & PCR5 match expected ===\n");
    SEND_STDOUT_CTRL(0xff);
}
