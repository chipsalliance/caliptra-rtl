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
// Shared library for ICCM hash measurement tests.

#include "iccm_hash.h"
#include "printf.h"

// Expected PCR after run_default_iccm_hash from zero.
// Default ICCM data is 64 words {0x10..0x4F} -- same as directed_test_iccm_hash sequence 1.
const uint32_t expected_default_iccm_hash_pcr[ICCM_HASH_PCR_DWORDS] = {
    0x73c26a32, 0x28bce060, 0x94b092a6, 0x4d3c6007,
    0xbe359bab, 0xa1b76c71, 0x812f325a, 0x99a13504,
    0x665282d5, 0xa2df5e62, 0xf00187ff, 0x61da0cd0
};

uint8_t acquire_sha_lock(void) {
    uint32_t reg;
    uint32_t timeout = 20000;
    lsu_write_32(CLP_SHA512_ACC_CSR_LOCK, SHA512_ACC_CSR_LOCK_LOCK_MASK);
    while (timeout--) {
        reg = lsu_read_32(CLP_SHA512_ACC_CSR_LOCK);
        if (!(reg & SHA512_ACC_CSR_LOCK_LOCK_MASK)) return 1;
    }
    return 0;
}

uint8_t wait_pcr4_ready(void) {
    uint32_t timeout = 20000;
    while (timeout--) {
        if (lsu_read_32(CLP_PV_REG_PCR_ENTRY_4_0) != 0) return 1;
    }
    return 0;
}

uint8_t wait_pcr5_ready(void) {
    uint32_t timeout = 20000;
    while (timeout--) {
        if (lsu_read_32(CLP_PV_REG_PCR_ENTRY_5_0) != 0) return 1;
    }
    return 0;
}

uint8_t run_default_iccm_hash(void) {
    volatile uint32_t *iccm = (volatile uint32_t *)RV_ICCM_SADR;
    // ICCM-write snoop engages the hash automatically on the first write;
    // no firmware-side arming or lock acquisition is required.
    for (uint32_t i = 0; i < ICCM_HASH_DEFAULT_NUM_WORDS; i++) {
        iccm[i] = ICCM_HASH_DEFAULT_WORD(i);
    }
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK,
                 SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK);
    return wait_pcr4_ready();
}

// Wait for SHA512 controller READY
static uint8_t wait_sha512_ready(void) {
    uint32_t timeout = 20000;
    while (timeout--) {
        uint32_t reg = lsu_read_32(CLP_SHA512_REG_SHA512_STATUS);
        if (reg & SHA512_REG_SHA512_STATUS_READY_MASK) return 1;
    }
    return 0;
}

// Wait for VAULT_RD_STATUS.VALID (PCR loaded into BLOCK[0:11])
static uint8_t wait_vault_rd_valid(void) {
    uint32_t timeout = 20000;
    while (timeout--) {
        uint32_t reg = lsu_read_32(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);
        if (reg & SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_MASK) return 1;
    }
    return 0;
}

uint8_t sha_ctrl_extend(uint32_t pcr_entry, const uint32_t *digest) {
    if (!wait_sha512_ready()) return 0;
    lsu_write_32(CLP_SHA512_REG_SHA512_VAULT_RD_CTRL,
                 (1 << SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_LOW) |
                 (pcr_entry << SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_LOW) |
                 (1 << SHA512_REG_SHA512_VAULT_RD_CTRL_PCR_HASH_EXTEND_LOW));
    if (!wait_vault_rd_valid()) return 0;
    for (int i = 0; i < ICCM_HASH_PCR_DWORDS; i++) {
        lsu_write_32(CLP_SHA512_REG_SHA512_BLOCK_12 + (i * 4), digest[i]);
    }
    lsu_write_32(CLP_SHA512_REG_SHA512_BLOCK_24, 0x80000000);
    for (int i = 25; i < 31; i++) {
        lsu_write_32(CLP_SHA512_REG_SHA512_BLOCK_0 + (i * 4), 0x00000000);
    }
    lsu_write_32(CLP_SHA512_REG_SHA512_BLOCK_0 + (31 * 4), 0x00000300);
    if (!wait_sha512_ready()) return 0;
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL,
                 (1 << SHA512_REG_SHA512_CTRL_INIT_LOW) |
                 (2 << SHA512_REG_SHA512_CTRL_MODE_LOW) |
                 (1 << SHA512_REG_SHA512_CTRL_LAST_LOW));
    return wait_sha512_ready();
}

void fw_write_attack(uint32_t pcr_base) {
    for (int i = 0; i < ICCM_HASH_PCR_DWORDS; i++) {
        lsu_write_32(pcr_base + (i * 4), 0xDEADBEEF);
    }
}

void snapshot_pcr(uint32_t pcr_base, uint32_t *out) {
    volatile uint32_t *pcr = (volatile uint32_t *)pcr_base;
    for (int i = 0; i < ICCM_HASH_PCR_DWORDS; i++) {
        out[i] = pcr[i];
    }
}

uint8_t check_pcr_zero(uint32_t pcr_base, uint32_t pcr_idx) {
    volatile uint32_t *pcr = (volatile uint32_t *)pcr_base;
    uint8_t pass = 1;
    for (int i = 0; i < ICCM_HASH_PCR_DWORDS; i++) {
        if (pcr[i] != 0) {
            VPRINTF(ERROR, "ERROR: PCR%d[%d] non-zero! Got 0x%x\n", pcr_idx, i, pcr[i]);
            pass = 0;
        }
    }
    return pass;
}

uint8_t check_pcr_nonzero(uint32_t pcr_base, uint32_t pcr_idx) {
    volatile uint32_t *pcr = (volatile uint32_t *)pcr_base;
    for (int i = 0; i < ICCM_HASH_PCR_DWORDS; i++) {
        if (pcr[i] != 0) return 1;
    }
    VPRINTF(ERROR, "ERROR: PCR%d unexpectedly all zero\n", pcr_idx);
    return 0;
}

uint8_t check_pcr_match(uint32_t pcr_base, const uint32_t *expected,
                             uint32_t pcr_idx, uint32_t iter) {
    volatile uint32_t *pcr = (volatile uint32_t *)pcr_base;
    uint8_t pass = 1;
    for (int i = 0; i < ICCM_HASH_PCR_DWORDS; i++) {
        if (pcr[i] != expected[i]) {
            VPRINTF(ERROR, "ERROR: Iter%d PCR%d[%d] mismatch! Got 0x%x, expected 0x%x\n",
                    iter, pcr_idx, i, pcr[i], expected[i]);
            pass = 0;
        }
    }
    return pass;
}
