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
// Checks that ZEROIZE cancels a staged-but-unfinished PCR hash extend so that
// the following ordinary SHA-512 operation returns its correct digest in the
// software DIGEST registers.
//
//   A: baseline ordinary hash                                    -> KAT
//   B: control, ZEROIZE without a PCR request, ordinary hash      -> KAT
//   C: PCR hash-extend read, ZEROIZE before LAST, ordinary hash   -> KAT
//   D: second ordinary hash after C (stale-state persistence)     -> KAT
//
// Expected digest is the FIPS 180-2 SHA-512("abc") known answer, independent
// of the DUT. Any mismatch, timeout or unexpected status fails the test.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include <stdint.h>
#include "printf.h"
#include "riscv_hw_if.h"
#include "sha512.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define POLL_LIMIT      100000
#define PCR_ENTRY       0
#define ZEROIZE_SETTLE  20

static const uint32_t abc_block[32] = {
    0x61626380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x00000018
};

// FIPS 180-2 Appendix C.1: SHA-512("abc")
static const uint32_t abc_sha512_kat[16] = {
    0xDDAF35A1, 0x93617ABA, 0xCC417349, 0xAE204131,
    0x12E6FA4E, 0x89A97EA2, 0x0A9EEEE6, 0x4B55D39A,
    0x2192992A, 0x274FC1A8, 0x36BA3C23, 0xA3FEEBBD,
    0x454D4423, 0x643CE80E, 0x2A9AC94F, 0xA54CA49F
};

static void fail(const char *msg) {
    VPRINTF(ERROR, "FAIL: %s\n", msg);
    SEND_STDOUT_CTRL(0x1);
    while (1);
}

static void poll_mask(uint32_t addr, uint32_t mask, uint32_t want, const char *what) {
    for (uint32_t i = 0; i < POLL_LIMIT; i++) {
        if ((lsu_read_32(addr) & mask) == want) return;
    }
    VPRINTF(ERROR, "Timeout waiting for %s (reg=0x%x)\n", what, lsu_read_32(addr));
    fail("poll timeout");
}

static void zeroize_and_settle(void) {
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL, SHA512_REG_SHA512_CTRL_ZEROIZE_MASK);
    for (volatile int i = 0; i < ZEROIZE_SETTLE; i++);
    poll_mask(CLP_SHA512_REG_SHA512_STATUS, SHA512_REG_SHA512_STATUS_READY_MASK,
              SHA512_REG_SHA512_STATUS_READY_MASK, "SHA READY after ZEROIZE");
}

// Single-block ordinary SHA-512 (INIT, no LAST); returns number of mismatching dwords.
static uint32_t ordinary_hash_and_check(const char *phase) {
    uint32_t digest[16];
    uint32_t mismatches = 0;
    uint32_t zero_words = 0;
    uint32_t status;

    poll_mask(CLP_SHA512_REG_SHA512_STATUS, SHA512_REG_SHA512_STATUS_READY_MASK,
              SHA512_REG_SHA512_STATUS_READY_MASK, "SHA READY before hash");

    for (uint32_t i = 0; i < 32; i++) {
        lsu_write_32(CLP_SHA512_REG_SHA512_BLOCK_0 + 4 * i, abc_block[i]);
    }

    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL,
                 SHA512_REG_SHA512_CTRL_INIT_MASK |
                 ((SHA512_512_MODE << SHA512_REG_SHA512_CTRL_MODE_LOW) & SHA512_REG_SHA512_CTRL_MODE_MASK));

    poll_mask(CLP_SHA512_REG_SHA512_STATUS,
              SHA512_REG_SHA512_STATUS_READY_MASK | SHA512_REG_SHA512_STATUS_VALID_MASK,
              SHA512_REG_SHA512_STATUS_READY_MASK | SHA512_REG_SHA512_STATUS_VALID_MASK,
              "SHA READY&VALID after hash");

    status = lsu_read_32(CLP_SHA512_REG_SHA512_STATUS);
    for (uint32_t i = 0; i < 16; i++) {
        digest[i] = lsu_read_32(CLP_SHA512_REG_SHA512_DIGEST_0 + 4 * i);
        if (digest[i] != abc_sha512_kat[i]) mismatches++;
        if (digest[i] == 0) zero_words++;
    }

    VPRINTF(LOW, "[%s] SHA_STATUS=0x%x GEN_PCR_HASH_STATUS=0x%x VAULT_RD_STATUS=0x%x KV_WR_STATUS=0x%x\n",
            phase, status,
            lsu_read_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_STATUS),
            lsu_read_32(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS),
            lsu_read_32(CLP_SHA512_REG_SHA512_KV_WR_STATUS));
    for (uint32_t i = 0; i < 16; i++) {
        VPRINTF(LOW, "[%s] DIGEST[%d] actual=0x%x expected=0x%x%s\n", phase, i,
                digest[i], abc_sha512_kat[i], (digest[i] != abc_sha512_kat[i]) ? "  <-- MISMATCH" : "");
    }
    VPRINTF(LOW, "[%s] mismatching dwords=%d, all-zero dwords=%d\n", phase, mismatches, zero_words);
    return mismatches;
}

void main() {
    uint32_t mism_c, mism_d, rd_status;

    VPRINTF(LOW, "----------------------------------------------------\n");
    VPRINTF(LOW, " SHA512 ZEROIZE during unfinished PCR hash extend\n");
    VPRINTF(LOW, "----------------------------------------------------\n");

    VPRINTF(LOW, "Phase A: baseline ordinary SHA-512\n");
    if (ordinary_hash_and_check("A") != 0) fail("Phase A baseline digest mismatch");

    VPRINTF(LOW, "Phase B: ZEROIZE without PCR request, then ordinary SHA-512\n");
    zeroize_and_settle();
    if (ordinary_hash_and_check("B") != 0) fail("Phase B control digest mismatch");

    VPRINTF(LOW, "Phase C: stage PCR%d hash extend, ZEROIZE before completion\n", PCR_ENTRY);
    poll_mask(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS, SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK,
              SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK, "VAULT_RD READY before request");
    lsu_write_32(CLP_SHA512_REG_SHA512_VAULT_RD_CTRL,
                 SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_MASK |
                 ((PCR_ENTRY << SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_LOW) & SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_MASK) |
                 SHA512_REG_SHA512_VAULT_RD_CTRL_PCR_HASH_EXTEND_MASK);
    poll_mask(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS,
              SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK | SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_MASK,
              SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK | SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_MASK,
              "VAULT_RD READY&VALID");
    rd_status = lsu_read_32(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);
    if (rd_status & SHA512_REG_SHA512_VAULT_RD_STATUS_ERROR_MASK) {
        VPRINTF(ERROR, "VAULT_RD_STATUS=0x%x\n", rd_status);
        fail("PCR read reported error; scenario not established");
    }
    VPRINTF(LOW, "[C] PCR read done: VAULT_RD_STATUS=0x%x GEN_PCR_HASH_STATUS=0x%x\n",
            rd_status, lsu_read_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_STATUS));

    zeroize_and_settle();
    VPRINTF(LOW, "[C] after ZEROIZE: SHA_STATUS=0x%x GEN_PCR_HASH_STATUS=0x%x\n",
            lsu_read_32(CLP_SHA512_REG_SHA512_STATUS),
            lsu_read_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_STATUS));

    mism_c = ordinary_hash_and_check("C");

    VPRINTF(LOW, "Phase D: second ordinary SHA-512 (persistence check)\n");
    mism_d = ordinary_hash_and_check("D");

    if ((lsu_read_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_STATUS) &
         SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_READY_MASK) == 0) {
        VPRINTF(ERROR, "GEN_PCR_HASH_STATUS.READY stuck low after ZEROIZE\n");
        if ((mism_c | mism_d) == 0) fail("GEN_PCR_HASH not ready after cancelled extend");
    }
    if (mism_c != 0) fail("Phase C: ordinary hash after cancelled PCR extend returned wrong DIGEST");
    if (mism_d != 0) fail("Phase D: stale PCR extend state persisted");

    VPRINTF(LOW, "All phases matched SHA-512 KAT\n");
    SEND_STDOUT_CTRL(0xff);
}
