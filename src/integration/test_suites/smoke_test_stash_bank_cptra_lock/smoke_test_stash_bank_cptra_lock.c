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
// Stash bank partial-populate + post-CPTRA_LOCK seal smoke test (RFC #673/694).
//
// Boot ordering:
//   1. BFM (write_stash_bank_partial): writes slot 0 dwords 0..9 only,
//      locks slot 0 via STASH_BANK_SOC_LOCK[0], asserts STASH_END_STASH.
//      Slots 1..7 are never written and are not SOC-locked.
//   2. uC drains the partial slot, asserts STASH_BANK_CPTRA_LOCK = 1.
//   3. uC requests BFM post-CPTRA_LOCK negative writes (STDOUT 0xc2).
//   4. BFM (write_stash_bank_post_cptra_lock) attempts writes to an
//      SOC-unlocked slot, a partial locked slot, STASH_BANK_SOC_LOCK, and
//      STASH_END_STASH - all must be silently dropped once CPTRA_LOCK=1.
//   5. uC verifies bank contents and STATUS mirrors are unchanged.

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include <stdint.h>
#include "printf.h"
#include "caliptra_isr.h"

volatile uint32_t* stdout = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Must match write_stash_bank_partial() in caliptra_top_tb_soc_bfm.sv.
#define PARTIAL_SLOT           0u
#define PARTIAL_NUM_DWORDS     10u
#define SOC_UNLOCKED_SLOT      1u
#define STASH_SLOT_DWORDS      26u

#define POST_CPTRA_SLOT0_DATA  0xC0FFEE00u
#define POST_CPTRA_SLOT1_DATA  0xC0FFEE01u

// NOTE: was 0xbd; moved to 0xc2 to keep the stash-bank STDOUT hooks (0xc1/0xc2)
// contiguous and clear of the boot-phase-enforcement opcode range (0xbb-0xbf).
#define POST_CPTRA_STDOUT_CTRL 0xc2u
#define POST_CPTRA_LOCK_DONE   0x600d573bu

#define EXPECTED_SLOT_LOCKED   0x01u
#define EXPECTED_STATUS        0x301u  // slot_locked=0x01 | end_stash | cptra_lock

static inline uint32_t stash_pattern(uint32_t slot, uint32_t dword) {
    return (slot << 24) | (dword << 8) | 0xA5u;
}

static inline uint32_t slot_addr(uint32_t slot, uint32_t dword) {
    return CLP_SOC_IFC_REG_STASH_BANK_SLOT_DATA_0 + 4u * (slot * STASH_SLOT_DWORDS + dword);
}

static void fail(const char *why, uint32_t a, uint32_t b) {
    VPRINTF(ERROR, "ERROR: %s (got 0x%08x, expected 0x%08x)\n", why, a, b);
    SEND_STDOUT_CTRL(0x1);
    while (1);
}

static void verify_partial_bank(void) {
    uint32_t got;
    uint32_t want;

    for (uint32_t d = 0; d < PARTIAL_NUM_DWORDS; d++) {
        got  = lsu_read_32(slot_addr(PARTIAL_SLOT, d));
        want = stash_pattern(PARTIAL_SLOT, d);
        if (got != want) {
            VPRINTF(ERROR, "ERROR: partial slot %0d dword %0d\n", PARTIAL_SLOT, d);
            fail("partial slot data mismatch", got, want);
        }
    }
    for (uint32_t d = PARTIAL_NUM_DWORDS; d < STASH_SLOT_DWORDS; d++) {
        got = lsu_read_32(slot_addr(PARTIAL_SLOT, d));
        if (got != 0u) {
            VPRINTF(ERROR, "ERROR: partial slot %0d dword %0d should be 0\n", PARTIAL_SLOT, d);
            fail("unwritten partial slot dword nonzero", got, 0u);
        }
    }
    for (uint32_t s = 1; s < 8; s++) {
        for (uint32_t d = 0; d < STASH_SLOT_DWORDS; d++) {
            got = lsu_read_32(slot_addr(s, d));
            if (got != 0u) {
                VPRINTF(ERROR, "ERROR: SOC-unlocked slot %0d dword %0d\n", s, d);
                fail("SOC-unlocked slot should be zero", got, 0u);
            }
        }
    }
}

static void verify_post_cptra_sentinels_absent(void) {
    uint32_t got;

    got = lsu_read_32(slot_addr(PARTIAL_SLOT, 5));
    if (got == POST_CPTRA_SLOT0_DATA) {
        fail("post-CPTRA_LOCK slot 0 rewrite landed", got, stash_pattern(PARTIAL_SLOT, 5));
    }
    got = lsu_read_32(slot_addr(SOC_UNLOCKED_SLOT, 0));
    if (got == POST_CPTRA_SLOT1_DATA) {
        fail("post-CPTRA_LOCK slot 1 write landed", got, 0u);
    }
}

void main(void) {
    uint32_t status;
    uint32_t slot_locked_mask;

    VPRINTF(LOW, "----------------------------------------------------\n");
    VPRINTF(LOW, " Caliptra Stash Bank CPTRA_LOCK Smoke Test\n");
    VPRINTF(LOW, "----------------------------------------------------\n");

    // Step A: BFM finished; end_stash must be set.
    do {
        status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    } while ((status & SOC_IFC_REG_STASH_BANK_STATUS_END_STASH_MASK) == 0);
    VPRINTF(LOW, "FW: STASH_BANK_STATUS = 0x%08x (end_stash observed)\n", status);

    slot_locked_mask = (status & SOC_IFC_REG_STASH_BANK_STATUS_SLOT_LOCKED_MASK)
                       >> SOC_IFC_REG_STASH_BANK_STATUS_SLOT_LOCKED_LOW;
    if (slot_locked_mask != EXPECTED_SLOT_LOCKED) {
        fail("partial populate should lock slot 0 only", slot_locked_mask, EXPECTED_SLOT_LOCKED);
    }
    if ((status & SOC_IFC_REG_STASH_BANK_STATUS_CPTRA_LOCK_MASK) != 0) {
        fail("cptra_lock should be 0 before runtime drain", status, 0x100);
    }

    // Step B: verify partial bank layout from BFM.
    verify_partial_bank();
    VPRINTF(LOW, "FW: partial slot %0d (%0d dwords) verified; slots 1..7 are zero\n",
            PARTIAL_SLOT, PARTIAL_NUM_DWORDS);

    // Step C: simulate runtime drain (read partial slot contents).
    for (uint32_t d = 0; d < PARTIAL_NUM_DWORDS; d++) {
        (void)lsu_read_32(slot_addr(PARTIAL_SLOT, d));
    }
    VPRINTF(LOW, "FW: drained partial slot %0d\n", PARTIAL_SLOT);

    // Step D: assert CPTRA_LOCK (RFC 694 §4.4 / §7.3 post-drain seal).
    lsu_write_32(CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK, 1);
    status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    if ((status & SOC_IFC_REG_STASH_BANK_STATUS_CPTRA_LOCK_MASK) == 0) {
        fail("cptra_lock mirror should be 1 after FW write", status, EXPECTED_STATUS);
    }
    VPRINTF(LOW, "FW: STASH_BANK_CPTRA_LOCK asserted (STATUS=0x%08x)\n", status);

    // Step E: trigger BFM post-CPTRA_LOCK negative writes.
    VPRINTF(LOW, "FW: requesting BFM post-CPTRA_LOCK writes (STDOUT 0x%02x)\n", POST_CPTRA_STDOUT_CTRL);
    SEND_STDOUT_CTRL(POST_CPTRA_STDOUT_CTRL);
    do {
    } while (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) != POST_CPTRA_LOCK_DONE);
    VPRINTF(LOW, "FW: BFM post-CPTRA_LOCK negative sequence completed\n");

    // Step F: bank contents and STATUS must be unchanged.
    status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    if (status != EXPECTED_STATUS) {
        fail("STATUS changed after post-CPTRA_LOCK writes", status, EXPECTED_STATUS);
    }
    verify_partial_bank();
    verify_post_cptra_sentinels_absent();
    VPRINTF(LOW, "FW: post-CPTRA_LOCK SoC writes dropped; STATUS=0x%08x\n", status);

    VPRINTF(LOW, "FW: stash bank CPTRA_LOCK checks passed\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
