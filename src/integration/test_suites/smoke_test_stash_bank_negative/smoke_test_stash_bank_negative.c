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
// Stash measurement register bank NEGATIVE-path smoke test (RFC #673).
//
// Boot ordering:
//   1. BFM populates slots 0..7, locks them, then (negative path only,
//      before STASH_END_STASH):
//      - Step 3b: STASH_BANK_SOC_LOCK write with one bit cleared (W1S ignored).
//      - Step 3c: rewrite a locked slot with 0xFEED_FACE (SOC_LOCK-only drop).
//      Then asserts STASH_END_STASH (write_stash_bank()).
//   2. BFM runs write_stash_bank_negative():
//      - Rewrites slot 0 dword 0 with 0xDEAD_BEEF (SOC_LOCK + end_stash).
//      - Bad-PAUSER write to slot 1 dword 0 with 0xBAAD_F00D.
//      - STASH_END_STASH write of 0 (W1S ignored).
//      - SoC write to STASH_BANK_CPTRA_LOCK (dropped).
//      - SoC reads of write-only lock registers (expect 0).
//   3. BOOTFSM_GO is asserted, uC starts this firmware.
//   4. FW verifies all negative writes were dropped and lock readback rules.

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

// Matches num_slots in write_stash_bank() in caliptra_top_tb_soc_bfm.sv
// (passive-mode path). Exercises every slot supported by the RTL.
#define EXPECTED_NUM_SLOTS 8
#define STASH_SLOT_DWORDS  26

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

static void expect_lock_reg_read_zero(const char *name, uint32_t addr) {
    uint32_t got = lsu_read_32(addr);
    if (got != 0u) {
        fail(name, got, 0u);
    }
    VPRINTF(LOW, "FW: %s read as 0 (write-only register)\n", name);
}

void main(void) {
    uint32_t status;
    uint32_t got;
    uint32_t slot_locked_mask;

    VPRINTF(LOW, "--------------------------------------------\n");
    VPRINTF(LOW, " Caliptra Stash Bank NEGATIVE Smoke Test\n");
    VPRINTF(LOW, "--------------------------------------------\n");

    // Step A: confirm BFM finished populating the bank.
    do {
        status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    } while ((status & SOC_IFC_REG_STASH_BANK_STATUS_END_STASH_MASK) == 0);
    VPRINTF(LOW, "FW: STASH_BANK_STATUS = 0x%08x (end_stash observed)\n", status);

    slot_locked_mask = (status & SOC_IFC_REG_STASH_BANK_STATUS_SLOT_LOCKED_MASK)
                       >> SOC_IFC_REG_STASH_BANK_STATUS_SLOT_LOCKED_LOW;
    if (slot_locked_mask != ((1u << EXPECTED_NUM_SLOTS) - 1u)) {
        fail("slot_locked mirror cleared by SOC_LOCK W1S unlock attempt", slot_locked_mask,
             (1u << EXPECTED_NUM_SLOTS) - 1u);
    }
    VPRINTF(LOW, "FW: slot_locked = 0x%02x unchanged after BFM SOC_LOCK unlock attempt\n",
            slot_locked_mask);

    // Step B: positive verification - slot data matches pattern.
    // If any negative write had landed, the pattern check would fail here.
    for (uint32_t s = 0; s < EXPECTED_NUM_SLOTS; s++) {
        for (uint32_t d = 0; d < STASH_SLOT_DWORDS; d++) {
            got = lsu_read_32(slot_addr(s, d));
            uint32_t want = stash_pattern(s, d);
            if (got != want) {
                VPRINTF(ERROR, "ERROR: slot %0d dword %0d - negative write may have landed\n", s, d);
                fail("stash bank data mismatch", got, want);
            }
        }
    }
    VPRINTF(LOW, "FW: all %0d slots match expected pattern (no negative writes landed)\n",
            EXPECTED_NUM_SLOTS);

    // Step C: explicit negative-path assertions - the specific writes
    // attempted by write_stash_bank() steps 3b/3c and write_stash_bank_negative()
    // must NOT change observable state.
    for (uint32_t s = 0; s < EXPECTED_NUM_SLOTS; s++) {
        got = lsu_read_32(slot_addr(s, 0));
        if (got == 0xFEEDFACEu) {
            VPRINTF(ERROR, "ERROR: pre-end_stash SOC_LOCK rewrite landed at slot %0d dword 0\n", s);
            fail("pre-end_stash SOC_LOCK rewrite was NOT dropped", got, stash_pattern(s, 0));
        }
    }
    VPRINTF(LOW, "FW: pre-end_stash SOC_LOCK slot rewrite was dropped (0xFEED_FACE)\n");

    got = lsu_read_32(slot_addr(0, 0));
    if (got == 0xDEADBEEFu) {
        fail("post-end_stash rewrite of slot 0 dword 0 was NOT dropped", got, stash_pattern(0, 0));
    }
    VPRINTF(LOW, "FW: post-end_stash rewrite of slot 0 dword 0 was dropped (slot[0][0]=0x%08x)\n", got);

    got = lsu_read_32(slot_addr(1, 0));
    if (got == 0xBAADF00Du) {
        fail("bad-PAUSER write to slot 1 dword 0 was NOT dropped", got, stash_pattern(1, 0));
    }
    VPRINTF(LOW, "FW: bad-PAUSER write to slot 1 dword 0 was dropped (slot[1][0]=0x%08x)\n", got);

    status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    if ((status & SOC_IFC_REG_STASH_BANK_STATUS_END_STASH_MASK) == 0) {
        fail("STASH_END_STASH write of 0 cleared end_stash mirror", status, 0x100);
    }
    slot_locked_mask = (status & SOC_IFC_REG_STASH_BANK_STATUS_SLOT_LOCKED_MASK)
                       >> SOC_IFC_REG_STASH_BANK_STATUS_SLOT_LOCKED_LOW;
    if (slot_locked_mask != ((1u << EXPECTED_NUM_SLOTS) - 1u)) {
        fail("slot_locked mirror changed after STASH_END_STASH write of 0",
             slot_locked_mask, (1u << EXPECTED_NUM_SLOTS) - 1u);
    }
    VPRINTF(LOW, "FW: STASH_END_STASH write of 0 ignored (STATUS=0x%08x)\n", status);

    // Step D: write-only lock registers must read as 0 on the uC path.
    // Lock state is observable only via STASH_BANK_STATUS (RFC 694 §4.5).
    expect_lock_reg_read_zero("STASH_BANK_SOC_LOCK", CLP_SOC_IFC_REG_STASH_BANK_SOC_LOCK);
    expect_lock_reg_read_zero("STASH_END_STASH", CLP_SOC_IFC_REG_STASH_END_STASH);
    expect_lock_reg_read_zero("STASH_BANK_CPTRA_LOCK", CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK);

    // Step E: uC write of 0 to STASH_BANK_CPTRA_LOCK is W1S - must be ignored.
    if ((status & SOC_IFC_REG_STASH_BANK_STATUS_CPTRA_LOCK_MASK) != 0) {
        fail("cptra_lock mirror should be 0 before uC write", status, 0);
    }
    lsu_write_32(CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK, 0);
    status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    if ((status & SOC_IFC_REG_STASH_BANK_STATUS_CPTRA_LOCK_MASK) != 0) {
        fail("uC write of 0 to CPTRA_LOCK cleared cptra_lock mirror", status, 0);
    }
    expect_lock_reg_read_zero("STASH_BANK_CPTRA_LOCK after uC write of 0",
                              CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK);
    VPRINTF(LOW, "FW: uC write of 0 to STASH_BANK_CPTRA_LOCK ignored (STATUS=0x%08x)\n", status);

    // Step F: assert CPTRA_LOCK from Caliptra (post-drain seal, RFC 694 §4.4 / §7.3).
    lsu_write_32(CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK, 1);
    status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    if ((status & SOC_IFC_REG_STASH_BANK_STATUS_CPTRA_LOCK_MASK) == 0) {
        fail("STASH_BANK_STATUS.cptra_lock mirror should be 1 after FW write", status, 0x200);
    }
    expect_lock_reg_read_zero("STASH_BANK_CPTRA_LOCK after uC write of 1",
                              CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK);
    expect_lock_reg_read_zero("STASH_BANK_SOC_LOCK after CPTRA_LOCK assert",
                              CLP_SOC_IFC_REG_STASH_BANK_SOC_LOCK);
    expect_lock_reg_read_zero("STASH_END_STASH after CPTRA_LOCK assert",
                              CLP_SOC_IFC_REG_STASH_END_STASH);
    VPRINTF(LOW, "FW: STASH_BANK_STATUS = 0x%08x after CPTRA_LOCK assertion\n", status);

    VPRINTF(LOW, "FW: all negative-path checks passed\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
