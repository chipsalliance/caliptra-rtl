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
// Stash measurement register bank smoke test (RFC #673).
//
// Companion to caliptra_top_tb_soc_bfm.sv::write_stash_bank() which runs
// when +CALIPTRA_TEST_STASH_BANK is passed at simv invocation (auto-set
// by the Makefile when TESTNAME matches smoke_test_stash_bank*).
//
// Boot ordering (positive path):
//   1. BFM writes fuses + FUSE_WR_DONE.
//   2. BFM locks CPTRA_MBOX_AXI_USER_LOCK[0] so PAUSER 0xFFFF_FFFF is accepted.
//   3. BFM populates N slots with pattern (slot<<24 | dword<<8 | 0xA5),
//      locks each slot via STASH_BANK_SOC_LOCK, then asserts STASH_END_STASH.
//   4. BFM writes BOOTFSM_GO, uC starts running this firmware.
//   5. FW (this code) reads STASH_BANK_STATUS, compares slot data against
//      the expected pattern, sets STASH_BANK_CPTRA_LOCK, and exits PASSED.
//      (In a real Caliptra boot per RFC 673 §7.3, the CPTRA_LOCK assert is
//      done by Caliptra Runtime FW after the post-DPE-init drain. This smoke
//      test simulates that sealing step.)
//   6. FW requests the BFM (STDOUT 0xc1) to overwrite every slot with random
//      data using an invalid stash PAUSER, then re-verifies the bank still
//      holds the original BFM pattern (proving the writes were dropped).
//
// In CALIPTRA_MODE_SUBSYSTEM builds, the BFM populates only slot 0; the
// rest of slots 1..7 must read back as zero because soc_ifc_top.sv ties
// their swwel high so the BFM writes (if any) are dropped.

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

#ifdef CALIPTRA_HWCONFIG_SUBSYSTEM_MODE
    #define EXPECTED_NUM_SLOTS 1
#else
    // Passive mode exercises every slot supported by the RTL (8 total).
    // Must match num_slots in write_stash_bank() in caliptra_top_tb_soc_bfm.sv.
    #define EXPECTED_NUM_SLOTS 8
#endif

#define STASH_SLOT_DWORDS  26

// STDOUT opcode decoded in caliptra_top_tb_services.sv; triggers
// write_stash_bank_bad_pauser() in caliptra_top_tb_soc_bfm.sv.
// NOTE: was 0xbc; moved to 0xc1 to avoid collision with
// TB_CMD_MUBI4_GLITCH (directed_kv_glitch_inject.c) which now owns 0xbc.
#define STASH_BAD_PAUSER_STDOUT_CTRL  0xc1u

// Completion sentinel driven onto GENERIC_INPUT_WIRES[0] by the BFM when the
// invalid-PAUSER overwrite attempt finishes (caliptra_top_tb_pkg.sv).
#define STASH_BAD_PAUSER_DONE         0x600d573au

// BFM-side pattern (must match write_stash_bank() in caliptra_top_tb_soc_bfm.sv).
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

static void verify_stash_pattern(const char *context) {
    for (uint32_t s = 0; s < EXPECTED_NUM_SLOTS; s++) {
        for (uint32_t d = 0; d < STASH_SLOT_DWORDS; d++) {
            uint32_t got  = lsu_read_32(slot_addr(s, d));
            uint32_t want = stash_pattern(s, d);
            if (got != want) {
                VPRINTF(ERROR, "ERROR: %s slot %0d dword %0d\n", context, s, d);
                fail("stash bank data mismatch", got, want);
            }
        }
        VPRINTF(LOW, "FW: slot %0d - all 26 dwords match BFM pattern (%s)\n", s, context);
    }
}

void main(void) {
    uint32_t status;
    uint32_t slot_locked_mask;
    uint32_t expected_slot_locked_mask;

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Caliptra Stash Bank Smoke Test (RFC #673)\n");
    VPRINTF(LOW, "----------------------------------\n");

    // Step A: confirm the BFM has finished populating the bank.
    // end_stash should already be asserted by the time the uC executes.
    VPRINTF(LOW, "FW: polling STASH_BANK_STATUS.end_stash\n");
    do {
        status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    } while ((status & SOC_IFC_REG_STASH_BANK_STATUS_END_STASH_MASK) == 0);
    VPRINTF(LOW, "FW: STASH_BANK_STATUS = 0x%08x (end_stash observed)\n", status);

    // Step B: verify slot_locked mirror matches what we expect for this build.
    slot_locked_mask = (status & SOC_IFC_REG_STASH_BANK_STATUS_SLOT_LOCKED_MASK)
                       >> SOC_IFC_REG_STASH_BANK_STATUS_SLOT_LOCKED_LOW;
    expected_slot_locked_mask = (1u << EXPECTED_NUM_SLOTS) - 1u;
    if (slot_locked_mask != expected_slot_locked_mask) {
        fail("slot_locked mirror mismatch", slot_locked_mask, expected_slot_locked_mask);
    }
    VPRINTF(LOW, "FW: slot_locked = 0x%02x matches expected (num_slots=%0d)\n",
            slot_locked_mask, EXPECTED_NUM_SLOTS);

    // Step C: read each locked slot's 26 dwords, verify against the BFM pattern.
    verify_stash_pattern("initial BFM populate");

    // Step D: request the SoC BFM to overwrite the bank with random data using
    // an invalid stash PAUSER (0xCAFE_BABE). Stash slot data is SoC/AXI-only
    // and PAUSER-gated; the uC cannot originate these writes. The BFM must
    // drive them. All such writes must be silently dropped; re-read below
    // confirms the original BFM pattern is unchanged.
    VPRINTF(LOW, "FW: requesting BFM invalid-PAUSER stash bank overwrite (STDOUT 0x%02x)\n",
            STASH_BAD_PAUSER_STDOUT_CTRL);
    SEND_STDOUT_CTRL(STASH_BAD_PAUSER_STDOUT_CTRL);
    do {
    } while (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) != STASH_BAD_PAUSER_DONE);
    VPRINTF(LOW, "FW: BFM invalid-PAUSER overwrite attempt completed\n");
    verify_stash_pattern("after invalid-PAUSER overwrite attempt");

    // Step E: SOC_LOCK / END_STASH / CPTRA_LOCK are write-only (sw=w in RDL).
    // Lock state is observable only via STASH_BANK_STATUS; direct reads of
    // those addresses must return 0 even when STATUS mirrors show locks set.
    expect_lock_reg_read_zero("STASH_BANK_SOC_LOCK", CLP_SOC_IFC_REG_STASH_BANK_SOC_LOCK);
    expect_lock_reg_read_zero("STASH_END_STASH", CLP_SOC_IFC_REG_STASH_END_STASH);
    expect_lock_reg_read_zero("STASH_BANK_CPTRA_LOCK", CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK);

    // Step F: Caliptra writes STASH_BANK_CPTRA_LOCK = 1 (post-drain seal,
    // RFC 694 §4.4 / §7.3). The write goes through the uC AHB path
    // (soc_req=0); the glue gates CPTRA_LOCK.swwe on ~soc_req so the
    // write is accepted only from Caliptra.
    VPRINTF(LOW, "FW: writing STASH_BANK_CPTRA_LOCK = 1\n");
    lsu_write_32(CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK, 1);

    // Step G: re-read STATUS - cptra_lock mirror bit must now be 1.
    status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    if ((status & SOC_IFC_REG_STASH_BANK_STATUS_CPTRA_LOCK_MASK) == 0) {
        fail("STASH_BANK_STATUS.cptra_lock mirror should be 1", status, 0x200);
    }
    VPRINTF(LOW, "FW: STASH_BANK_STATUS = 0x%08x after CPTRA_LOCK assertion\n", status);

    expect_lock_reg_read_zero("STASH_BANK_SOC_LOCK after CPTRA_LOCK assert",
                              CLP_SOC_IFC_REG_STASH_BANK_SOC_LOCK);
    expect_lock_reg_read_zero("STASH_END_STASH after CPTRA_LOCK assert",
                              CLP_SOC_IFC_REG_STASH_END_STASH);
    expect_lock_reg_read_zero("STASH_BANK_CPTRA_LOCK after CPTRA_LOCK assert",
                              CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK);

    VPRINTF(LOW, "FW: all stash bank checks passed\n");

    // End the simulation with success.
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
