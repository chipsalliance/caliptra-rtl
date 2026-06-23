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
//   1. BFM populates slots 0..7 with the standard pattern, locks them,
//      asserts STASH_END_STASH (same as smoke_test_stash_bank positive
//      path - via write_stash_bank() in caliptra_top_tb_soc_bfm.sv).
//   2. BFM then runs write_stash_bank_negative():
//      - Attempts to rewrite slot 0 dword 0 with 0xDEAD_BEEF, expecting
//        the RTL to drop the write because STASH_BANK_SOC_LOCK[0]=1
//        (and end_stash=1).
//      - Attempts to write slot 1 dword 0 with 0xBAAD_F00D using a
//        mismatched AXI USER (0xCAFE_BABE), expecting the RTL to drop
//        the write because the PAUSER filter (stash_axi_user_valid)
//        rejects unrecognized AXI USER values.
//   3. BOOTFSM_GO is asserted, uC starts this firmware.
//   4. FW (this code) reads each negative target back and confirms it
//      still holds the original BFM pattern - proving both writes were
//      dropped.

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

void main(void) {
    uint32_t status;
    uint32_t got;

    VPRINTF(LOW, "--------------------------------------------\n");
    VPRINTF(LOW, " Caliptra Stash Bank NEGATIVE Smoke Test\n");
    VPRINTF(LOW, "--------------------------------------------\n");

    // Step A: confirm BFM finished populating the bank.
    do {
        status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    } while ((status & SOC_IFC_REG_STASH_BANK_STATUS_END_STASH_MASK) == 0);
    VPRINTF(LOW, "FW: STASH_BANK_STATUS = 0x%08x (end_stash observed)\n", status);

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

    // Step C: explicit negative-path assertions - the two specific writes
    // attempted by write_stash_bank_negative() must NOT be observable.
    got = lsu_read_32(slot_addr(0, 0));
    if (got == 0xDEADBEEFu) {
        fail("post-lock rewrite of slot 0 dword 0 was NOT dropped", got, stash_pattern(0, 0));
    }
    VPRINTF(LOW, "FW: post-lock rewrite of slot 0 dword 0 was dropped (slot[0][0]=0x%08x)\n", got);

    got = lsu_read_32(slot_addr(1, 0));
    if (got == 0xBAADF00Du) {
        fail("bad-PAUSER write to slot 1 dword 0 was NOT dropped", got, stash_pattern(1, 0));
    }
    VPRINTF(LOW, "FW: bad-PAUSER write to slot 1 dword 0 was dropped (slot[1][0]=0x%08x)\n", got);

    // Step D: set CPTRA_LOCK for completeness (defense-in-depth post-drain seal,
    // RFC 694 §4.4 / §7.3).
    lsu_write_32(CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK, 1);
    status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    if ((status & SOC_IFC_REG_STASH_BANK_STATUS_CPTRA_LOCK_MASK) == 0) {
        fail("STASH_BANK_STATUS.cptra_lock mirror should be 1 after FW write", status, 0x200);
    }

    VPRINTF(LOW, "FW: all negative-path checks passed\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
