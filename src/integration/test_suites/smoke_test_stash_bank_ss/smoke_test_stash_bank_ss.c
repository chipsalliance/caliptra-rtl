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
// Stash measurement register bank SUBSYSTEM-mode smoke test (RFC #673).
//
// Built with +define+CALIPTRA_MODE_SUBSYSTEM (the Makefile maps that
// into -DCALIPTRA_HWCONFIG_SUBSYSTEM_MODE for C).
//
// Boot ordering:
//   1. BFM populates slot 0 (only) with the standard pattern, locks
//      slot 0, then - because CALIPTRA_MODE_SUBSYSTEM is defined - also
//      attempts to write slot 1 dword 0 (with valid PAUSER) to prove the
//      RTL tie-off of slots 1..7 works. BFM then asserts STASH_END_STASH.
//   2. BOOTFSM_GO is asserted, uC starts this firmware.
//   3. FW verifies:
//      - Slot 0 has the expected pattern.
//      - Slot 1..7 all read back as 0 (the tie-off blocked the BFM's
//        attempted slot 1 write, and the BFM never tried slots 2..7).
//      - STATUS.slot_locked bit 0 is set; bits 1..7 are clear.

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

#define STASH_SLOT_DWORDS 26

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
    uint32_t want;

    VPRINTF(LOW, "--------------------------------------------------\n");
    VPRINTF(LOW, " Caliptra Stash Bank SUBSYSTEM Smoke Test (N=1)\n");
    VPRINTF(LOW, "--------------------------------------------------\n");

#ifndef CALIPTRA_HWCONFIG_SUBSYSTEM_MODE
    // Should be unreachable - this test only makes sense when compiled with
    // +define+CALIPTRA_MODE_SUBSYSTEM (CALIPTRA_HWCONFIG_SUBSYSTEM_MODE in C).
    VPRINTF(ERROR, "ERROR: smoke_test_stash_bank_ss built without CALIPTRA_MODE_SUBSYSTEM\n");
    SEND_STDOUT_CTRL(0x1);
    while (1);
#else

    // Step A: confirm BFM finished populating the bank.
    do {
        status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    } while ((status & SOC_IFC_REG_STASH_BANK_STATUS_END_STASH_MASK) == 0);
    VPRINTF(LOW, "FW: STASH_BANK_STATUS = 0x%08x (end_stash observed)\n", status);

    // Step B: slot_locked mirror should be 0x01 (only slot 0 locked).
    uint32_t slot_locked_mask = (status & SOC_IFC_REG_STASH_BANK_STATUS_SLOT_LOCKED_MASK)
                                >> SOC_IFC_REG_STASH_BANK_STATUS_SLOT_LOCKED_LOW;
    if (slot_locked_mask != 0x01u) {
        fail("subsystem-mode slot_locked mask should be 0x01", slot_locked_mask, 0x01);
    }
    VPRINTF(LOW, "FW: slot_locked = 0x%02x (only slot 0 locked, as expected)\n", slot_locked_mask);

    // Step C: slot 0 has the BFM pattern.
    for (uint32_t d = 0; d < STASH_SLOT_DWORDS; d++) {
        got  = lsu_read_32(slot_addr(0, d));
        want = stash_pattern(0, d);
        if (got != want) {
            VPRINTF(ERROR, "ERROR: slot 0 dword %0d\n", d);
            fail("slot 0 data mismatch", got, want);
        }
    }
    VPRINTF(LOW, "FW: slot 0 - all 26 dwords match BFM pattern\n");

    // Step D: slots 1..7 are all zero. In subsystem mode the BFM explicitly
    // attempts a slot 1 dword 0 write with valid PAUSER; the RTL tie-off
    // must drop it. We read every dword of every disabled slot to confirm
    // none of them accidentally got a value.
    for (uint32_t s = 1; s < 8; s++) {
        for (uint32_t d = 0; d < STASH_SLOT_DWORDS; d++) {
            got = lsu_read_32(slot_addr(s, d));
            if (got != 0u) {
                VPRINTF(ERROR, "ERROR: subsystem tie-off failed at slot %0d dword %0d\n", s, d);
                fail("disabled slot has nonzero value", got, 0);
            }
        }
    }
    VPRINTF(LOW, "FW: slots 1..7 all read as 0 (subsystem tie-off verified)\n");

    // Step E: explicit check on the slot the BFM tried to write.
    got = lsu_read_32(slot_addr(1, 0));
    if (got == 0xCAFEF00Du) {
        fail("subsystem tie-off failed - BFM write to slot 1 dword 0 landed", got, 0);
    }
    VPRINTF(LOW, "FW: BFM's slot 1 dword 0 write attempt was dropped (got 0x%08x)\n", got);

    // Step F: set CPTRA_LOCK (per RFC 694 §4.4 / §7.3).
    lsu_write_32(CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK, 1);
    status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    if ((status & SOC_IFC_REG_STASH_BANK_STATUS_CPTRA_LOCK_MASK) == 0) {
        fail("STASH_BANK_STATUS.cptra_lock mirror should be 1", status, 0x200);
    }

    VPRINTF(LOW, "FW: subsystem-mode stash bank checks passed\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
#endif
}
