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
// Stash bank lock stickiness + cptra_rst_b clear smoke test (RFC #694).
//
// Boot ordering:
//   1. First boot: BFM populates stash, locks all 8 slots, asserts end_stash.
//   2. FW verifies uC (AHB, soc_req=0) writes to STASH_BANK_SLOT_DATA,
//      STASH_BANK_SOC_LOCK, and STASH_END_STASH are all silently dropped -
//      these registers are SoC/AXI-only per RFC 694 SS4.4 (soc_ifc_top.sv
//      gates swwe/swwel on soc_req for all three).
//   3. FW sets CPTRA_LOCK and verifies all STATUS lock mirrors are set (0x3FF).
//   4. FW attempts uC write of 0 to CPTRA_LOCK (W1S - must be ignored).
//   5. FW issues warm reset (STDOUT 0xf6) which asserts cptra_rst_b.
//   6. Second boot: BFM skips stash populate (+CALIPTRA_TEST_STASH_BANK_RST).
//   7. FW verifies STASH_BANK_STATUS == 0 (all lock bits cleared by reset).

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"
#include "soc_ifc.h"
#include <stddef.h>
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

// Survives warm reset (cptra_rst_b) in DCCM persistent section.
volatile uint32_t rst_count __attribute__((section(".dccm.persistent"))) = 0;

#define EXPECTED_NUM_SLOTS       8u
#define STASH_SLOT_DWORDS        26u
// slot_locked=0xFF | end_stash=0x100 | cptra_lock=0x200
#define ALL_LOCKS_STATUS         0x3FFu

// Must match write_stash_bank() pattern in caliptra_top_tb_soc_bfm.sv.
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

// uC (AHB, soc_req=0) writes to STASH_BANK_SLOT_DATA, STASH_BANK_SOC_LOCK,
// and STASH_END_STASH must all be silently dropped - these registers are
// SoC/AXI-only (soc_ifc_top.sv gates swwe/swwel on soc_req). Verifies the
// bank's observable state (slot data + STATUS mirrors) is unchanged by the
// attempted uC writes.
static void verify_uc_stash_writes_dropped(void) {
    uint32_t status_before, status_after;
    uint32_t got;

    // 1) Slot data: uC write must not alter existing slot contents.
    got = lsu_read_32(slot_addr(0, 0));
    if (got != stash_pattern(0, 0)) {
        fail("slot[0][0] does not match BFM pattern before uC write attempt",
             got, stash_pattern(0, 0));
    }
    lsu_write_32(slot_addr(0, 0), 0xDEADBEEFu);
    got = lsu_read_32(slot_addr(0, 0));
    if (got != stash_pattern(0, 0)) {
        fail("uC write to STASH_BANK_SLOT_DATA[0][0] was NOT dropped",
             got, stash_pattern(0, 0));
    }
    VPRINTF(LOW, "FW: uC write to STASH_BANK_SLOT_DATA[0][0] dropped (still 0x%08x)\n", got);

    // 2) STASH_BANK_SOC_LOCK: uC write must not affect slot_locked mirror.
    status_before = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    lsu_write_32(CLP_SOC_IFC_REG_STASH_BANK_SOC_LOCK, 0xFFu);
    status_after = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    if (status_after != status_before) {
        fail("uC write to STASH_BANK_SOC_LOCK was NOT dropped",
             status_after, status_before);
    }
    VPRINTF(LOW, "FW: uC write to STASH_BANK_SOC_LOCK dropped (STATUS=0x%08x)\n", status_after);

    // 3) STASH_END_STASH: uC write must not affect end_stash mirror.
    status_before = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    lsu_write_32(CLP_SOC_IFC_REG_STASH_END_STASH, 0x0u);
    status_after = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    if (status_after != status_before) {
        fail("uC write to STASH_END_STASH was NOT dropped",
             status_after, status_before);
    }
    VPRINTF(LOW, "FW: uC write to STASH_END_STASH dropped (STATUS=0x%08x)\n", status_after);

    // All three lock/end registers are write-only (sw=w) - direct reads must
    // return 0 regardless of the attempted (dropped) uC writes above.
    got = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_SOC_LOCK);
    if (got != 0u) {
        fail("STASH_BANK_SOC_LOCK read as nonzero after uC write attempt", got, 0u);
    }
    got = lsu_read_32(CLP_SOC_IFC_REG_STASH_END_STASH);
    if (got != 0u) {
        fail("STASH_END_STASH read as nonzero after uC write attempt", got, 0u);
    }
    VPRINTF(LOW, "FW: STASH_BANK_SOC_LOCK / STASH_END_STASH read as 0 (write-only)\n");
}

static void wait_for_end_stash(uint32_t *status_out) {
    uint32_t status;
    do {
        status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
    } while ((status & SOC_IFC_REG_STASH_BANK_STATUS_END_STASH_MASK) == 0);
    if (status_out != NULL) {
        *status_out = status;
    }
}

void main(void) {
    uint32_t status;
    uint32_t slot_locked_mask;

    rst_count++;

    VPRINTF(LOW, "------------------------------------------\n");
    VPRINTF(LOW, " Caliptra Stash Bank RST Smoke Test\n");
    VPRINTF(LOW, " rst_count = %0d\n", rst_count);
    VPRINTF(LOW, "------------------------------------------\n");

    if (rst_count == 1u) {
        // Phase 1 (pre-reset): all lock bits must be set and sticky.
        wait_for_end_stash(&status);

        slot_locked_mask = (status & SOC_IFC_REG_STASH_BANK_STATUS_SLOT_LOCKED_MASK)
                           >> SOC_IFC_REG_STASH_BANK_STATUS_SLOT_LOCKED_LOW;
        if (slot_locked_mask != ((1u << EXPECTED_NUM_SLOTS) - 1u)) {
            fail("slot_locked mirror mismatch before reset", slot_locked_mask,
                 (1u << EXPECTED_NUM_SLOTS) - 1u);
        }
        VPRINTF(LOW, "FW: STASH_BANK_STATUS = 0x%08x after BFM populate\n", status);

        // uC-side writes to data/SOC_LOCK/END_STASH must be no-ops (soc_req
        // gating in soc_ifc_top.sv), independent of CPTRA_LOCK sealing below.
        verify_uc_stash_writes_dropped();

        lsu_write_32(CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK, 1);
        status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
        if (status != ALL_LOCKS_STATUS) {
            fail("all lock mirrors should be set before reset", status, ALL_LOCKS_STATUS);
        }
        VPRINTF(LOW, "FW: all lock bits set (STATUS=0x%08x)\n", status);

        // W1S stickiness: uC write of 0 must not clear cptra_lock.
        lsu_write_32(CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK, 0);
        status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
        if (status != ALL_LOCKS_STATUS) {
            fail("lock bits not sticky (uC write of 0 cleared state)", status, ALL_LOCKS_STATUS);
        }
        VPRINTF(LOW, "FW: lock bits sticky after uC write of 0 to CPTRA_LOCK\n");

        VPRINTF(LOW, "FW: issuing warm reset (STDOUT 0xf6) to assert cptra_rst_b\n");
        SEND_STDOUT_CTRL(0xf6);
        while (1);
    }

    if (rst_count == 2u) {
        // Phase 2 (post-reset): all lock bits cleared by cptra_rst_b.
        // BFM did not repopulate the bank on this boot.
        status = lsu_read_32(CLP_SOC_IFC_REG_STASH_BANK_STATUS);
        if (status != 0u) {
            fail("all lock mirrors should clear on cptra_rst_b", status, 0u);
        }
        VPRINTF(LOW, "FW: STASH_BANK_STATUS = 0x%08x after cptra_rst_b (all locks cleared)\n", status);

        VPRINTF(LOW, "FW: stash bank lock reset checks passed\n");
        SEND_STDOUT_CTRL(0xff);
        while (1);
    }

    VPRINTF(ERROR, "ERROR: unexpected rst_count %0d\n", rst_count);
    SEND_STDOUT_CTRL(0x1);
    while (1);
}
