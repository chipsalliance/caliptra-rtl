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
// Description:
//   Directed regression test for the Key Vault firmware-update-reset lock
//   bypass fix (see kv_fw_update_reset_lock_bypass_plan.md).
//
//   Threat model being validated
//   ----------------------------
//   A firmware-update / core-only reset masks the effective KV write locks
//   open (lock_wr/lock_use are masked to 0 during fw_update_rst_window in
//   kv.sv, fail-open for RDC cleanliness), while a noncore producer (HMAC or
//   DOE -- both run on cptra_noncore_rst_b and therefore SURVIVE a core-only
//   reset) may have a multiword KV write in flight. Before the fix, a producer
//   write beat that landed while the locks were masked open could partially or
//   fully overwrite a write-locked slot.
//
//   The fix has two independent layers plus a read-side abort layer, exercised
//   by the four cases below:
//     - kv.sv (central, protects ALL producers): during fw_update_rst_window,
//       the data-write enables (key_entry_we) AND the dest_valid/last_dword
//       commit enables (key_entry_ctrl_we) are gated with & ~fw_update_rst_window,
//       and kv_wr_resp.error is asserted (| fw_update_rst_window). So NO producer
//       write can modify any slot during the window, regardless of lock state.
//     - kv_fsm.sv (per shared-FSM client): abort_i (= kv_resp.error) forces the
//       shared write/read FSM to KV_DONE; write_last never asserts on abort, so
//       dest_valid never commits. Wired into kv_write_client / kv_read_client,
//       so HMAC/ECC/MLKEM abort on a rejected beat. DOE does NOT use kv_fsm and
//       cannot self-abort -- it relies solely on the central kv.sv gating.
//
//   Single binary, multi-boot phase state machine
//   ---------------------------------------------
//   main() is re-entered after each firmware-update / core-only reset. The
//   current case is tracked by a persistent DCCM counter (phase) that survives a
//   core-only reset (DCCM is not cleared and crt0 does not re-init the
//   .dccm.persistent section). Each boot verifies the PREVIOUS case, advances
//   the phase, and sets up the NEXT case; a TB-only alignment hook then drives a
//   fw-update reset so it lands while the producer's KV write is in flight, and
//   main() is re-entered to verify. SEND_STDOUT_CTRL(0xff) is emitted only after
//   the final case (Case C) verifies.
//
//     Boot 0 (cold,       phase 0): setup Case A.
//     Boot 1 (fw-update,  phase 0): verify Case A -> phase 1 -> setup Case B.
//     Boot 2 (fw-update,  phase 1): verify Case B -> phase 2 -> setup Case C.
//     Boot 3 (fw-update,  phase 2): verify Case C -> phase 3 -> setup Case D.
//     Boot 4 (fw-update,  phase 3): verify Case D -> PASS.
//
//   Case A -- HMAC producer, LOCKED slot (shared-FSM abort path)
//   ------------------------------------------------------------
//     Populate spare slot KV_SLOT_TMP(3) via HMAC (dest_valid = HMAC_KEY), set
//     lock_wr, arm TB hook 0xbd flavor 0 (waits for kv_write[HMAC].write_en then forces
//     fw_update_rst), and kick a NON-BLOCKING HMAC->KV write to the same locked
//     slot with a DIFFERENT dest_valid (AES_KEY). Because the slot is already
//     lock_wr-locked, the very first beat is rejected on the REAL effective lock
//     (not the window); with the fix the kv_fsm aborts immediately (abort_i ->
//     KV_DONE), write_last never asserts, dest_valid never flips. Post-reset:
//     dest_valid unchanged == HMAC_KEY (no AES_KEY), no spurious kv_error.
//
//   Case B -- HMAC producer, UNLOCKED slot, WINDOW-ALIGNED (kv.sv write-block)
//   -------------------------------------------------------------------------
//     This case isolates the kv.sv & ~fw_update_rst_window write-block, which
//     Case A does NOT reach (Case A rejects on the real lock before the window).
//     Populate spare slot 11 via HMAC (dest_valid = HMAC_KEY) but do NOT lock
//     it, so the ONLY thing that can block the attacker write is the window
//     gate. Arm TB hook 0xbd flavor 1, which waits for the HMAC core's digest_valid_new
//     (asserted in CTRL_DONE, exactly one cycle BEFORE the HMAC->KV write burst
//     begins) and then forces fw_update_rst. Triggering off digest_valid_new
//     raises the window BEFORE the first write beat (leading-edge coverage); a
//     long wait_cycles keeps the window asserted past the last beat
//     (trailing-edge coverage). Kick a NON-BLOCKING HMAC->KV write to slot 11
//     with a DIFFERENT dest_valid (AES_KEY). Every beat lands during the window,
//     so in kv.sv key_entry_we (data) AND key_entry_ctrl_we (dest_valid /
//     last_dword) are all gated off -> nothing commits and the pre-existing
//     contents persist. Post-reset: dest_valid unchanged == HMAC_KEY, and
//     crucially NOT flipped to AES_KEY; no spurious kv_error.
//
//   Case C -- DOE producer, UNLOCKED slot (fw_update_rst_window gate + DOE abort)
//   ----------------------------------------------------------------------------
//     With this PR's DOE hardening, doe_fsm.sv now consumes kv_wr_resp.error and
//     aborts its KV write, and presents dest_valid only on the final beat. Populate
//     spare slot 12 via HMAC (dest_valid = HMAC_KEY) and leave it UNLOCKED so the
//     DOE write is NOT lock-rejected; arm TB hook 0xbd flavor 2 (waits for
//     kv_write[DOE].write_en then forces fw_update_rst), and start a DOE
//     deobfuscation flow whose UDS destination is slot 12. The reset lands while
//     the DOE write is in flight: the window error-responds the remaining beats,
//     the DOE FSM aborts, and the write never COMPLETES (its dest_valid = 0x3 =
//     hmac_key|hmac_block is committed only on the final, blocked beat). This
//     isolates the window gate from the normal lock_wr path. Post-reset: the DOE's
//     hmac_block bit must NOT be set (a completed overwrite). A pre-window beat may
//     legitimately leave the slot invalid (dest_valid = 0), which is a safe outcome,
//     so HMAC_KEY is not required to persist; no spurious kv_error.
//
//   Case D -- HMAC consumer, READ-side abort (window read-block + hwclr)
//   -------------------------------------------------------------------
//     The three cases above all cover the WRITE side. Case D covers the READ
//     side of the fix. During fw_update_rst_window, kv.sv also blocks READ data
//     (returns 0) and asserts kv_rd_resp.error. The shared-FSM read client
//     (kv_read_client, abort_i = kv_resp.error) aborts the in-flight read and
//     latches error_code = KV_READ_FAIL; the HMAC consumer then clears its key
//     register (HMAC512_KEY[dword].KEY.hwclr on kv_key_error != KV_SUCCESS,
//     hmac.sv). So a fw-update reset timed into an in-flight KV KEY read must
//     leave the consumer with NO partial key. Populate a fresh spare slot
//     TEST_SLOT_D(13) via HMAC (dest_valid = HMAC_KEY) and leave it UNLOCKED so
//     the read STARTS successfully -- the window (not a lock) is what forces the
//     error (straddle scenario). Arm TB hook 0xbd flavor 3, which waits for the
//     read client's kv_key_write_en (asserted per dword as KV data is written
//     into HMAC512_KEY, i.e. an in-flight KEY read) and then forces
//     fw_update_rst so the window straddles the remaining read beats. Kick a
//     NON-BLOCKING HMAC KEY read from slot 13. The read client's error_code
//     register lives on cptra_noncore_rst_b and thus SURVIVES the core-only
//     reset; once KV_READ_FAIL latches it self-holds. Post-reset: read
//     HMAC512_KV_RD_KEY_STATUS -- the ERROR field must be NON-ZERO (the windowed
//     read aborted with KV_READ_FAIL, which drove KEY.hwclr so no partial key
//     remains). A clean VALID with ERROR==0 would mean the read completed
//     normally and (partially) loaded a key -> FAIL. No spurious kv_error.
//
//   NOTE: This test is expected to PASS only with the RTL fix present. Reverting
//   the kv.sv / kv_fsm.sv / kv_*client.sv changes lets one or more of the
//   in-flight producer writes land on the write-locked / window-protected slot,
//   flipping dest_valid and failing the corresponding verify step; reverting the
//   read-side gating lets Case D complete the read cleanly (ERROR==0), failing.

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "riscv_hw_if.h"
#include "kv_boot_flow.h"
#include "doe.h"

volatile uint32_t* stdout = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Persistent phase counter. Placed in .dccm.persistent so it SURVIVES the
// firmware-update / core-only reset (DCCM is not cleared and crt0 does not
// re-initialize this section). The init value 0 only applies on cold boot.
// Same pattern as smoke_test_kv_boot_flow_monitor's boot_count.
volatile uint32_t phase __attribute__((section(".dccm.persistent"))) = 0;

// Spare slots used for the experiments (avoid ROM/DICE persistent slots and
// slot 23 which can hang the DOE FSM).
#define TEST_SLOT_A            KV_SLOT_TMP        // 3  (Case A, HMAC, locked)
#define TEST_SLOT_B            11                 //    (Case B, HMAC, unlocked)
#define TEST_SLOT_C            12                 //    (Case C, DOE,  unlocked)
#define DOE_FE_SLOT            13                 //    (Case C, DOE FE spare dest)
#define DOE_HEK_SLOT           14                 //    (Case C, DOE HEK spare dest)
// Case D repopulates slot 13 fresh (the stale Case C DOE FE spare) as a
// readable HMAC key; the earlier DOE FE write to it is unlocked and unchecked.
#define TEST_SLOT_D            13                 //    (Case D, HMAC KEY read, unlocked)

// TB-only deterministic alignment hooks (see caliptra_top_tb_services.sv). Once
// armed, each hook waits for its producer's in-flight KV write beat and then
// drives a firmware-update / core-only reset so it lands during the burst.
// Single command 0xbd; the flavor byte selects the trigger event.
#define TB_CMD_KV_FWRST          0xbd
#define KV_FWRST_FLAVOR_HMAC     0    // Case A: waits for kv_write[HMAC].write_en
#define KV_FWRST_FLAVOR_WINDOW   1    // Case B: waits for hmac core digest_valid_new
#define KV_FWRST_FLAVOR_DOE      2    // Case C: waits for kv_write[DOE].write_en
#define KV_FWRST_FLAVOR_KEYREAD  3    // Case D: waits for hmac kv_key_write_en (in-flight KEY read)
#define ARM_KV_FWRST(flavor)     lsu_write_32(STDOUT, (((flavor) & 0xff) << 8) | TB_CMD_KV_FWRST)

// fw-update-reset window length (INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES). Case A
// only needs the reset to land during the burst (the real lock_wr protects the
// rest), and Case C's DOE FSM self-aborts on the first window-gated error beat,
// so 5 is sufficient for both. Case B is unlocked and relies purely on the window
// spanning the ENTIRE ~12-beat HMAC->KV burst; use a long value.
#define FWRST_WAIT_CYCLES_SHORT  5
#define FWRST_WAIT_CYCLES_LONG   40

// dest_valid bit positions inside the KV KEY_CTRL.dest_valid[9] field
// (ordering from kv_reg.rdl).
#define KV_DV_HMAC_KEY_BIT     0
#define KV_DV_HMAC_BLOCK_BIT   1   // DOE sets this on an overwrite (dest_valid=0x3)
#define KV_DV_AES_KEY_BIT      5

// dest_valid masks (DV_HMAC_KEY / DV_AES_KEY) come from kv_boot_flow.h.

// DOE deobfuscation IVs (same vectors used by smoke_test_kv_crypto_flow).
static const uint32_t iv_data_uds[] = {0x2eb94297,0x77285196,0x3dd39a1e,0xb95d438f};
static const uint32_t iv_data_fe[]  = {0x14451624,0x6a752c32,0x9056d884,0xdaf3c89d};
static const uint32_t iv_data_hek[] = {0x3e8b1c72,0xa459d6f0,0x5c27b9ae,0xf02d4389};

//
// Read the dest_valid field (9 bits) out of a slot's KEY_CTRL register.
//
static uint32_t kv_read_dest_valid(uint8_t slot) {
    uint32_t key_ctrl = lsu_read_32(KV_KEY_CTRL(slot));
    return (key_ctrl & KV_REG_KEY_CTRL_0_DEST_VALID_MASK) >>
           KV_REG_KEY_CTRL_0_DEST_VALID_LOW;
}

//
// Non-blocking variant of hmac_write_kv_slot(): programs KEY/BLOCK/LFSR and the
// HMAC KV_WR_CTRL destination, kicks HMAC INIT, and RETURNS IMMEDIATELY (does
// NOT poll STATUS.VALID). This lets the fw-update reset be aligned to the
// resulting in-flight HMAC->KV write burst.
//
static void hmac_start_kv_write_nonblocking(uint8_t slot, uint32_t dest_valid_mask) {
    uint32_t *reg;

    // Wait for HMAC ready (previous op drained)
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) &
            HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    // Distinct "attacker" key material (differs from the legit populate) so a
    // successful overwrite would be observable.
    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_KEY_0;
    for (int i = 0;
         i <= (CLP_HMAC_REG_HMAC512_KEY_11 - CLP_HMAC_REG_HMAC512_KEY_0) / 4;
         i++) {
        lsu_write_32((uintptr_t)(reg + i), 0xBADC0DE0 + i);
    }
    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_BLOCK_0;
    for (int i = 0;
         i <= (CLP_HMAC_REG_HMAC512_BLOCK_31 - CLP_HMAC_REG_HMAC512_BLOCK_0) / 4;
         i++) {
        lsu_write_32((uintptr_t)(reg + i), 0x5A5A0000 + i);
    }
    reg = (uint32_t *)CLP_HMAC_REG_HMAC512_LFSR_SEED_0;
    for (int i = 0;
         i <= (CLP_HMAC_REG_HMAC512_LFSR_SEED_5 - CLP_HMAC_REG_HMAC512_LFSR_SEED_0) / 4;
         i++) {
        lsu_write_32((uintptr_t)(reg + i), 0x1234000 + i);
    }

    // Target the slot with the requested dest_valid.
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL,
        HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
        ((slot << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
         HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK) |
        dest_valid_mask);

    // Kick off HMAC384 INIT and return without polling.
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL,
        HMAC_REG_HMAC512_CTRL_INIT_MASK |
        (HMAC384_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));
}

//
// Non-blocking HMAC KEY read from a KV slot: waits for the read client to be
// READY, kicks a KEY read (READ_EN + READ_ENTRY) and RETURNS IMMEDIATELY (does
// NOT poll STATUS.VALID / STATUS.ERROR). This lets the fw-update reset be
// aligned to the resulting in-flight KV->HMAC KEY read burst (kv_key_write_en).
//
static void hmac_start_kv_keyread_nonblocking(uint8_t slot) {
    // Kick the KEY read from the slot and return without polling. The read
    // client asserts kv_key_write_en per dword as it streams KV data into
    // HMAC512_KEY -- the TB (flavor 3) forces fw_update_rst on that signal.
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL,
        HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
        ((slot << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) &
         HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));
}

//
// Spin waiting for the TB-driven fw-update reset to re-enter main(). If it never
// arrives, the alignment hook failed -- fail the test.
//
static void spin_for_fwrst(const char *tag) {
    for (volatile uint32_t i = 0; i < 2000000u; i++) {
        __asm__ volatile ("nop");
    }
    VPRINTF(ERROR, "[FAIL] fw-update reset never landed during case %s KV write\n", tag);
    SEND_STDOUT_CTRL(0x01);
    while (1);
}

// ============================================================
// Write-side cases (A/B/C): a producer's in-flight KV write must NOT modify
// the target slot across a fw-update reset. Verified by dest_valid: the legit
// populate sets HMAC_KEY; a successful overwrite would set `other_bit`
// (AES_KEY for the HMAC producer, HMAC_BLOCK for DOE's dest_valid=0x3).
// ============================================================
static void verify_no_overwrite(uint8_t slot, uint32_t other_bit, const char *tag) {
    uint32_t dv = kv_read_dest_valid(slot);
    if (((dv >> other_bit) & 0x1) || !((dv >> KV_DV_HMAC_KEY_BIT) & 0x1)) {
        VPRINTF(ERROR, "[FAIL] %s: slot %d overwritten across fw-update reset "
                       "(dest_valid=0x%x, expected HMAC_KEY only)\n", tag, slot, dv);
        SEND_STDOUT_CTRL(0x01);
        while (1);
    }
    check_no_kv_error(tag);
    VPRINTF(LOW, "%s passed: slot %d preserved (dest_valid=0x%x)\n", tag, slot, dv);
}

// Case C verification (DOE producer, window gate). The DOE UDS write presents its
// dest_valid (HMAC_BLOCK bit, forming 0x3) only on the final beat, which the
// fw_update_rst_window blocks -- so a COMPLETED DOE overwrite is detectable by the
// HMAC_BLOCK bit being set, and that must never happen. Unlike the HMAC cases, an
// unlocked slot may be legitimately left invalid (dest_valid=0) by a pre-window
// beat; that is a safe outcome (no valid overwritten key), so we do NOT require
// HMAC_KEY to persist -- only that the DOE write never completed.
static void verify_case_c(uint8_t slot, const char *tag) {
    uint32_t dv = kv_read_dest_valid(slot);
    if ((dv >> KV_DV_HMAC_BLOCK_BIT) & 0x1) {
        VPRINTF(ERROR, "[FAIL] %s: DOE overwrite COMPLETED across fw-update reset "
                       "(dest_valid=0x%x, HMAC_BLOCK set)\n", tag, slot, dv);
        SEND_STDOUT_CTRL(0x01);
        while (1);
    }
    check_no_kv_error(tag);
    VPRINTF(LOW, "%s passed: DOE overwrite did not complete (dest_valid=0x%x)\n", tag, slot, dv);
}

// Case A (locked, short window, HMAC write_en hook) and Case B (unlocked,
// long window, digest_valid_new hook) share this setup. Populate the slot via
// HMAC, optionally lock it, program the window, arm the TB hook, then kick a
// NON-BLOCKING HMAC->KV write with a DIFFERENT dest_valid (AES_KEY) so any
// overwrite is observable. The TB forces fw_update_rst mid-burst.
static void setup_hmac_write_case(uint8_t slot, int do_lock, uint32_t flavor,
                                  uint32_t wait_cycles, const char *tag) {
    VPRINTF(LOW, "%s setup: HMAC write to slot %d (lock=%d)\n", tag, slot, do_lock);
    hmac_write_kv_slot(slot, DV_HMAC_KEY);
    if (do_lock) {
        lsu_write_32(KV_KEY_CTRL(slot), KV_LOCK_WR_MASK);
    }
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES, wait_cycles);
    ARM_KV_FWRST(flavor);
    hmac_start_kv_write_nonblocking(slot, DV_AES_KEY);
    spin_for_fwrst(tag);
}

// Case C -- DOE producer, UNLOCKED slot: exercises the fw_update_rst_window gate,
// NOT a lock. With this PR's DOE hardening, doe_fsm consumes kv_wr_resp.error and
// aborts, and dest_valid is presented only on the final DOE beat (mirroring
// kv_write_client). Populate slot 12 and leave it UNLOCKED so the DOE write is not
// lock-rejected on beat 0; arm the DOE write_en hook so the reset lands while the
// DOE UDS write is in flight. The window then error-responds the remaining beats,
// the DOE FSM aborts, and the write never completes (its dest_valid=0x3 is never
// committed). Verified by verify_case_c().
static void setup_case_c(void) {
    VPRINTF(LOW, "C setup: DOE write to unlocked slot %d (window gate)\n", TEST_SLOT_C);
    hmac_write_kv_slot(TEST_SLOT_C, DV_HMAC_KEY);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES,
                 FWRST_WAIT_CYCLES_SHORT);
    ARM_KV_FWRST(KV_FWRST_FLAVOR_DOE);
    doe_init((uint32_t *)iv_data_uds, (uint32_t *)iv_data_fe, (uint32_t *)iv_data_hek,
             TEST_SLOT_C, DOE_FE_SLOT, DOE_HEK_SLOT);
    spin_for_fwrst("C");
}

// ============================================================
// Case D -- HMAC consumer, READ-side abort (window read-block + hwclr)
// ============================================================
static void setup_case_d(void) {
    // Populate a fresh readable HMAC key, left UNLOCKED so the read STARTS
    // successfully -- the window (not a lock) forces the error (straddle). Long
    // window so it straddles the remaining KV->HMAC KEY read beats after the
    // trigger fires on the first kv_key_write_en. Kick a NON-BLOCKING KEY read;
    // the TB forces fw_update_rst mid-read so it aborts with KV_READ_FAIL.
    VPRINTF(LOW, "D setup: HMAC KEY read from slot %d\n", TEST_SLOT_D);
    hmac_write_kv_slot(TEST_SLOT_D, DV_HMAC_KEY);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES,
                 FWRST_WAIT_CYCLES_LONG);
    ARM_KV_FWRST(KV_FWRST_FLAVOR_KEYREAD);
    hmac_start_kv_keyread_nonblocking(TEST_SLOT_D);
    spin_for_fwrst("D");
}

static void verify_case_d(void) {
    // The HMAC KEY register is NOT SW-readable, so verify via the read status.
    // The read client's error_code lives on cptra_noncore_rst_b, so KV_READ_FAIL
    // survives the core-only reset. ERROR field NON-ZERO proves the windowed
    // read aborted and drove KEY.hwclr -> no partial key. A clean completion
    // (ERROR==0) would mean a (partial) key loaded -> security FAIL.
    uint32_t rd_status = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS);
    uint32_t rd_error  = (rd_status & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_MASK) >>
                         HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_LOW;
    if (rd_error == 0) {
        VPRINTF(ERROR, "[FAIL] D: KEY read did not abort during window "
                       "(KV_RD_KEY_STATUS=0x%08x, expected non-zero ERROR)\n", rd_status);
        SEND_STDOUT_CTRL(0x01);
        while (1);
    }
    check_no_kv_error("D");
    VPRINTF(LOW, "D passed: KEY read aborted, no partial key (err=0x%x)\n", rd_error);
}

void main() {
    init_interrupts();

    uint32_t reset_reason = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_RESET_REASON);
    uint32_t is_fw_update = reset_reason & SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK;

    if (!is_fw_update) {
        // Cold boot: must be the very first phase.
        if (phase != 0) {
            VPRINTF(ERROR, "[FAIL] cold boot with unexpected phase=%u\n", phase);
            SEND_STDOUT_CTRL(0x01);
            while (1);
        }
        VPRINTF(LOW, "KV fw-update-reset abort test (4 cases)\n");
        // Case A: locked slot, short window, HMAC write_en hook.
        setup_hmac_write_case(TEST_SLOT_A, 1, KV_FWRST_FLAVOR_HMAC,
                              FWRST_WAIT_CYCLES_SHORT, "A");
    } else {
        // fw-update reset re-entry: verify the case just exercised, advance the
        // phase, and set up the next case. Only the final case signals PASS.
        if (phase == 0) {
            verify_no_overwrite(TEST_SLOT_A, KV_DV_AES_KEY_BIT, "A");
            phase = 1;
            // Case B: unlocked slot, long window, digest_valid_new hook.
            setup_hmac_write_case(TEST_SLOT_B, 0, KV_FWRST_FLAVOR_WINDOW,
                                  FWRST_WAIT_CYCLES_LONG, "B");
        } else if (phase == 1) {
            verify_no_overwrite(TEST_SLOT_B, KV_DV_AES_KEY_BIT, "B");
            phase = 2;
            setup_case_c();
        } else if (phase == 2) {
            verify_case_c(TEST_SLOT_C, "C");
            phase = 3;
            setup_case_d();
        } else if (phase == 3) {
            verify_case_d();
            VPRINTF(LOW, "All 4 cases passed: KV protected across fw-update reset\n");
            SEND_STDOUT_CTRL(0xff);
            while (1);
        } else {
            VPRINTF(ERROR, "[FAIL] fw-update reset with unexpected phase=%u\n", phase);
            SEND_STDOUT_CTRL(0x01);
            while (1);
        }
    }

    // setup_* never returns (they spin for the TB-driven reset). Reaching here
    // means the state machine fell through unexpectedly.
    VPRINTF(ERROR, "[FAIL] unexpected fallthrough in phase state machine (phase=%u)\n", phase);
    SEND_STDOUT_CTRL(0x01);
    while (1);
}
