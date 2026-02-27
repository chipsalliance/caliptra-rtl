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
// =============================================================================
// smoke_test_kv_lock_use_mid_read.c
//
// PURPOSE:
//   Validates the kv_read_client.sv error_code fix for mid-read lock_use
//   injection. Before the fix, error detection was gated by validated_read_en
//   (a one-cycle pulse on beat 0). If lock_use was set DURING the multi-beat
//   KV read (after beat 0), kv_resp.error on beats 1-15 was ignored and
//   error_code remained KV_SUCCESS — allowing a crypto engine to consume a
//   partially-zeroed key without detecting the fault.
//
//   The fix gates error detection by read_allow (held high for all beats),
//   so kv_resp.error on any beat is captured.
//
// TEST STRATEGY:
//   1. Inject a valid key into a KV slot via TB (0xa9 command)
//   2. Pre-compute the lock_use write value (minimize instructions between
//      the KV read trigger and the lock_use write)
//   3. Trigger HMAC KV key read from the slot
//   4. Immediately write lock_use to the same slot — the RISC-V instruction
//      pipeline delay ensures this lands mid-read (after beat 0 but before
//      the 16-beat read completes)
//   5. Wait for the read to complete, verify KV_RD_KEY_STATUS reports error
//   6. Verify lock_use is sticky (cannot be cleared by SW)
// =============================================================================

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {
    uint32_t status;
    uint32_t error_field;
    uint8_t test_slot = 2;

    VPRINTF(LOW, "============================================================\n");
    VPRINTF(LOW, " KV lock_use Mid-Read Fault Capture Test\n");
    VPRINTF(LOW, "============================================================\n");

    // ------------------------------------------------------------------
    // Step 1: Inject a valid HMAC512 key into KV slot via TB
    //
    // TB command 0xa9 injects hmac512_key_tb data into the slot with:
    //   dest_valid = 8'b1  (bit 0 = HMAC_KEY read client allowed)
    //   last_dword = 15    (16 dwords)
    // Note: must use lsu_write_32 (not SEND_STDOUT_CTRL) because the slot
    // number is encoded in bits [12:8] and SEND_STDOUT_CTRL truncates to char.
    // ------------------------------------------------------------------
    VPRINTF(LOW, "[SETUP] Injecting HMAC512 key into KV slot %d via TB...\n", test_slot);
    lsu_write_32((uintptr_t) stdout, (test_slot << 8) | 0xa9);

    // ------------------------------------------------------------------
    // Step 2: Pre-read KEY_CTRL and prepare lock_use value
    //
    // We do this BEFORE triggering the read so there are zero extra
    // instructions (reads) between the KV read trigger and the lock_use
    // write. This maximizes the chance that lock_use takes effect mid-read.
    // ------------------------------------------------------------------
    uint32_t key_ctrl_addr = CLP_KV_REG_KEY_CTRL_0 + (test_slot * 4);
    uint32_t key_ctrl_val = lsu_read_32(key_ctrl_addr);
    VPRINTF(LOW, "[SETUP] KEY_CTRL[%d] = 0x%08x\n", test_slot, key_ctrl_val);

    uint32_t lock_val = key_ctrl_val | KV_REG_KEY_CTRL_0_LOCK_USE_MASK;

    // Wait for HMAC engine ready
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) &
            HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    // ------------------------------------------------------------------
    // Step 3: Trigger HMAC KV key read — starts a 16-beat read from KV
    // Step 4: Set lock_use after a short delay to ensure it lands after
    //         validated_read_en has de-asserted (i.e., after beat 0)
    //
    // The KV read takes ~18 cycles (2 cycles pipeline + 16 beats).
    // validated_read_en is a one-cycle pulse that fires ~2 cycles after
    // the KV_RD_CTRL write. We insert a few NOPs after the read trigger
    // to guarantee the lock_use write arrives after validated_read_en
    // has gone low, exercising the mid-read error detection path.
    //
    // With the old (buggy) code:
    //   - Beat 0: kv_resp.error=0, error_code=KV_SUCCESS
    //   - Beats 1-15: kv_resp.error=1 (lock_use now active), but
    //     validated_read_en=0 so error not captured → KV_SUCCESS
    //
    // With the fix:
    //   - Beat 0: kv_resp.error=0, error_code=KV_SUCCESS
    //   - Beats 1+: kv_resp.error=1, read_allow=1 → KV_READ_FAIL
    // ------------------------------------------------------------------
    VPRINTF(LOW, "[TEST] Triggering HMAC KV key read + delayed lock_use...\n");

    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL,
                 HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                 ((test_slot << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) &
                  HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

    // Delay ~3 cycles so lock_use lands after validated_read_en de-asserts
    __asm__ volatile ("nop");
    __asm__ volatile ("nop");
    __asm__ volatile ("nop");

    lsu_write_32(key_ctrl_addr, lock_val);

    // ------------------------------------------------------------------
    // Step 5: Wait for read to complete and check error
    // ------------------------------------------------------------------
    while ((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) &
            HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK) == 0);

    status = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS);
    error_field = (status & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_MASK) >>
                  HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_LOW;

    VPRINTF(LOW, "[RESULT] HMAC KV_RD_KEY_STATUS = 0x%08x (error=0x%02x)\n",
            status, error_field);

    if (error_field == 0) {
        VPRINTF(ERROR, "[FAIL] lock_use set mid-read but error_code = KV_SUCCESS!\n");
        VPRINTF(ERROR, "       Crypto engine received partially-zeroed key "
                       "without error detection.\n");
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "[PASS] Mid-read lock_use correctly reported error=0x%02x\n",
            error_field);

    // ------------------------------------------------------------------
    // Step 6: Verify lock_use is sticky (cannot be cleared by SW)
    // ------------------------------------------------------------------
    uint32_t key_ctrl_readback = lsu_read_32(key_ctrl_addr);
    if (!(key_ctrl_readback & KV_REG_KEY_CTRL_0_LOCK_USE_MASK)) {
        VPRINTF(ERROR, "[FAIL] lock_use bit not set after write!\n");
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }

    uint32_t clear_val = key_ctrl_readback & ~KV_REG_KEY_CTRL_0_LOCK_USE_MASK;
    lsu_write_32(key_ctrl_addr, clear_val);
    key_ctrl_readback = lsu_read_32(key_ctrl_addr);

    if (!(key_ctrl_readback & KV_REG_KEY_CTRL_0_LOCK_USE_MASK)) {
        VPRINTF(ERROR, "[FAIL] lock_use was cleared by SW — not sticky!\n");
        SEND_STDOUT_CTRL(0x01);
        while(1);
    }
    VPRINTF(LOW, "[PASS] lock_use is sticky — cannot be cleared by SW\n");

    // ------------------------------------------------------------------
    // Done
    // ------------------------------------------------------------------
    VPRINTF(LOW, "\n============================================================\n");
    VPRINTF(LOW, " ALL CHECKS PASSED\n");
    VPRINTF(LOW, "============================================================\n");
    SEND_STDOUT_CTRL(0xff);
}
