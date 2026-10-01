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
//   Directed test for "KV write controls must be cleared on zeroize".
//
//   Bug being covered (caliptra-rtl issue #1159):
//     A crypto operation that fails never produces a result, so the KV write
//     FSM never runs and therefore never clears KV_WR_CTRL.write_en through
//     the ~kv_write_ready term. The stale write_en leaves dest_keyvault
//     asserted, so the *next* (good) operation silently routes its result to
//     the key vault instead of the SW-readable result registers, which then
//     read back as all zeros.
//
//   The fix adds zeroize to the hwclr term of KV_WR_CTRL.write_en and
//   KV_WR_STATUS.VALID in HMAC, ECC and AES.
//
//   Test phases (single run, no reset needed - zeroize is the recovery):
//     Phase 0 - HMAC: arm KV write, inject an all-zero KV key so the engine
//               raises key_zero_error, zeroize, then check
//                 a) HMAC512_KV_WR_CTRL.write_en == 0
//                 b) a following SW-key HMAC512 lands in HMAC512_TAG (non-zero)
//     Phase 1 - ECC : arm KV write, launch KEYGEN with PCR_SIGN set so the
//               engine raises pcr_sign_input_invalid, zeroize, then check
//                 a) ECC_KV_WR_PKEY_CTRL.write_en == 0
//                 b) a following SW-seed KEYGEN lands in ECC_PRIVKEY_OUT
//
//   AES is not exercised here: its only zeroize source is
//   debugUnlock_or_scan_mode_switch, which is covered by
//   smoke_test_kv_write_scan_mode and by the AES SVA in caliptra_top_sva.sv.
//
//   Without the RTL fix both (a) and (b) fail in each phase.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "hmac.h"
#include "ecc.h"
#include "caliptra_rtl_lib.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile uint32_t* stdout     = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define FAIL_CMD 0x1

// KV slot holding the injected all-zero HMAC key (crypto-error source)
#define KV_SLOT_ZERO_KEY 3
// KV slot the engines are (incorrectly) left armed to write into
#define KV_SLOT_STALE_WR 5

static uint32_t error_count = 0;

// Aborts the test immediately - used when the stimulus itself did not take
// effect and the remaining checks would be meaningless.
static void fail(const char *msg) {
    VPRINTF(ERROR, "%s\n", msg);
    SEND_STDOUT_CTRL(FAIL_CMD);
    while(1);
}

// Records a check failure but keeps going, so a single run reports every
// symptom of the bug (stale write_en *and* the diverted result) instead of
// stopping at the first one.
static void check_failed(const char *msg) {
    VPRINTF(ERROR, "%s\n", msg);
    error_count++;
}

//----------------------------------------------------------------------------
// Phase 0: HMAC
//----------------------------------------------------------------------------
static void hmac_phase(void) {
    volatile uint32_t *reg_ptr;
    uint32_t           kv_wr_ctrl;
    uint32_t           tag_or;
    uint8_t            offset;

    VPRINTF(LOW, "\n=== PHASE 0: HMAC KV write ctrl cleared by zeroize ===\n");

    while((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    // Inject an all-zero HMAC key into the key vault so the HMAC engine will
    // raise key_zero_error and abort before producing a tag.
    VPRINTF(LOW, "Injecting all-zero HMAC key into KV\n");
    SEND_STDOUT_CTRL(0xa8);

    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL,
                 HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                 ((KV_SLOT_ZERO_KEY << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) &
                  HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

    while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) &
           (HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK |
            HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_MASK)) == 0);

    if ((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) &
         HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_MASK) != 0) {
        fail("unexpected KV read error while loading the zero HMAC key");
    }

    // Arm the KV write path for the operation that is about to fail
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL,
                 HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
                 HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK |
                 HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK |
                 ((KV_SLOT_STALE_WR << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) &
                  HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK));

    kv_wr_ctrl = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL);
    if ((kv_wr_ctrl & HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK) == 0) {
        fail("HMAC KV_WR_CTRL.write_en did not take the SW write");
    }

    // Trigger the failing operation (zero key -> key_zero_error, no tag)
    VPRINTF(LOW, "Starting HMAC512 with an all-zero KV key - expecting the key-zero abort\n");
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL,
                 HMAC_REG_HMAC512_CTRL_INIT_MASK |
                 (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));

    wait_for_hmac_intr();
    if (cptra_intr_rcv.hmac_error == 0) {
        fail("HMAC key_zero_error was not reported - crypto error injection failed");
    }
    cptra_intr_rcv.hmac_error = 0;
    cptra_intr_rcv.hmac_notif = 0;

    // Failed operation never ran the KV write FSM, so write_en is still armed.
    kv_wr_ctrl = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL);
    VPRINTF(LOW, "After failed op: HMAC512_KV_WR_CTRL = 0x%x (write_en=%d)\n",
            kv_wr_ctrl, kv_wr_ctrl & HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK);

    // Zeroize is the documented recovery from a failed operation
    hmac_zeroize();
    while((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    // CHECK (a): zeroize must disarm the KV write request
    kv_wr_ctrl = lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL);
    VPRINTF(LOW, "After zeroize: HMAC512_KV_WR_CTRL = 0x%x\n", kv_wr_ctrl);
    if ((kv_wr_ctrl & HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK) != 0) {
        check_failed("HMAC512_KV_WR_CTRL.write_en still set after zeroize");
    }
    if ((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS) &
         HMAC_REG_HMAC512_KV_WR_STATUS_VALID_MASK) != 0) {
        check_failed("HMAC512_KV_WR_STATUS.VALID still set after zeroize");
    }

    // CHECK (b): the next SW-driven operation must land in the TAG registers
    VPRINTF(LOW, "Running a clean SW-key HMAC512 and checking TAG readback\n");

    reg_ptr = (uint32_t *) CLP_HMAC_REG_HMAC512_KEY_0;
    offset  = 0;
    while (reg_ptr <= (uint32_t *) CLP_HMAC_REG_HMAC512_KEY_15) {
        *reg_ptr++ = 0xA5A5A500 + offset++;
    }

    reg_ptr = (uint32_t *) CLP_HMAC_REG_HMAC512_BLOCK_0;
    offset  = 0;
    while (reg_ptr <= (uint32_t *) CLP_HMAC_REG_HMAC512_BLOCK_31) {
        *reg_ptr++ = 0x5A5A5A00 + offset++;
    }

    reg_ptr = (uint32_t *) CLP_HMAC_REG_HMAC512_LFSR_SEED_0;
    offset  = 0;
    while (reg_ptr <= (uint32_t *) CLP_HMAC_REG_HMAC512_LFSR_SEED_5) {
        *reg_ptr++ = 0xC0FFEE00 + offset++;
    }

    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL,
                 HMAC_REG_HMAC512_CTRL_INIT_MASK |
                 HMAC_REG_HMAC512_CTRL_LAST_MASK |
                 (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));

    wait_for_hmac_intr();
    if (cptra_intr_rcv.hmac_error != 0) {
        // On broken RTL the stale KV write request can also surface here as a
        // KV write error - report it but keep going so the TAG check below
        // still runs.
        check_failed("unexpected HMAC error on the clean SW-key operation");
        cptra_intr_rcv.hmac_error = 0;
    } else {
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_VALID_MASK) == 0);
    }
    cptra_intr_rcv.hmac_notif = 0;

    tag_or  = 0;
    reg_ptr = (uint32_t *) CLP_HMAC_REG_HMAC512_TAG_0;
    while (reg_ptr <= (uint32_t *) CLP_HMAC_REG_HMAC512_TAG_15) {
        tag_or |= *reg_ptr++;
    }

    VPRINTF(LOW, "Clean HMAC512 TAG OR = 0x%x\n", tag_or);
    if (tag_or == 0) {
        check_failed("HMAC512_TAG is all-zero - stale KV write_en diverted the tag to the key vault");
    } else {
        VPRINTF(LOW, "PHASE 0 check (b) passed - TAG readback is non-zero\n");
    }

    hmac_zeroize();
}

//----------------------------------------------------------------------------
// Phase 1: ECC
//----------------------------------------------------------------------------
static void ecc_phase(void) {
    volatile uint32_t *reg_ptr;
    uint32_t           kv_wr_ctrl;
    uint32_t           privkey_or;
    uint8_t            offset;

    VPRINTF(LOW, "\n=== PHASE 1: ECC KV write ctrl cleared by zeroize ===\n");

    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    // Arm the KV write path for the operation that is about to fail
    lsu_write_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL,
                 ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                 ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK |
                 ((KV_SLOT_STALE_WR << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) &
                  ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK));

    kv_wr_ctrl = lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL);
    if ((kv_wr_ctrl & ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK) == 0) {
        fail("ECC KV_WR_PKEY_CTRL.write_en did not take the SW write");
    }

    // Inject the crypto error: KEYGEN is illegal while PCR_SIGN is set, so the
    // DSA FSM aborts immediately and never produces a private key.
    VPRINTF(LOW, "Starting ECC KEYGEN with PCR_SIGN set - expecting the pcr_sign_input_invalid abort\n");
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_KEYGEN | ECC_REG_ECC_CTRL_PCR_SIGN_MASK);

    wait_for_ecc_intr();
    if (cptra_intr_rcv.ecc_error == 0) {
        fail("ECC error interrupt was not reported - crypto error injection failed");
    }
    cptra_intr_rcv.ecc_error = 0;
    cptra_intr_rcv.ecc_notif = 0;

    kv_wr_ctrl = lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL);
    VPRINTF(LOW, "After failed op: ECC_KV_WR_PKEY_CTRL = 0x%x (write_en=%d)\n",
            kv_wr_ctrl, kv_wr_ctrl & ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK);

    ecc_zeroize();
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    // CHECK (a): zeroize must disarm the KV write request
    kv_wr_ctrl = lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL);
    VPRINTF(LOW, "After zeroize: ECC_KV_WR_PKEY_CTRL = 0x%x\n", kv_wr_ctrl);
    if ((kv_wr_ctrl & ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK) != 0) {
        check_failed("ECC_KV_WR_PKEY_CTRL.write_en still set after zeroize");
    }
    if ((lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_STATUS) &
         ECC_REG_ECC_KV_WR_PKEY_STATUS_VALID_MASK) != 0) {
        check_failed("ECC_KV_WR_PKEY_STATUS.VALID still set after zeroize");
    }

    // CHECK (b): the next SW-driven KEYGEN must land in ECC_PRIVKEY_OUT
    VPRINTF(LOW, "Running a clean SW-seed ECC KEYGEN and checking PRIVKEY_OUT readback\n");

    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_SEED_0;
    offset  = 0;
    while (reg_ptr <= (uint32_t *) CLP_ECC_REG_ECC_SEED_11) {
        *reg_ptr++ = 0x1234AB00 + offset++;
    }

    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_NONCE_0;
    offset  = 0;
    while (reg_ptr <= (uint32_t *) CLP_ECC_REG_ECC_NONCE_11) {
        *reg_ptr++ = 0x5678CD00 + offset++;
    }

    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_IV_0;
    offset  = 0;
    while (reg_ptr <= (uint32_t *) CLP_ECC_REG_ECC_IV_11) {
        *reg_ptr++ = 0x9ABCEF00 + offset++;
    }

    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_KEYGEN);

    wait_for_ecc_intr();
    if (cptra_intr_rcv.ecc_error != 0) {
        check_failed("unexpected ECC error on the clean SW-seed KEYGEN");
        cptra_intr_rcv.ecc_error = 0;
    } else {
        while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_VALID_MASK) == 0);
    }
    cptra_intr_rcv.ecc_notif = 0;

    privkey_or = 0;
    reg_ptr    = (uint32_t *) CLP_ECC_REG_ECC_PRIVKEY_OUT_0;
    while (reg_ptr <= (uint32_t *) CLP_ECC_REG_ECC_PRIVKEY_OUT_11) {
        privkey_or |= *reg_ptr++;
    }

    VPRINTF(LOW, "Clean ECC KEYGEN PRIVKEY_OUT OR = 0x%x\n", privkey_or);
    if (privkey_or == 0) {
        check_failed("ECC_PRIVKEY_OUT is all-zero - stale KV write_en diverted the key to the key vault");
    } else {
        VPRINTF(LOW, "PHASE 1 check (b) passed - PRIVKEY_OUT readback is non-zero\n");
    }

    ecc_zeroize();
}

void main(void) {

    VPRINTF(LOW, "--------------------------------------------------\n");
    VPRINTF(LOW, " KV write control cleared on zeroize - smoke test\n");
    VPRINTF(LOW, "--------------------------------------------------\n");

    init_interrupts();

    hmac_phase();
    ecc_phase();

    if (error_count != 0) {
        VPRINTF(ERROR, "\n KV write control zeroize test failed %d check(s)\n", error_count);
        SEND_STDOUT_CTRL(FAIL_CMD);
        while(1);
    }

    VPRINTF(LOW, "\n--------------------------------------------------\n");
    VPRINTF(LOW, " KV write control zeroize test PASSED\n");
    VPRINTF(LOW, "--------------------------------------------------\n");

    SEND_STDOUT_CTRL(0xff);
    while(1);
}
