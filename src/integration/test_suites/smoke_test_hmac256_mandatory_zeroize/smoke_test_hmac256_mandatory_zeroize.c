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
// HMAC-256 mandatory-zeroize test. This is the HMAC256 counterpart of
// smoke_test_hmac_mandatory_zeroize, which covers the same contract for
// HMAC512. Two independent properties are checked:
//
// PART A - the mandatory-zeroize command barrier.
//   After any completed SW-visible operation, hmac256 latches
//   awaiting_zeroize and parks with STATUS.READY=0 until firmware writes
//   HMAC256_CTRL.ZEROIZE. Because CTRL.*.swwe is driven by ready_reg,
//   CTRL writes during the parked window are dropped, so a stray
//   INIT/NEXT/LAST cannot bypass the zeroize step. After ZEROIZE,
//   STATUS.READY recovers and a new operation runs normally.
//
// PART B - busy_o must NOT be held through the awaiting_zeroize window.
//   hmac256_busy feeds the concurrent-crypto detector in caliptra_top
//   (crypto_error -> cptra_hw_fatal_errors.crypto_err, non-recoverable).
//   ZEROIZE hwclr's the TAG registers, so firmware must read the tag
//   before zeroizing; that read window is structurally unavoidable. If
//   busy_o stayed asserted across it, starting any second engine would
//   raise a spurious fatal crypto_err. This part starts a real HMAC512
//   operation while hmac256 is parked awaiting zeroize and requires that
//   CPTRA_HW_ERROR_FATAL.crypto_err stays clear.
//
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "hmac256.h"
#include "hmac.h"
#include "caliptra_rtl_lib.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// HMAC-256 single-block vector, shared with smoke_test_hmac256.
static uint32_t key_data[HMAC256_KEY_SIZE] = {
    0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
    0x0b0b0b0b, 0x00000000, 0x00000000, 0x00000000
};

static uint32_t block_data[HMAC256_BLOCK_SIZE] = {
    0x48692054, 0x68657265, 0x80000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000240
};

static uint32_t expected_tag[HMAC256_TAG_SIZE] = {
    0xb0344c61, 0xd8db3853, 0x5ca8afce, 0xaf0bf12b,
    0x881dc200, 0xc9833da7, 0x26e9376c, 0x2e32cff7
};

static uint32_t lfsr_seed_data[HMAC256_LFSR_SEED_SIZE] = {
    0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C
};

// HMAC-512 vector, only used to create concurrent engine activity in PART B.
static uint32_t hmac512_key[16] = {
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,
    0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b,0x0b0b0b0b};

static uint32_t hmac512_block[32] = {
    0x48692054,0x68657265,0x80000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000440};

static uint32_t hmac512_lfsr_seed[6] = {
    0xfeedface,0xdeadbeef,0xcafef00d,0x12345678,0x9abcdef0,0x0badc0de};

static void fail(const char *msg) {
    VPRINTF(FATAL, "FAIL: %s\n", msg);
    SEND_STDOUT_CTRL(0x1);
    while (1);
}

static void delay_cycles(int n) {
    for (volatile int i = 0; i < n; i++) { __asm__ volatile ("nop"); }
}

static uint32_t hmac256_status(void) {
    return lsu_read_32(CLP_HMAC256_REG_HMAC256_STATUS);
}

// Runs one INIT|LAST single-block HMAC-256 operation and leaves the engine
// parked in awaiting_zeroize. Does not zeroize.
static void run_single_block_op(void) {
    hmac256_wait_ready();
    cptra_intr_rcv.hmac256_notif = 0;
    cptra_intr_rcv.hmac256_error = 0;
    hmac256_load_inputs(key_data, block_data, lfsr_seed_data);
    hmac256_ctrl_write(HMAC256_REG_HMAC256_CTRL_INIT_MASK |
                       HMAC256_REG_HMAC256_CTRL_LAST_MASK, 1u);
    wait_for_hmac256_intr();
    if (cptra_intr_rcv.hmac256_error != 0) {
        fail("unexpected HMAC256 error interrupt during a legal operation");
    }
}

static void check_tag_matches(void) {
    volatile uint32_t *tag = (volatile uint32_t *)CLP_HMAC256_REG_HMAC256_TAG_0;
    for (int i = 0; i < HMAC256_TAG_SIZE; i++) {
        if (tag[i] != expected_tag[i]) {
            VPRINTF(FATAL, "FAIL: TAG[%0d]=0x%08x expected 0x%08x\n",
                    i, tag[i], expected_tag[i]);
            SEND_STDOUT_CTRL(0x1);
            while (1);
        }
    }
}

static uint32_t crypto_err_asserted(void) {
    return lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL) &
           SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_MASK;
}

void main(void) {
    SEND_STDOUT_CTRL(0x7F);

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC-SHA-256 mandatory-zeroize test\n");
    VPRINTF(LOW, "----------------------------------\n");

    init_interrupts();

    // A crypto_err latched before the test starts would mask PART B.
    if (crypto_err_asserted()) {
        fail("CPTRA_HW_ERROR_FATAL.crypto_err already set at test start");
    }

    // ---------------------------------------------------------------
    // PART A - mandatory-zeroize command barrier
    // ---------------------------------------------------------------
    run_single_block_op();
    check_tag_matches();
    VPRINTF(LOW, "PART A: first operation completed, TAG matched\n");

    // The engine must park: STATUS.READY stays low until ZEROIZE.
    delay_cycles(64);
    if (hmac256_status() & HMAC256_REG_HMAC256_STATUS_READY_MASK) {
        fail("STATUS.READY high after final op - awaiting_zeroize gate missing");
    }
    VPRINTF(LOW, "PART A: engine parked with STATUS.READY=0\n");

    // A CTRL write while parked must be dropped (swwe = ready_reg), so no
    // new operation may start and READY must not come back on its own.
    cptra_intr_rcv.hmac256_notif = 0;
    cptra_intr_rcv.hmac256_error = 0;
    hmac256_ctrl_write(HMAC256_REG_HMAC256_CTRL_INIT_MASK |
                       HMAC256_REG_HMAC256_CTRL_LAST_MASK, 1u);
    delay_cycles(256);
    if (cptra_intr_rcv.hmac256_notif != 0) {
        fail("engine accepted INIT|LAST without a preceding ZEROIZE");
    }
    if (hmac256_status() & HMAC256_REG_HMAC256_STATUS_READY_MASK) {
        fail("STATUS.READY went high without a preceding ZEROIZE");
    }
    VPRINTF(LOW, "PART A: stray INIT|LAST correctly dropped\n");

    // ---------------------------------------------------------------
    // PART B - busy_o must not block other engines while parked
    // ---------------------------------------------------------------
    // hmac256 is still parked in awaiting_zeroize here. Running HMAC512
    // now exercises the (hmac_busy & hmac256_busy) crypto_error term.
    hmac_wait_ready();
    hmac_load_inputs(hmac512_key, hmac512_block, hmac512_lfsr_seed);
    hmac512_ctrl_write(HMAC_REG_HMAC512_CTRL_INIT_MASK |
                       HMAC_REG_HMAC512_CTRL_LAST_MASK, FALSE);
    hmac_wait_valid();
    if (crypto_err_asserted()) {
        fail("spurious crypto_err: hmac256 busy_o held through awaiting_zeroize");
    }
    hmac_zeroize();
    hmac_wait_ready();
    VPRINTF(LOW, "PART B: concurrent HMAC512 op raised no crypto_err\n");

    // hmac256 must still be parked - the HMAC512 activity must not have
    // cleared its pending-zeroize state.
    if (hmac256_status() & HMAC256_REG_HMAC256_STATUS_READY_MASK) {
        fail("HMAC256 left awaiting_zeroize without an explicit ZEROIZE");
    }

    // ---------------------------------------------------------------
    // Recovery - ZEROIZE releases the barrier and the engine works again
    // ---------------------------------------------------------------
    hmac256_zeroize();
    hmac256_wait_ready();
    VPRINTF(LOW, "STATUS.READY recovered after ZEROIZE\n");

    run_single_block_op();
    check_tag_matches();
    hmac256_zeroize();
    hmac256_wait_ready();

    if (crypto_err_asserted()) {
        fail("crypto_err asserted by the end of the test");
    }

    VPRINTF(LOW, "HMAC-SHA-256 mandatory-zeroize test passed\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
