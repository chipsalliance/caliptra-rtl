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
// KV length-mismatch — HMAC KEY path (single-shot randomized).
// Each invocation exercises exactly ONE KV read; the regression obtains
// diversity by running the test many times with distinct random seeds.
//
// Under universal relaxed semantics:
//   length_mismatch = (stored_last_dword < expected_key_size)
//
// HMAC KEY-side length check is enforced (crypto correctness: wrong-size
// key would produce a wrong HMAC). BLOCK-side length check is intentionally
// disabled — the HMAC block is a message chunk (not a security-sized key)
// and legitimate consumers (e.g., OCP LOCK HEK seed, 8 dwords → HMAC_BLOCK)
// rely on PAD=1 zero-extension for short entries.
//
// HMAC consumer expected sizes:
//   HMAC-384 key → 11
//   HMAC-512 key → 15
// dest_valid bits: bit0=HMAC_KEY, bit1=HMAC_BLOCK
//
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "hmac.h"
#include "keyvault.h"
#include "caliptra_rtl_lib.h"

volatile uint32_t* stdout = (uint32_t *)STDOUT;
volatile uint32_t intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define KV_ERR_SUCCESS      0u
#define KV_ERR_LEN_MISMATCH 3u

#define DV_HMAC_KEY   0x01u
#define DV_HMAC_BLOCK 0x02u

// Consumer enumeration (KEY paths only — BLOCK-side length check removed).
enum { HMAC_384_KEY = 0, HMAC_512_KEY };

static const char* consumer_name(int c) {
    switch (c) {
    case HMAC_384_KEY:   return "HMAC_384_KEY";
    case HMAC_512_KEY:   return "HMAC_512_KEY";
    default:             return "?";
    }
}

static uint32_t kv_get_err(uint32_t s) { return (s >> 2) & 0xffu; }

static void fail_test(const char* m){
    VPRINTF(FATAL,"TEST FAIL: %s\n", m);
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

// TB inject cmd 0xa2 — arbitrary slot/last_dword/dest_valid.
static inline void kv_inject(uint8_t slot, uint8_t last_dword, uint8_t dest_valid) {
    uint32_t cmd = 0xa2u
                 | ((uint32_t)(slot & 0x1Fu) << 8)
                 | ((uint32_t)(last_dword & 0xFu) << 13)
                 | ((uint32_t)dest_valid << 17);
    lsu_write_32((uintptr_t)stdout, cmd);
    for (volatile int i = 0; i < 32; i++) __asm__ volatile("nop");
}

// Bounded VALID poll. Waits a moderate window of nops after issuing the
// read_en so RTL has time to clear any stale VALID before we sample.
static uint32_t kv_read_and_wait(uint32_t rd_ctrl, uint32_t rd_status,
                                 uint8_t slot) {
    kv_read_ctrl(rd_ctrl, slot);
    for (volatile int i = 0; i < 64; i++) __asm__ volatile("nop");
    for (volatile int i = 0; i < 20000; i++) {
        uint32_t s = lsu_read_32(rd_status);
        if (s & KV_RD_STATUS_VALID_MASK) return s;
    }
    return lsu_read_32(rd_status);
}

void main(void) {
    VPRINTF(LOW, "-------------------------------------------------\n");
    VPRINTF(LOW, " KV length-mismatch — HMAC (single-shot random)\n");
    VPRINTF(LOW, "-------------------------------------------------\n");
    init_interrupts();

    // Seed selection: honour MY_RANDOM_SEED when provided by the regression.
#ifdef MY_RANDOM_SEED
    unsigned rand_seed = (unsigned) MY_RANDOM_SEED;
#else
    unsigned rand_seed = 0xC8F518D4u;
#endif
    srand(rand_seed);
    VPRINTF(LOW, "seed=0x%x\n", rand_seed);

    // 1. Randomize slot and last_dword.
    uint8_t slot       = (uint8_t)(rand() % 24);
    uint8_t last_dword = (uint8_t)(rand() & 0xF);

    // 2. Pick consumer (HMAC-384/512 KEY only).
    int consumer = rand() & 0x1;
    uint32_t rd_ctrl, rd_status;
    uint8_t  dv;
    uint8_t  expected;
    switch (consumer) {
    case HMAC_384_KEY:
        rd_ctrl   = CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL;
        rd_status = CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS;
        dv        = DV_HMAC_KEY;
        expected  = 11;
        break;
    case HMAC_512_KEY:
    default:
        rd_ctrl   = CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL;
        rd_status = CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS;
        dv        = DV_HMAC_KEY;
        expected  = 15;
        break;
    }

    // 3. Predict outcome.
    int expect_mismatch = (last_dword < expected);

    VPRINTF(LOW,
        "PARAMS: consumer=%s slot=%u last_dword=%u expected=%u expect_mismatch=%d\n",
        consumer_name(consumer), slot, last_dword, expected, expect_mismatch);

    // 4. Inject KV entry.
    kv_inject(slot, last_dword, dv);

    // 5. Trigger KV read + bounded wait. For HMAC, LEN_CHECK_AT_KEY_USE=1
    //    so the length check fires on INIT/NEXT (not on read completion) —
    //    KV_RD_STATUS.ERROR at this point is still KV_SUCCESS regardless
    //    of last_dword.
    uint32_t st_after_read = kv_read_and_wait(rd_ctrl, rd_status, slot);
    VPRINTF(LOW, "post-KV-read: STATUS=0x%x (before INIT, no check fired yet)\n",
            st_after_read);

    // 6. Preload block + LFSR seed and trigger INIT with the chosen mode.
    //    KEY-side test — block is FW-loaded.
    volatile uint32_t* bp = (uint32_t*) CLP_HMAC_REG_HMAC512_BLOCK_0;
    for (int i = 0; i < 32; i++) *bp++ = (i == 31) ? 0x00000440u : 0;
    volatile uint32_t* lp = (uint32_t*) CLP_HMAC_REG_HMAC512_LFSR_SEED_0;
    for (int i = 0; i < 12; i++) *lp++ = 0xC8F518D4u + i;

    // Disable HMAC error interrupts before triggering INIT. On a mismatched
    // KV read, HMAC may internally assert key_zero_error or key_mode_error
    // (when the injected upper key dwords are still zero because last_dword
    // < the mode's requirement). With the ISR stub as a no-op, an
    // unmasked error_intr would storm the CPU and hang the test. This test
    // is specifically validating the KV_RD_LEN_MISMATCH contract via
    // STATUS.ERROR polling; other HMAC error-interrupt paths are exercised
    // elsewhere.
    lsu_write_32(CLP_HMAC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R, 0);

    uint32_t hmac_mode = (consumer == HMAC_512_KEY) ? 1u : 0u;
    // Set MODE and INIT together (per the HMAC engine's programming model).
    uint32_t ctrl_val  = HMAC_REG_HMAC512_CTRL_INIT_MASK
                       | ((hmac_mode & 1u) << HMAC_REG_HMAC512_CTRL_MODE_LOW);
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, ctrl_val);

    // 7. Wait for either HMAC completion (positive case) or the check to
    //    settle (negative case).
    if (expect_mismatch) {
        // Length check + hwclr + register update: 32 nops is safe headroom.
        for (volatile int i = 0; i < 32; i++) __asm__ volatile("nop");
    } else {
        // Poll HMAC completion.
        for (volatile int i = 0; i < 20000; i++) {
            uint32_t hs = lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS);
            if (hs & HMAC_REG_HMAC512_STATUS_VALID_MASK) break;
        }
    }

    // 8. Read KV_RD_STATUS.ERROR (now reflects post-INIT check outcome).
    uint32_t st  = lsu_read_32(rd_status);
    uint32_t err = kv_get_err(st);
    uint32_t hs  = lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS);

    // 9. Verify.
    //    Security contract: on KEY-path mismatch, FW must observe
    //    KV_RD_STATUS.ERROR=KV_RD_LEN_MISMATCH after INIT, and HMAC must
    //    NOT complete (cleared key prevents the engine from advancing).
    //    BLOCK-path length check is intentionally disabled — see hmac.sv.
    if (expect_mismatch) {
        if (err != KV_ERR_LEN_MISMATCH) {
            VPRINTF(FATAL, "post-INIT STATUS=0x%x err=%u HMAC_STATUS=0x%x\n", st, err, hs);
            fail_test("expected LEN_MISMATCH after INIT");
        }
    } else {
        if (err != KV_ERR_SUCCESS) {
            VPRINTF(FATAL, "STATUS=0x%x err=%u\n", st, err);
            fail_test("unexpected KV error on positive case");
        }
        if (!(hs & HMAC_REG_HMAC512_STATUS_VALID_MASK)) {
            fail_test("HMAC did not complete on positive case");
        }
    }

    VPRINTF(LOW,
        "PASS: consumer=%s slot=%u last_dword=%u expected=%u "
        "expect_mismatch=%d KV_RD_STATUS=0x%x err=%u HMAC_STATUS=0x%x\n",
        consumer_name(consumer), slot, last_dword, expected,
        expect_mismatch, st, err, hs);

    // Cleanup.
    lsu_write_32(rd_ctrl, 0);
    hmac_zeroize();

    SEND_STDOUT_CTRL(0xff);
    while (1);
}
