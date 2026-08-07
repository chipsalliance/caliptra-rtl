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
// KV length-mismatch — AES key path (single-shot randomized).
// Exercises BOTH check-timing orderings on each invocation:
//   Order A — set CTRL_SHADOWED.key_len → then KV read.
//             Fires the first-edge check on kv_key_done.
//   Order B — set an initial permissive key_len (AES-128) → KV read →
//             then reprogram CTRL_SHADOWED.key_len to the target size.
//             Fires the deferred check via keymgr_key.valid
//             (LEN_CHECK_AT_KEY_USE=1 arms check_key_size on this edge too).
//
// Regression obtains ordering/consumer/slot/last_dword diversity through
// PLAYBOOK_RANDOM_SEED across nightly runs; the deferred-check hit window
// (last_dword ∈ [3, expected(target)-1] under Order B) is covered
// probabilistically.
//
// AES key expected sizes (from CTRL_SHADOWED.key_len):
//   AES-128 → expected=3   (4 dwords)
//   AES-192 → expected=5   (6 dwords)
//   AES-256 → expected=7   (8 dwords)
// dest_valid bit5 = AES_KEY (encoded 0x20).
//
// AES has no CPU-visible interrupt: error_intr/notif_intr are tied off in
// aes_clp_wrapper.sv and dropped at caliptra_top.sv:1268. FW MUST poll
// AES_KV_RD_KEY_STATUS.ERROR — both after VALID rises AND after any
// reprogram of CTRL_SHADOWED.KEY_LEN that follows a KV key read
// (LEN_CHECK_AT_KEY_USE=1 fires the deferred check at the second edge).
//
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
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

#define DV_AES_KEY 0x20u

// aes_key_len_e codes.
#define AES_KEY_LEN_128 0x1u
#define AES_KEY_LEN_192 0x2u
#define AES_KEY_LEN_256 0x4u

enum { AES_128 = 0, AES_192 = 1, AES_256 = 2 };

static const char* consumer_name(int c) {
    switch (c) {
    case AES_128: return "AES_128";
    case AES_192: return "AES_192";
    case AES_256: return "AES_256";
    default:      return "?";
    }
}

static uint32_t kv_get_err(uint32_t s) { return (s >> 2) & 0xffu; }

static void fail_test(const char* m){
    VPRINTF(FATAL,"TEST FAIL: %s\n", m);
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

static inline void kv_inject(uint8_t slot, uint8_t last_dword, uint8_t dest_valid) {
    uint32_t cmd = 0xa2u
                 | ((uint32_t)(slot & 0x1Fu) << 8)
                 | ((uint32_t)(last_dword & 0xFu) << 13)
                 | ((uint32_t)dest_valid << 17);
    lsu_write_32((uintptr_t)stdout, cmd);
    for (volatile int i = 0; i < 32; i++) __asm__ volatile("nop");
}

// AES CTRL_SHADOWED is a shadow register — must be written twice.
static void aes_set_key_len(uint32_t key_len_code) {
    uint32_t v = (key_len_code & 0x7u) << AES_REG_CTRL_SHADOWED_KEY_LEN_LOW;
    lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, v);
    lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, v);
}

static uint32_t aes_kv_read_and_wait(uint8_t slot) {
    kv_read_ctrl(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL, slot);
    for (volatile int i = 0; i < 64; i++) __asm__ volatile("nop");
    for (volatile int i = 0; i < 20000; i++) {
        uint32_t s = lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS);
        if (s & AES_CLP_REG_AES_KV_RD_KEY_STATUS_VALID_MASK) return s;
    }
    return lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS);
}

void main(void) {
    VPRINTF(LOW, "-------------------------------------------------\n");
    VPRINTF(LOW, " KV length-mismatch — AES (single-shot random)\n");
    VPRINTF(LOW, "-------------------------------------------------\n");
    init_interrupts();

#ifdef MY_RANDOM_SEED
    unsigned rand_seed = (unsigned) MY_RANDOM_SEED;
#else
    unsigned rand_seed = 0xC8F518D4u;
#endif
    srand(rand_seed);
    VPRINTF(LOW, "seed=0x%x\n", rand_seed);

    uint8_t slot       = (uint8_t)(rand() % 24);
    uint8_t last_dword = (uint8_t)(rand() & 0xF);

    int consumer = rand() % 3;
    uint32_t key_len_code;
    uint8_t  expected;
    switch (consumer) {
    case AES_128: key_len_code = AES_KEY_LEN_128; expected = 3;  break;
    case AES_192: key_len_code = AES_KEY_LEN_192; expected = 5;  break;
    case AES_256:
    default:      key_len_code = AES_KEY_LEN_256; expected = 7;  break;
    }

    int order = rand() & 0x1;   // 0 = set-then-read (Order A); 1 = read-then-set (Order B)
    int expect_mismatch = (last_dword < expected);

    VPRINTF(LOW,
        "PARAMS: order=%c consumer=%s slot=%u last_dword=%u expected=%u expect_mismatch=%d\n",
        order ? 'B' : 'A', consumer_name(consumer), slot, last_dword,
        expected, expect_mismatch);

    // Inject KV entry.
    kv_inject(slot, last_dword, DV_AES_KEY);

    uint32_t st;
    uint32_t err;

    if (order == 0) {
        // ---------- Order A: set key_len BEFORE KV read ----------
        aes_set_key_len(key_len_code);
        st  = aes_kv_read_and_wait(slot);
        err = kv_get_err(st);
    } else {
        // ---------- Order B: KV read BEFORE final key_len ----------
        aes_set_key_len(AES_KEY_LEN_128);
        st = aes_kv_read_and_wait(slot);
        uint32_t first_err = kv_get_err(st);
        int first_edge_mismatch = (last_dword < 3);

        if (first_edge_mismatch) {
            if (first_err != KV_ERR_LEN_MISMATCH) {
                VPRINTF(FATAL, "first-edge STATUS=0x%x err=%u\n", st, first_err);
                fail_test("Order B first-edge expected LEN_MISMATCH");
            }
            err = first_err;
        } else {
            if (first_err != KV_ERR_SUCCESS) {
                VPRINTF(FATAL, "first-edge STATUS=0x%x err=%u\n", st, first_err);
                fail_test("Order B first-edge expected SUCCESS");
            }
            // Deferred trigger: reprogram key_len to target size.
            aes_set_key_len(key_len_code);
            for (volatile int i = 0; i < 64; i++) __asm__ volatile("nop");
            st  = lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS);
            err = kv_get_err(st);
        }
    }

    if (expect_mismatch) {
        if (err != KV_ERR_LEN_MISMATCH) {
            VPRINTF(FATAL, "STATUS=0x%x err=%u\n", st, err);
            fail_test("expected LEN_MISMATCH");
        }
    } else {
        if (err != KV_ERR_SUCCESS) {
            VPRINTF(FATAL, "STATUS=0x%x err=%u\n", st, err);
            fail_test("unexpected KV error");
        }
    }

    VPRINTF(LOW,
        "PASS: order=%c consumer=%s slot=%u last_dword=%u expected=%u "
        "expect_mismatch=%d STATUS=0x%x err=%u\n",
        order ? 'B' : 'A', consumer_name(consumer), slot, last_dword,
        expected, expect_mismatch, st, err);

    // Cleanup.
    lsu_write_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL, 0);
    lsu_write_32(CLP_AES_REG_TRIGGER,
                 AES_REG_TRIGGER_KEY_IV_DATA_IN_CLEAR_MASK);

    SEND_STDOUT_CTRL(0xff);
    while (1);
}
