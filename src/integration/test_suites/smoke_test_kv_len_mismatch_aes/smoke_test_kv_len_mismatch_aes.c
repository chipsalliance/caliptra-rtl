// SPDX-License-Identifier: Apache-2.0
//
// KV length-mismatch — AES key path (single-shot randomized).
// Round-6 rewrite. Each invocation exercises exactly ONE KV read.
//
// AES key expected sizes (from CTRL_SHADOWED.key_len):
//   AES-128 → expected=3   (4 dwords)
//   AES-192 → expected=5   (6 dwords)
//   AES-256 → expected=7   (8 dwords)
// dest_valid bit5 = AES_KEY (encoded 0x20).
//
// Note: AES gates check_key_size on (kv_key_done | keymgr_key.valid).
// To ensure aes_expected_key_size is set correctly for the KV read, we
// shadow-write CTRL_SHADOWED.key_len BEFORE issuing kv_read_ctrl. AES has
// no error_intr — we poll AES_KV_RD_KEY_STATUS.VALID and read ERROR.
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

    int expect_mismatch = (last_dword < expected);

    VPRINTF(LOW,
        "PARAMS: consumer=%s slot=%u last_dword=%u expected=%u expect_mismatch=%d\n",
        consumer_name(consumer), slot, last_dword, expected, expect_mismatch);

    // Inject KV entry first.
    kv_inject(slot, last_dword, DV_AES_KEY);

    // Program AES CTRL_SHADOWED.key_len BEFORE triggering the KV read so that
    // aes_expected_key_size latches the correct value when the key arrives.
    aes_set_key_len(key_len_code);

    // Trigger KV read + bounded wait on AES_KV_RD_KEY_STATUS.VALID.
    uint32_t st  = aes_kv_read_and_wait(slot);
    uint32_t err = kv_get_err(st);

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
        "PASS: consumer=%s slot=%u last_dword=%u expected=%u "
        "expect_mismatch=%d STATUS=0x%x err=%u\n",
        consumer_name(consumer), slot, last_dword, expected,
        expect_mismatch, st, err);

    // Cleanup.
    lsu_write_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL, 0);
    lsu_write_32(CLP_AES_REG_TRIGGER,
                 AES_REG_TRIGGER_KEY_IV_DATA_IN_CLEAR_MASK);

    SEND_STDOUT_CTRL(0xff);
    while (1);
}
