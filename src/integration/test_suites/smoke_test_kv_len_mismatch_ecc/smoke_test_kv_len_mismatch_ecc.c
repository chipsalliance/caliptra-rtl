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
// KV length-mismatch — ECC privkey/seed path (single-shot randomized).
// Round-6 rewrite. Each invocation exercises exactly ONE KV read.
//
// ECC consumer expected sizes:
//   privkey → 11 (12 dwords)
//   seed    → 11 (12 dwords)
// dest_valid bits: bit3=ECC_PKEY, bit4=ECC_SEED
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

#define DV_ECC_PKEY 0x08u
#define DV_ECC_SEED 0x10u

enum { ECC_PRIVKEY = 0, ECC_SEED = 1 };

static const char* consumer_name(int c) {
    return (c == ECC_PRIVKEY) ? "ECC_PRIVKEY" : "ECC_SEED";
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
    VPRINTF(LOW, " KV length-mismatch — ECC (single-shot random)\n");
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

    int consumer = rand() & 0x1;
    uint32_t rd_ctrl, rd_status;
    uint8_t  dv;
    uint8_t  expected = 11;
    if (consumer == ECC_PRIVKEY) {
        rd_ctrl   = CLP_ECC_REG_ECC_KV_RD_PKEY_CTRL;
        rd_status = CLP_ECC_REG_ECC_KV_RD_PKEY_STATUS;
        dv        = DV_ECC_PKEY;
    } else {
        rd_ctrl   = CLP_ECC_REG_ECC_KV_RD_SEED_CTRL;
        rd_status = CLP_ECC_REG_ECC_KV_RD_SEED_STATUS;
        dv        = DV_ECC_SEED;
    }

    int expect_mismatch = (last_dword < expected);

    VPRINTF(LOW,
        "PARAMS: consumer=%s slot=%u last_dword=%u expected=%u expect_mismatch=%d\n",
        consumer_name(consumer), slot, last_dword, expected, expect_mismatch);

    kv_inject(slot, last_dword, dv);
    uint32_t st  = kv_read_and_wait(rd_ctrl, rd_status, slot);
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

    lsu_write_32(rd_ctrl, 0);

    SEND_STDOUT_CTRL(0xff);
    while (1);
}
