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
// The key vault has 24 entries, but its entry fields are 5 bits wide. For
// entries 24 to 31, check that
//   - an HMAC key read (unpadded client) reports KV_READ_FAIL,
//   - an HMAC block read (padded client) completes and reports KV_READ_FAIL,
//   - an HMAC tag write to the key vault reports KV_WRITE_FAIL.
// Every poll is bounded, so a read that never completes fails the test.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include "printf.h"

volatile char*    stdout     = (char *)STDOUT;
volatile uint32_t intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define KV_READ_FAIL  0x1u
#define KV_WRITE_FAIL 0x2u
#define POLL_LIMIT    20000

static void fail_test(const char* msg, uint32_t entry, uint32_t status) {
    VPRINTF(FATAL, "TEST FAIL: entry %d: %s (status 0x%x)\n", entry, msg, status);
    SEND_STDOUT_CTRL(0x1);
    while (1);
}

// Poll a key vault status register until VALID is set, or fail.
static uint32_t wait_valid(uint32_t status_addr, const char* what, uint32_t entry) {
    uint32_t status = 0;
    for (int i = 0; i < POLL_LIMIT; i++) {
        status = lsu_read_32(status_addr);
        if (status & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK) {
            return status;
        }
    }
    fail_test(what, entry, status);
    return status;
}

static uint32_t error_code(uint32_t status) {
    return (status & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_MASK) >> HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_LOW;
}

static void hmac_zeroize_and_wait(uint32_t entry) {
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_ZEROIZE_MASK);
    for (int i = 0; i < POLL_LIMIT; i++) {
        if (lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) {
            return;
        }
    }
    fail_test("HMAC not ready after zeroize", entry, lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS));
}

static void check_key_read(uint32_t entry) {
    uint32_t status;
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                 ((entry << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));
    status = wait_valid(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS, "HMAC key read did not complete", entry);
    if (error_code(status) != KV_READ_FAIL) {
        fail_test("HMAC key read did not report KV_READ_FAIL", entry, status);
    }
    hmac_zeroize_and_wait(entry);
}

static void check_block_read(uint32_t entry) {
    uint32_t status;
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL, HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_EN_MASK |
                 ((entry << HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_MASK));
    status = wait_valid(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS, "HMAC block read did not complete", entry);
    if (error_code(status) != KV_READ_FAIL) {
        fail_test("HMAC block read did not report KV_READ_FAIL", entry, status);
    }
    hmac_zeroize_and_wait(entry);
}

static void check_tag_write(uint32_t entry) {
    volatile uint32_t* reg_ptr;
    uint32_t status;

    // Firmware key, block, and LFSR seed. The values do not matter, but the
    // key must not be zero.
    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_0;
    for (int i = 0; reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_15; i++) {
        *reg_ptr++ = 0x0b0b0b0b + i;
    }
    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC512_BLOCK_0;
    for (int i = 0; reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_BLOCK_31; i++) {
        *reg_ptr++ = (i == 0) ? 0x80000000 : (i == 31) ? 0x00000400 : 0;
    }
    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC512_LFSR_SEED_0;
    for (int i = 0; reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_LFSR_SEED_5; i++) {
        *reg_ptr++ = 0xc8f518d4 + i;
    }

    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL, HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
                 HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK |
                 ((entry << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) & HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK));
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK | HMAC_REG_HMAC512_CTRL_LAST_MASK |
                 (1 << HMAC_REG_HMAC512_CTRL_MODE_LOW));

    status = wait_valid(CLP_HMAC_REG_HMAC512_KV_WR_STATUS, "HMAC tag write did not complete", entry);
    if (error_code(status) != KV_WRITE_FAIL) {
        fail_test("HMAC tag write did not report KV_WRITE_FAIL", entry, status);
    }
    hmac_zeroize_and_wait(entry);
}

void main() {
    const uint32_t entries[] = {24, 27, 31};

    VPRINTF(LOW, "----------------------------------------------\n");
    VPRINTF(LOW, " Key vault entries 24 to 31 report an error\n");
    VPRINTF(LOW, "----------------------------------------------\n");

    for (int i = 0; i < sizeof(entries) / sizeof(entries[0]); i++) {
        VPRINTF(LOW, "Entry %d: key read, block read, and tag write\n", entries[i]);
        check_key_read(entries[i]);
        check_block_read(entries[i]);
        check_tag_write(entries[i]);
    }

    VPRINTF(LOW, "All out-of-range accesses reported an error\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
