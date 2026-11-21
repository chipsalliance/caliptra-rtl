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
// The key vault has 24 entries, but its entry fields are 5 bits wide. The test
//   1. writes a sentinel to entries 0 to 22: an HMAC-384 tag that only the AES
//      key client may read,
//   2. checks that entry 23, the last entry, accepts an HMAC-512 tag write for
//      the HMAC key, HMAC block, and AES key clients, and that an HMAC key read
//      (used by an HMAC-512 operation) and an HMAC block read of it succeed,
//   3. records the KEY_CTRL of entries 0 to 23 and a fingerprint of each
//      entry's contents (the AES-256 encryption of a zero block, with the entry
//      as the key), and checks that the fingerprints differ,
//   4. checks that for entries 24 to 31 an HMAC key read and an HMAC block read
//      report KV_READ_FAIL, and an HMAC-512 tag write for the HMAC key client
//      reports KV_WRITE_FAIL,
//   5. checks that the KEY_CTRL and fingerprint of entries 0 to 23 are
//      unchanged.
// The rejected tag writes differ from every entry in contents and destinations,
// and from the sentinels in length, so a rejected write that still reached an
// entry changes its fingerprint or KEY_CTRL. Every poll is bounded, so a read
// that never completes fails the test.

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

#define KV_ENTRIES      24
#define KV_ENTRY_VALUES 32  // values of the 5-bit entry fields
#define KV_SUCCESS      0x0u
#define KV_READ_FAIL    0x1u
#define KV_WRITE_FAIL   0x2u
#define POLL_LIMIT      20000

// The HMAC and AES key vault status registers share one layout.
#define KV_STATUS_VALID HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK

#define SENTINEL_DEST   HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK
#define BOUNDARY_DEST   (HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK | \
                         HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK | \
                         HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK)
#define REJECTED_DEST   HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK

static void fail_test(const char* msg, uint32_t entry, uint32_t value) {
    VPRINTF(FATAL, "TEST FAIL: entry %d: %s (0x%x)\n", entry, msg, value);
    SEND_STDOUT_CTRL(0x1);
    while (1);
}

// Poll a register until one of the bits in mask is set, or fail.
static uint32_t wait_set(uint32_t addr, uint32_t mask, const char* what, uint32_t entry) {
    uint32_t value = 0;
    for (int i = 0; i < POLL_LIMIT; i++) {
        value = lsu_read_32(addr);
        if (value & mask) {
            return value;
        }
    }
    fail_test(what, entry, value);
    return value;
}

static uint32_t error_code(uint32_t status) {
    return (status & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_MASK) >> HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_LOW;
}

static void expect_error(uint32_t status, uint32_t expected, const char* msg, uint32_t entry) {
    if (error_code(status) != expected) {
        fail_test(msg, entry, status);
    }
}

static uint32_t read_key_ctrl(uint32_t entry) {
    return lsu_read_32(CLP_KV_REG_KEY_CTRL_0 + 4 * entry);
}

// KEY_CTRL after a write for the KV_WR_CTRL destinations dest that ends at
// last_dword. KV_WR_CTRL and KEY_CTRL list the destinations in the same order.
static void expect_key_ctrl(uint32_t entry, uint32_t dest, uint32_t last_dword) {
    uint32_t expected = (((dest >> HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_LOW) << KV_REG_KEY_CTRL_0_DEST_VALID_LOW) &
                         KV_REG_KEY_CTRL_0_DEST_VALID_MASK) |
                        ((last_dword << KV_REG_KEY_CTRL_0_LAST_DWORD_LOW) & KV_REG_KEY_CTRL_0_LAST_DWORD_MASK);
    uint32_t ctrl = read_key_ctrl(entry);
    if (ctrl != expected) {
        fail_test("unexpected KEY_CTRL", entry, ctrl);
    }
}

static void hmac_zeroize_and_wait(uint32_t entry) {
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_ZEROIZE_MASK);
    wait_set(CLP_HMAC_REG_HMAC512_STATUS, HMAC_REG_HMAC512_STATUS_READY_MASK, "HMAC not ready after zeroize", entry);
}

// Load a nonzero firmware key: 12 dwords for HMAC-384, 16 for HMAC-512.
static void hmac_load_key(uint32_t mode, uint32_t seed) {
    uint32_t dwords = (mode == HMAC512_MODE) ? 16 : 12;
    for (uint32_t i = 0; i < dwords; i++) {
        lsu_write_32(CLP_HMAC_REG_HMAC512_KEY_0 + 4 * i, seed + i);
    }
}

// Load a padded empty message and the LFSR seed, and start a one-block HMAC.
static void hmac_start(uint32_t mode) {
    for (uint32_t i = 0; i < 32; i++) {
        lsu_write_32(CLP_HMAC_REG_HMAC512_BLOCK_0 + 4 * i, (i == 0) ? 0x80000000 : (i == 31) ? 0x00000400 : 0);
    }
    for (uint32_t i = 0; i < 6; i++) {
        lsu_write_32(CLP_HMAC_REG_HMAC512_LFSR_SEED_0 + 4 * i, 0xc8f518d4 + i);
    }
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK | HMAC_REG_HMAC512_CTRL_LAST_MASK |
                 (mode << HMAC_REG_HMAC512_CTRL_MODE_LOW));
}

// Write the tag of an HMAC with a firmware key to a key vault entry, and return
// KV_WR_STATUS.
static uint32_t hmac_tag_to_kv(uint32_t entry, uint32_t mode, uint32_t key_seed, uint32_t dest) {
    uint32_t status;
    hmac_load_key(mode, key_seed);
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL, HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK | dest |
                 ((entry << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) & HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK));
    hmac_start(mode);
    status = wait_set(CLP_HMAC_REG_HMAC512_KV_WR_STATUS, KV_STATUS_VALID, "HMAC tag write did not complete", entry);
    hmac_zeroize_and_wait(entry);
    return status;
}

static uint32_t hmac_key_read(uint32_t entry) {
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                 ((entry << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));
    return wait_set(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS, KV_STATUS_VALID, "HMAC key read did not complete", entry);
}

static uint32_t hmac_block_read(uint32_t entry) {
    lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL, HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_EN_MASK |
                 ((entry << HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_MASK));
    return wait_set(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS, KV_STATUS_VALID, "HMAC block read did not complete", entry);
}

// Encrypt a zero block with AES-256-ECB, using the first eight dwords of a key
// vault entry as the key.
static void aes_fingerprint(uint32_t entry, uint32_t fp[4]) {
    uint32_t status;
    uint32_t ctrl = (1u << AES_REG_CTRL_SHADOWED_OPERATION_LOW) |  // encrypt
                    (1u << AES_REG_CTRL_SHADOWED_MODE_LOW) |       // ECB
                    (4u << AES_REG_CTRL_SHADOWED_KEY_LEN_LOW) |    // 256-bit key
                    AES_REG_CTRL_SHADOWED_SIDELOAD_MASK;           // key from the key vault

    wait_set(CLP_AES_REG_STATUS, AES_REG_STATUS_IDLE_MASK, "AES not idle", entry);
    wait_set(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS, AES_CLP_REG_AES_KV_RD_KEY_STATUS_READY_MASK,
             "AES key read not ready", entry);
    lsu_write_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL, AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_EN_MASK |
                 ((entry << AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_MASK));
    status = wait_set(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS, KV_STATUS_VALID, "AES key read did not complete", entry);
    expect_error(status, KV_SUCCESS, "AES key read failed", entry);

    // The control register is shadowed, so it is written twice.
    lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, ctrl);
    lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, ctrl);
    wait_set(CLP_AES_REG_STATUS, AES_REG_STATUS_INPUT_READY_MASK, "AES input not ready", entry);
    for (uint32_t i = 0; i < 4; i++) {
        lsu_write_32(CLP_AES_REG_DATA_IN_0 + 4 * i, 0);
    }
    wait_set(CLP_AES_REG_STATUS, AES_REG_STATUS_OUTPUT_VALID_MASK, "AES output not valid", entry);
    for (uint32_t i = 0; i < 4; i++) {
        fp[i] = lsu_read_32(CLP_AES_REG_DATA_OUT_0 + 4 * i);
    }
    expect_error(lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS), KV_SUCCESS, "AES key use failed", entry);
}

static int same_fingerprint(const uint32_t a[4], const uint32_t b[4]) {
    return (a[0] == b[0]) && (a[1] == b[1]) && (a[2] == b[2]) && (a[3] == b[3]);
}

static void check_boundary_entry(uint32_t entry) {
    uint32_t status;

    status = hmac_tag_to_kv(entry, HMAC512_MODE, 0x17171700, BOUNDARY_DEST);
    expect_error(status, KV_SUCCESS, "HMAC tag write failed", entry);
    expect_key_ctrl(entry, BOUNDARY_DEST, 15);

    // The key length is checked when the operation starts, so use the key.
    status = hmac_key_read(entry);
    expect_error(status, KV_SUCCESS, "HMAC key read failed", entry);
    hmac_start(HMAC512_MODE);
    wait_set(CLP_HMAC_REG_HMAC512_STATUS, HMAC_REG_HMAC512_STATUS_VALID_MASK,
             "HMAC with the key vault key did not complete", entry);
    expect_error(lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS), KV_SUCCESS, "HMAC key use failed", entry);
    hmac_zeroize_and_wait(entry);

    status = hmac_block_read(entry);
    expect_error(status, KV_SUCCESS, "HMAC block read failed", entry);
    hmac_zeroize_and_wait(entry);
}

static void check_rejected_entry(uint32_t entry) {
    uint32_t status;

    status = hmac_key_read(entry);
    expect_error(status, KV_READ_FAIL, "HMAC key read did not report KV_READ_FAIL", entry);
    hmac_zeroize_and_wait(entry);

    status = hmac_block_read(entry);
    expect_error(status, KV_READ_FAIL, "HMAC block read did not report KV_READ_FAIL", entry);
    hmac_zeroize_and_wait(entry);

    status = hmac_tag_to_kv(entry, HMAC512_MODE, 0x0b0b0b0b, REJECTED_DEST);
    expect_error(status, KV_WRITE_FAIL, "HMAC tag write did not report KV_WRITE_FAIL", entry);
}

void main() {
    static uint32_t key_ctrl[KV_ENTRIES];
    static uint32_t fingerprint[KV_ENTRIES][4];
    uint32_t fp[4];
    uint32_t entry;
    uint32_t value;

    VPRINTF(LOW, "----------------------------------------------\n");
    VPRINTF(LOW, " Key vault entries 24 to 31 report an error\n");
    VPRINTF(LOW, "----------------------------------------------\n");

    VPRINTF(LOW, "Entries 0 to 22: write sentinels\n");
    for (entry = 0; entry < KV_ENTRIES - 1; entry++) {
        value = hmac_tag_to_kv(entry, HMAC384_MODE, 0x5e000000 | (entry << 8), SENTINEL_DEST);
        expect_error(value, KV_SUCCESS, "sentinel write failed", entry);
        expect_key_ctrl(entry, SENTINEL_DEST, 11);
    }

    VPRINTF(LOW, "Entry 23: tag write, key read, and block read\n");
    check_boundary_entry(KV_ENTRIES - 1);

    VPRINTF(LOW, "Entries 0 to 23: record KEY_CTRL and fingerprints\n");
    for (entry = 0; entry < KV_ENTRIES; entry++) {
        key_ctrl[entry] = read_key_ctrl(entry);
        aes_fingerprint(entry, fingerprint[entry]);
        for (uint32_t other = 0; other < entry; other++) {
            if (same_fingerprint(fingerprint[entry], fingerprint[other])) {
                fail_test("fingerprint matches that of another entry", entry, other);
            }
        }
    }

    for (entry = KV_ENTRIES; entry < KV_ENTRY_VALUES; entry++) {
        VPRINTF(LOW, "Entry %d: key read, block read, and tag write\n", entry);
        check_rejected_entry(entry);
    }

    VPRINTF(LOW, "Entries 0 to 23: compare KEY_CTRL and fingerprints\n");
    for (entry = 0; entry < KV_ENTRIES; entry++) {
        value = read_key_ctrl(entry);
        if (value != key_ctrl[entry]) {
            fail_test("KEY_CTRL changed", entry, value);
        }
        aes_fingerprint(entry, fp);
        if (!same_fingerprint(fp, fingerprint[entry])) {
            fail_test("contents changed", entry, fp[0]);
        }
    }

    VPRINTF(LOW, "Out-of-range accesses reported errors and changed no entry\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
