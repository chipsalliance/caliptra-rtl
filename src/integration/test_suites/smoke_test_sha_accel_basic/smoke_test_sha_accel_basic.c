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

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "printf.h"
#include "soc_ifc.h"

volatile uint32_t *stdout = (uint32_t *)STDOUT;
volatile uint32_t intr_count = 0;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif

#define POLL_LIMIT 20000u
#define RANGE_STATUS SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK

// Big-endian words for "abcdefgh", matching the library's ENDIAN_TOGGLE setting.
static const uint32_t payload[] = {0x61626364, 0x65666768};
static const uint32_t expected_sha384[] = {
    0x9000cd7c, 0xada59d1d, 0x2eb82912, 0xf7f24e5e,
    0x69cc5517, 0xf68283b0, 0x05fa27c2, 0x85b61e05,
    0xedf1ad1a, 0x8a9bded6, 0xfd29eb87, 0xd75ad806
};
static const uint32_t expected_sha512[] = {
    0xa3a8c81b, 0xc97c2560, 0x010d7389, 0xbc88aac9,
    0x74a104e0, 0xe2381220, 0xc6e084c4, 0xdccd1d2d,
    0x17d4f86d, 0xb31c2a85, 0x1dc80e66, 0x81d74733,
    0xc55dcd03, 0xdd96f606, 0x2cdda12a, 0x291ae6ce
};

static void fail_test(const char *message) {
    VPRINTF(FATAL, "SHA accelerator test failed: %s\n", message);
    SEND_STDOUT_CTRL(0x01);
    while (1);
}

static void check_digest(uint32_t sha512_mode) {
    const uint32_t *expected = sha512_mode ? expected_sha512 : expected_sha384;
    uint32_t words = sha512_mode ? 16u : 12u;

    for (uint32_t i = 0; i < words; i++) {
        uint32_t actual = lsu_read_32(CLP_SHA512_ACC_CSR_DIGEST_0 + 4u * i);
        if (actual != expected[i]) {
            VPRINTF(FATAL, "Digest[%u] actual=%08x expected=%08x\n", i, actual, expected[i]);
            fail_test("digest mismatch");
        }
    }
}

// Caller holds the SHA lock, and mailbox data is already populated.
static void hash_payload(enum sha_accel_mode_e mode, uint32_t start_addr) {
    soc_ifc_sha_accel_wr_mode(mode);
    lsu_write_32(CLP_SHA512_ACC_CSR_START_ADDRESS, start_addr);
    lsu_write_32(CLP_SHA512_ACC_CSR_DLEN, sizeof(payload));
    if (mode == SHA_STREAM_384 || mode == SHA_STREAM_512) {
        for (uint32_t i = 0; i < sizeof(payload) / sizeof(payload[0]); i++)
            lsu_write_32(CLP_SHA512_ACC_CSR_DATAIN, payload[i]);
    }
    soc_ifc_sha_accel_execute();
    soc_ifc_sha_accel_poll_status();
    check_digest(mode == SHA_STREAM_512 || mode == SHA_MBOX_512);
}

static void check_rejected_ranges(uint32_t mailbox_bytes) {
    const struct {
        uint32_t start;
        uint32_t length;
    } requests[] = {
        {0u, mailbox_bytes * 2u},
        {4u, mailbox_bytes * 2u + 4u},
        {mailbox_bytes - 4u, 8u},
        {4u, 0x80000004u},
        {0xfffffffcu, 8u}
    };

    soc_ifc_sha_accel_acquire_lock();
    soc_ifc_sha_accel_wr_mode(SHA_MBOX_384);
    for (uint32_t i = 0; i < sizeof(requests) / sizeof(requests[0]); i++) {
        uint32_t poll;
        uint32_t status = 0;

        lsu_write_32(CLP_SHA512_ACC_CSR_START_ADDRESS, requests[i].start);
        lsu_write_32(CLP_SHA512_ACC_CSR_DLEN, requests[i].length);
        soc_ifc_sha_accel_execute();
        for (poll = 0; poll < POLL_LIMIT; poll++) {
            status = lsu_read_32(CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R);
            if (status & RANGE_STATUS)
                break;
        }
        if (poll == POLL_LIMIT)
            fail_test("oversized request did not report its range status");
        if (status != RANGE_STATUS)
            fail_test("unexpected SHA status during rejection");
        if (lsu_read_32(CLP_SHA512_ACC_CSR_STATUS) & SHA512_ACC_CSR_STATUS_VALID_MASK)
            fail_test("rejected request reported a valid digest");
        if (lsu_read_32(CLP_SHA512_ACC_CSR_EXECUTE) & SHA512_ACC_CSR_EXECUTE_EXECUTE_MASK)
            fail_test("rejected request did not clear EXECUTE");
        if (!(lsu_read_32(CLP_SHA512_ACC_CSR_LOCK) & SHA512_ACC_CSR_LOCK_LOCK_MASK))
            fail_test("rejected request released the SHA lock");

        lsu_write_32(CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R, RANGE_STATUS);
        if (lsu_read_32(CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) != 0)
            fail_test("range status did not clear");
        VPRINTF(LOW, "Rejected mailbox request start=%08x dlen=%08x\n",
                requests[i].start, requests[i].length);
    }

    // Correct the request under the same lock, without resetting the accelerator.
    hash_payload(SHA_MBOX_384, mailbox_bytes - sizeof(payload));
    if (lsu_read_32(CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) != 0)
        fail_test("exact-fit retry reported a fault");
    soc_ifc_sha_accel_clr_lock();
}

void main(void) {
    uint32_t hw_config;
    uint32_t mailbox_bytes;
    uint32_t mailbox_start;

    init_interrupts();
    // Poll sticky status directly; an ISR must not clear the expected rejection.
    lsu_write_32(CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R, 0);
    lsu_write_32(CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R, RANGE_STATUS);
    soc_ifc_sha_accel_clr_lock();

    hw_config = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
    mailbox_bytes = (hw_config & SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK) ?
                    16u * 1024u : 256u * 1024u;
    mailbox_start = mailbox_bytes - sizeof(payload);
    VPRINTF(LOW, "SHA accelerator basic scenarios, mailbox=%u bytes\n", mailbox_bytes);

    if (soc_ifc_mbox_acquire_lock(POLL_LIMIT))
        fail_test("could not acquire the mailbox lock");
    // The shared SHA polling helper reads mailbox word zero to create stalls.
    soc_ifc_mbox_dir_write_single(0, 0);
    for (uint32_t i = 0; i < sizeof(payload) / sizeof(payload[0]); i++)
        soc_ifc_mbox_dir_write_single(mailbox_start + 4u * i, payload[i]);

    VPRINTF(LOW, "Streaming SHA-384\n");
    soc_ifc_sha_accel_acquire_lock();
    hash_payload(SHA_STREAM_384, 0);
    soc_ifc_sha_accel_clr_lock();

    VPRINTF(LOW, "Streaming SHA-512\n");
    soc_ifc_sha_accel_acquire_lock();
    hash_payload(SHA_STREAM_512, 0);
    soc_ifc_sha_accel_clr_lock();

    VPRINTF(LOW, "Mailbox rejection and SHA-384 exact-fit recovery\n");
    check_rejected_ranges(mailbox_bytes);

    VPRINTF(LOW, "Mailbox SHA-512 exact fit\n");
    soc_ifc_sha_accel_acquire_lock();
    hash_payload(SHA_MBOX_512, mailbox_start);
    soc_ifc_sha_accel_clr_lock();

    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
    VPRINTF(LOW, "SHA accelerator basic scenarios complete\n");
    SEND_STDOUT_CTRL(0xff);
}
