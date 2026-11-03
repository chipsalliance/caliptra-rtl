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
// smoke_test_hmac_csr_key_lock.c
// Verifies INTERNAL_CSR_HMAC_KEY_LOCK: in MANUF state, HMAC512 CSR mode uses
// the CSR HMAC key until the lock is set. After the lock is set, the lock
// cannot be cleared by FW and CSR mode uses an all-zero key.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "hmac.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count       = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void check_csr_key_lock(uint32_t exp_lock) {
    uint32_t lock = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_CSR_HMAC_KEY_LOCK) &
                    SOC_IFC_REG_INTERNAL_CSR_HMAC_KEY_LOCK_LOCK_MASK;
    if (lock != exp_lock) {
        VPRINTF(ERROR, "ERROR: INTERNAL_CSR_HMAC_KEY_LOCK = %d, expected %d\n", lock, exp_lock);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

void main() {

    // "Hi There" padded for HMAC512 (same vector as smoke_test_hmac)
    uint32_t block_data[] = {0x48692054, 0x68657265, 0x80000000, 0x00000000,
                             0x00000000, 0x00000000, 0x00000000, 0x00000000,
                             0x00000000, 0x00000000, 0x00000000, 0x00000000,
                             0x00000000, 0x00000000, 0x00000000, 0x00000000,
                             0x00000000, 0x00000000, 0x00000000, 0x00000000,
                             0x00000000, 0x00000000, 0x00000000, 0x00000000,
                             0x00000000, 0x00000000, 0x00000000, 0x00000000,
                             0x00000000, 0x00000000, 0x00000000, 0x00000440};

    // HMAC512 tag with the TB CSR HMAC key (16 x 0x0b0b0b0b)
    uint32_t exp_tag_csr_key[] = {0x637edc6e, 0x01dce7e6, 0x742a9945, 0x1aae82df,
                                  0x23da3e92, 0x439e590e, 0x43e761b3, 0x3e910fb8,
                                  0xac2878eb, 0xd5803f6f, 0x0b61dbce, 0x5e251ff8,
                                  0x789a4722, 0xc1be65ae, 0xa45fd464, 0xe89f8f5b};

    // HMAC512 tag with an all-zero key
    uint32_t exp_tag_zero_key[] = {0xf7688a10, 0x4326d36c, 0x1940f6d2, 0x8d746c06,
                                   0x61d383e0, 0xd14fe8a0, 0x46494447, 0x77610f5d,
                                   0xd9565a36, 0x846ab9e9, 0xe734cf38, 0x0d3a070d,
                                   0x8ef021b5, 0xf3a50c48, 0x1710a464, 0x968e3419};

    uint32_t lfsr_seed_data[12] = {0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C, 0x3C9E16FB,
                                   0x800AF504, 0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C,
                                   0x3C9E16FB, 0x800AF504, 0xC8F518D4, 0xF3AA1BD4};

    hmac_io hmac512_key;
    hmac_io hmac_block;
    hmac_io hmac_lfsr_seed;
    hmac_io hmac512_tag;

    SEND_STDOUT_CTRL(0x7F); // Switch to MANUF device lifecycle state

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC CSR key lock smoke test !!\n"  );
    VPRINTF(LOW, "----------------------------------\n");

    init_interrupts();

    // Key registers are ignored in CSR mode
    hmac512_key.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_KEY_SIZE; i++)
        hmac512_key.data[i] = 0x12345678;

    hmac_block.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_BLOCK_SIZE; i++)
        hmac_block.data[i] = block_data[i];

    hmac_lfsr_seed.kv_intf = FALSE;
    for (int i = 0; i < HMAC512_LFSR_SEED_SIZE; i++)
        hmac_lfsr_seed.data[i] = lfsr_seed_data[i];

    hmac512_tag.kv_intf = FALSE;

    // 1. Lock clear: CSR mode uses the CSR HMAC key
    VPRINTF(LOW, "CSR mode before lock: expect CSR key tag\n");
    check_csr_key_lock(0);
    for (int i = 0; i < HMAC512_TAG_SIZE; i++)
        hmac512_tag.data[i] = exp_tag_csr_key[i];
    hmac512_flow_csr(hmac512_key, hmac_block, hmac_lfsr_seed, hmac512_tag, TRUE, TRUE);
    hmac_zeroize();

    // 2. Set the lock; FW cannot clear it
    VPRINTF(LOW, "Set INTERNAL_CSR_HMAC_KEY_LOCK\n");
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_CSR_HMAC_KEY_LOCK, SOC_IFC_REG_INTERNAL_CSR_HMAC_KEY_LOCK_LOCK_MASK);
    check_csr_key_lock(1);
    VPRINTF(LOW, "Attempt to clear INTERNAL_CSR_HMAC_KEY_LOCK\n");
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_CSR_HMAC_KEY_LOCK, 0x0);
    check_csr_key_lock(1);

    // 3. Lock set: CSR mode uses an all-zero key
    VPRINTF(LOW, "CSR mode after lock: expect zero key tag\n");
    for (int i = 0; i < HMAC512_TAG_SIZE; i++)
        hmac512_tag.data[i] = exp_tag_zero_key[i];
    hmac512_flow_csr(hmac512_key, hmac_block, hmac_lfsr_seed, hmac512_tag, TRUE, TRUE);
    hmac_zeroize();

    // Write 0xff to STDOUT for TB to terminate test.
    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
