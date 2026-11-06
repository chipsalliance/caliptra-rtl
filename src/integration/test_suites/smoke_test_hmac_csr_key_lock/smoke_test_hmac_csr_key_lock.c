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
// Verifies INTERNAL_CSR_HMAC_KEY_LOCK in MANUF state:
//   Boot 1: lock clear -> CSR mode uses the CSR HMAC key. Set the lock; FW
//           cannot clear it; CSR mode uses an all-zero key. Issue FW update reset.
//   Boot 2: FW update (hitless) reset keeps the lock -> zero key. Issue warm reset.
//   Boot 3: warm reset clears the lock -> CSR mode uses the CSR HMAC key again.

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
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// "Hi There" padded for HMAC512 (same vector as smoke_test_hmac)
uint32_t block_data[32] = {0x48692054, 0x68657265, 0x80000000, 0x00000000,
                           0x00000000, 0x00000000, 0x00000000, 0x00000000,
                           0x00000000, 0x00000000, 0x00000000, 0x00000000,
                           0x00000000, 0x00000000, 0x00000000, 0x00000000,
                           0x00000000, 0x00000000, 0x00000000, 0x00000000,
                           0x00000000, 0x00000000, 0x00000000, 0x00000000,
                           0x00000000, 0x00000000, 0x00000000, 0x00000000,
                           0x00000000, 0x00000000, 0x00000000, 0x00000440};

// HMAC512 tag with the TB CSR HMAC key (16 x 0x0b0b0b0b)
uint32_t exp_tag_csr_key[16] = {0x637edc6e, 0x01dce7e6, 0x742a9945, 0x1aae82df,
                                0x23da3e92, 0x439e590e, 0x43e761b3, 0x3e910fb8,
                                0xac2878eb, 0xd5803f6f, 0x0b61dbce, 0x5e251ff8,
                                0x789a4722, 0xc1be65ae, 0xa45fd464, 0xe89f8f5b};

// HMAC512 tag with an all-zero key
uint32_t exp_tag_zero_key[16] = {0xf7688a10, 0x4326d36c, 0x1940f6d2, 0x8d746c06,
                                 0x61d383e0, 0xd14fe8a0, 0x46494447, 0x77610f5d,
                                 0xd9565a36, 0x846ab9e9, 0xe734cf38, 0x0d3a070d,
                                 0x8ef021b5, 0xf3a50c48, 0x1710a464, 0x968e3419};

uint32_t lfsr_seed_data[12] = {0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C, 0x3C9E16FB,
                               0x800AF504, 0xC8F518D4, 0xF3AA1BD4, 0x6ED56C1C,
                               0x3C9E16FB, 0x800AF504, 0xC8F518D4, 0xF3AA1BD4};

void check_csr_key_lock(uint32_t exp_lock) {
    uint32_t lock = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_CSR_HMAC_KEY_LOCK) &
                    SOC_IFC_REG_INTERNAL_CSR_HMAC_KEY_LOCK_LOCK_MASK;
    if (lock != exp_lock) {
        VPRINTF(ERROR, "ERROR: INTERNAL_CSR_HMAC_KEY_LOCK = %d, expected %d\n", lock, exp_lock);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}

// Run a CSR-mode HMAC512 and compare against exp_tag (fails the test on mismatch)
void run_csr_hmac(uint32_t * exp_tag) {
    hmac_io hmac512_key;
    hmac_io hmac_block;
    hmac_io hmac_lfsr_seed;
    hmac_io hmac512_tag;

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
    for (int i = 0; i < HMAC512_TAG_SIZE; i++)
        hmac512_tag.data[i] = exp_tag[i];

    // ISR accumulates the notif flag; clear it so wait_for_hmac_intr() waits for this op
    cptra_intr_rcv.hmac_notif = 0;
    cptra_intr_rcv.hmac_error = 0;
    hmac512_flow_csr(hmac512_key, hmac_block, hmac_lfsr_seed, hmac512_tag, TRUE, TRUE);
    hmac_zeroize();
}

void main() {

    SEND_STDOUT_CTRL(0x7F); // Switch to MANUF device lifecycle state

    rst_count++;

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC CSR key lock smoke test !!\n"  );
    VPRINTF(LOW, " Boot %d\n", rst_count             );
    VPRINTF(LOW, "----------------------------------\n");

    init_interrupts();

    if (rst_count == 1) {
        VPRINTF(LOW, "CSR mode before lock: expect CSR key tag\n");
        check_csr_key_lock(0);
        run_csr_hmac(exp_tag_csr_key);

        VPRINTF(LOW, "Set INTERNAL_CSR_HMAC_KEY_LOCK\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_CSR_HMAC_KEY_LOCK, SOC_IFC_REG_INTERNAL_CSR_HMAC_KEY_LOCK_LOCK_MASK);
        check_csr_key_lock(1);
        VPRINTF(LOW, "Attempt to clear INTERNAL_CSR_HMAC_KEY_LOCK\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_CSR_HMAC_KEY_LOCK, 0x0);
        check_csr_key_lock(1);

        VPRINTF(LOW, "CSR mode after lock: expect zero key tag\n");
        run_csr_hmac(exp_tag_zero_key);

        VPRINTF(LOW, "Issue FW update reset\n");
        lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET, SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK);
        while(1);
    }
    else if (rst_count == 2) {
        VPRINTF(LOW, "After FW update reset: lock must stay set, expect zero key tag\n");
        check_csr_key_lock(1);
        run_csr_hmac(exp_tag_zero_key);

        VPRINTF(LOW, "Issue warm reset\n");
        SEND_STDOUT_CTRL(0xf6);
        while(1);
    }
    else if (rst_count == 3) {
        VPRINTF(LOW, "After warm reset: lock must be clear, expect CSR key tag\n");
        check_csr_key_lock(0);
        run_csr_hmac(exp_tag_csr_key);
    }
    else {
        VPRINTF(ERROR, "ERROR: unexpected boot count %d\n", rst_count);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }

    // Write 0xff to STDOUT for TB to terminate test.
    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
