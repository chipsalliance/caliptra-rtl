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
#include <string.h>
#include <stdint.h>
#include "printf.h"

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
volatile uint32_t hmac_intr_status = 0;

void main() {
    volatile uint32_t* hmac_key         = (uint32_t*) CLP_HMAC_REG_HMAC384_KEY_0;
    volatile uint32_t* hmac_block       = (uint32_t*) CLP_HMAC_REG_HMAC384_BLOCK_0;
    volatile uint32_t* hmac_tag         = (uint32_t*) CLP_HMAC_REG_HMAC384_TAG_0;
    volatile uint32_t* hmac_lfsr_seed   = (uint32_t*) CLP_HMAC_REG_HMAC384_LFSR_SEED_0;
    volatile uint32_t* hmac_reg;

    //this is the key 384-bit
    uint32_t key_data[] = {0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b,
                           0x0b0b0b0b};
    uint32_t block_data[] = {0x48692054,
                             0x68657265,
                             0x80000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000000,
                             0x00000440};
    uint32_t expected_data[] = {0xb6a8d563,
                                0x6f5c6a72,
                                0x24f9977d,
                                0xcf7ee6c7,
                                0xfb6d0c48,
                                0xcbdee973,
                                0x7a959796,
                                0x489bddbc,
                                0x4c5df61d,
                                0x5b3297b4,
                                0xfb68dab9,
                                0xf1b582c2};
    //this is a random lfsr_seed 160-bit
    uint32_t lfsr_seed_data[] = {0xC8F518D4,
                                 0xF3AA1BD4,
                                 0x6ED56C1C,
                                 0x3C9E16FB,
                                 0x800AF504};                               
    uint8_t offset;


    // Entry message
    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " HMAC smoke test !!\n"               );
    VPRINTF(LOW, "----------------------------------\n");

    // Call interrupt init
    init_interrupts();

    // Load key from hw_data and write to HMAC core
    VPRINTF(LOW, "Load Key data to HMAC\n");
    offset = 0;
    while (hmac_key <= (uint32_t*) CLP_HMAC_REG_HMAC384_KEY_11) {
        *hmac_key++ = key_data[offset++];
    }

    // Load lfsr_seed from hw_data and write to HMAC core
    VPRINTF(LOW, "Load LFSR_seed data to HMAC\n");
    offset = 0;
    while (hmac_lfsr_seed <= (uint32_t*) CLP_HMAC_REG_HMAC384_LFSR_SEED_4) {
        *hmac_lfsr_seed++ = lfsr_seed_data[offset++];
    }

    // Load block from hw_data and write to HMAC core
    VPRINTF(LOW, "Load Block data to HMAC\n");
    offset = 0;
    while (hmac_block <= (uint32_t*) CLP_HMAC_REG_HMAC384_BLOCK_31) {
        *hmac_block++ = block_data[offset++];
    }

    // Enable HMAC core
    VPRINTF(LOW, "Initiate HMAC operation\n");
    hmac_reg = (uint32_t *) CLP_HMAC_REG_HMAC384_CTRL;
    *hmac_reg = HMAC_INIT;

    // wait for HMAC process (poll interrupt flag)
    while(hmac_intr_status != HMAC_VALID) {
        __asm__ volatile ("wfi"); // "Wait for interrupt"
        // Sleep during HMAC operation to allow ISR to execute and show idle time in sims
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    };
    VPRINTF(LOW, "Received HMAC intr with status = %x\n", hmac_intr_status);
    hmac_intr_status = 0;

    // Read the data back from HMAC register
    VPRINTF(LOW, "Load Result data from HMAC\n");
    offset = 0;
    while (hmac_tag <= (uint32_t*) CLP_HMAC_REG_HMAC384_TAG_11) {
        if (*hmac_tag != expected_data[offset]) {
            VPRINTF(ERROR, "At offset [%d], data mismatch!\n", offset);
            VPRINTF(ERROR, "Actual   data: 0x%x\n", *hmac_tag);
            VPRINTF(ERROR, "Expected data: 0x%x\n", expected_data[offset]);
            SEND_STDOUT_CTRL( 0x1);
            while(1);
        } else {
            VPRINTF(ALL, "[%d] :: 0x%x matches 0x%x\n", offset, *hmac_tag, expected_data[offset]);
        }
        hmac_tag++;
        offset++;
    }

    // Write 0xff to STDOUT for TB to terminate test.
    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
