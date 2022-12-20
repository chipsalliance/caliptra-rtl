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

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
volatile uint32_t hmac_intr_status = 0;

void main() {
    uint32_t* hmac_key   = (uint32_t*) CLP_HMAC_REG_HMAC384_KEY_0;
    uint32_t* hmac_block = (uint32_t*) CLP_HMAC_REG_HMAC384_BLOCK_0;
    uint32_t* hmac_tag   = (uint32_t*) CLP_HMAC_REG_HMAC384_TAG_0;
    uint32_t* hmac_reg;

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
    uint8_t offset;


    // Entry message
    printf("----------------------------------\n");
    printf(" HMAC smoke test !!\n"               );
    printf("----------------------------------\n");

    // Call interrupt init
    init_interrupts();

    // Load key from hw_data and write to HMAC core
    printf("Load Key data to HMAC\n");
    offset = 0;
    while (hmac_key <= (uint32_t*) CLP_HMAC_REG_HMAC384_KEY_11) {
        *hmac_key++ = key_data[offset++];
    }

    // Load block from hw_data and write to HMAC core
    printf("Load Block data to HMAC\n");
    offset = 0;
    while (hmac_block <= (uint32_t*) CLP_HMAC_REG_HMAC384_BLOCK_31) {
        *hmac_block++ = block_data[offset++];
    }

    // Enable HMAC core
    printf("Initiate HMAC operation\n");
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
    printf("Received HMAC intr with status = %x\n", hmac_intr_status);
    hmac_intr_status = 0;

    // Read the data back from HMAC register
    printf("Load Result data from HMAC\n");
    offset = 0;
    while (hmac_tag <= (uint32_t*) CLP_HMAC_REG_HMAC384_TAG_11) {
        if (*hmac_tag != expected_data[offset]) {
            printf("At offset [%d], data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", *hmac_tag);
            printf("Expected data: 0x%x\n", expected_data[offset]);
            printf("%c", 0x1);
            while(1);
        } else {
            printf("[%d] :: 0x%x matches 0x%x\n", offset, *hmac_tag, expected_data[offset]);
        }
        hmac_tag++;
        offset++;
    }

    // Write 0xff to STDOUT for TB to terminate test.
    printf("%c", 0xff);
    while(1);

}
