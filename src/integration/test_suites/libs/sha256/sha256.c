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
#include "printf.h"
#include "sha256.h"
#include "caliptra_isr.h"

extern volatile caliptra_intr_received_s cptra_intr_rcv;

void wait_for_sha256_intr(){
    printf("SHA256 flow in progress...\n");
    while((cptra_intr_rcv.sha256_error == 0) & (cptra_intr_rcv.sha256_notif == 0)){
        __asm__ volatile ("wfi"); // "Wait for interrupt"
        // Sleep during SHA256 operation to allow ISR to execute and show idle time in sims
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    };
    //printf("Received SHA256 error intr with status = %d\n", cptra_intr_rcv.sha256_error);
    printf("Received SHA256 notif intr with status = %d\n", cptra_intr_rcv.sha256_notif);
}

void sha256_zeroize(){
    printf("SHA256 zeroize flow.\n");
    lsu_write_32(CLP_SHA256_REG_SHA256_CTRL, (1 << SHA256_REG_SHA256_CTRL_ZEROIZE_LOW) & SHA256_REG_SHA256_CTRL_ZEROIZE_MASK);
}

void sha256_flow(sha256_io block, uint8_t mode, sha256_io digest){
    volatile uint32_t * reg_ptr;
    uint8_t offset;
    uint8_t fail_cmd = 0x1;
    uint32_t sha256_digest [8];

    // wait for SHA to be ready
    while((lsu_read_32(CLP_SHA256_REG_SHA256_STATUS) & SHA256_REG_SHA256_STATUS_READY_MASK) == 0);

    // Write SHA256 block
    reg_ptr = (uint32_t*) CLP_SHA256_REG_SHA256_BLOCK_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_SHA256_REG_SHA256_BLOCK_15) {
        *reg_ptr++ = block.data[offset++];
    }

    // Enable SHA256 core 
    VPRINTF(LOW, "Enable SHA256\n");
    lsu_write_32(CLP_SHA256_REG_SHA256_CTRL, SHA256_REG_SHA256_CTRL_INIT_MASK | 
                                            (mode << SHA256_REG_SHA256_CTRL_MODE_LOW) & SHA256_REG_SHA256_CTRL_MODE_MASK);
    
    // wait for SHA to be valid
    wait_for_sha256_intr();

    reg_ptr = (uint32_t *) CLP_SHA256_REG_SHA256_DIGEST_0;
    printf("Load DIGEST data from SHA256\n");
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_SHA256_REG_SHA256_DIGEST_7) {
        sha256_digest[offset] = *reg_ptr;
        if (sha256_digest[offset] != digest.data[offset]) {
            printf("At offset [%d], sha_digest data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", sha256_digest[offset]);
            printf("Expected data: 0x%x\n", digest.data[offset]);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

}
