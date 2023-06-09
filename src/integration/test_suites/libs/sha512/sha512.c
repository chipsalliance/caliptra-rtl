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
#include "sha512.h"
#include "printf.h"
#include "riscv_hw_if.h"
#include "caliptra_isr.h"

extern volatile caliptra_intr_received_s cptra_intr_rcv;

void wait_for_sha512_intr(){
    printf("SHA512 flow in progress...\n");
    while((cptra_intr_rcv.sha512_error == 0) & (cptra_intr_rcv.sha512_notif == 0)){
        __asm__ volatile ("wfi"); // "Wait for interrupt"
        // Sleep during SHA512 operation to allow ISR to execute and show idle time in sims
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    };
    //printf("Received SHA512 error intr with status = %d\n", cptra_intr_rcv.sha512_error);
    printf("Received SHA512 notif intr with status = %d\n", cptra_intr_rcv.sha512_notif);
}

void sha_init(enum sha512_mode_e mode) {
    VPRINTF(MEDIUM,"SHA512: Set mode: 0x%x and init\n", mode);
    uint32_t reg;
    reg = ((1 << SHA512_REG_SHA512_CTRL_INIT_LOW) & SHA512_REG_SHA512_CTRL_INIT_MASK) |
          ((mode << SHA512_REG_SHA512_CTRL_MODE_LOW) & SHA512_REG_SHA512_CTRL_MODE_MASK);
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL,reg);
}

void sha_next(enum sha512_mode_e mode) {
    VPRINTF(MEDIUM,"SHA512: Set mode: 0x%x and next\n", mode);
    uint32_t reg;
    reg = ((1 << SHA512_REG_SHA512_CTRL_NEXT_LOW) & SHA512_REG_SHA512_CTRL_NEXT_MASK) |
          ((mode << SHA512_REG_SHA512_CTRL_MODE_LOW) & SHA512_REG_SHA512_CTRL_MODE_MASK);
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL,reg);
}

void sha_init_last(enum sha512_mode_e mode) {
    VPRINTF(MEDIUM,"SHA512: Set mode: 0x%x and init with last\n", mode);
    uint32_t reg;
    reg = ((1 << SHA512_REG_SHA512_CTRL_INIT_LOW) & SHA512_REG_SHA512_CTRL_INIT_MASK) |
          ((mode << SHA512_REG_SHA512_CTRL_MODE_LOW) & SHA512_REG_SHA512_CTRL_MODE_MASK) |
          SHA512_REG_SHA512_CTRL_LAST_MASK;
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL,reg);
}

void sha_next_last(enum sha512_mode_e mode) {
    VPRINTF(MEDIUM,"SHA512: Set mode: 0x%x and next with last\n", mode);
    uint32_t reg;
    reg = ((1 << SHA512_REG_SHA512_CTRL_NEXT_LOW) & SHA512_REG_SHA512_CTRL_NEXT_MASK) |
          ((mode << SHA512_REG_SHA512_CTRL_MODE_LOW) & SHA512_REG_SHA512_CTRL_MODE_MASK) |
          SHA512_REG_SHA512_CTRL_LAST_MASK;
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL,reg);
}

void sha_gen_hash_start() {
    VPRINTF(MEDIUM,"SHA512: Set START for gen hash func\n");
    uint32_t reg;
    reg = SHA512_REG_SHA512_GEN_PCR_HASH_CTRL_START_MASK;
    lsu_write_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_CTRL,reg);
}

void sha384_kvflow(uint8_t sha_kv_id, uint8_t store_to_kv, uint8_t digest_kv_id, uint32_t expected_digest[12]){
    uint8_t block_inject_cmd;
    volatile uint32_t * reg_ptr;
    uint8_t offset;
    uint8_t fail_cmd = 0x1;

    uint32_t sha_digest [12];

    //inject sha block to kv key reg (in RTL)
    block_inject_cmd = 0xc0 + (sha_kv_id & 0x7);
    printf("%c", block_inject_cmd);

    // wait for SHA to be ready
    while((lsu_read_32(CLP_SHA512_REG_SHA512_STATUS) & SHA512_REG_SHA512_STATUS_READY_MASK) == 0);


    // Program block Read with 12 dwords from sha_kv_id
    lsu_write_32(CLP_SHA512_REG_SHA512_VAULT_RD_CTRL, SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_MASK |
                                                   ((sha_kv_id << SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_LOW) & SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_MASK));

    // Check that SHA BLOCK is loaded
    while((lsu_read_32(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS) & SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_MASK) == 0);

    // if we want to store the results into kv 
    if (store_to_kv) {
        // set digest DEST to write
        lsu_write_32(CLP_SHA512_REG_SHA512_KV_WR_CTRL,  SHA512_REG_SHA512_KV_WR_CTRL_WRITE_EN_MASK |
                                                        SHA512_REG_SHA512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                        SHA512_REG_SHA512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                        SHA512_REG_SHA512_KV_WR_CTRL_SHA_BLOCK_DEST_VALID_MASK |
                                                        SHA512_REG_SHA512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                        SHA512_REG_SHA512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                        ((digest_kv_id << SHA512_REG_SHA512_KV_WR_CTRL_WRITE_ENTRY_LOW) & SHA512_REG_SHA512_KV_WR_CTRL_WRITE_ENTRY_MASK));
    }    


    // Enable SHA core in SHA384 MODE
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL, SHA512_REG_SHA512_CTRL_INIT_MASK | 
                                            (0x2 << SHA512_REG_SHA512_CTRL_MODE_LOW) |
                                             SHA512_REG_SHA512_CTRL_LAST_MASK);

    // wait for SHA to be valid
    wait_for_sha512_intr();

    // if we want to store the results into kv
    printf("check digest\n");
    if (store_to_kv) {
        // wait for SHA process - check dest done
        while((lsu_read_32(CLP_SHA512_REG_SHA512_KV_WR_STATUS) & SHA512_REG_SHA512_KV_WR_STATUS_VALID_MASK) == 0);
    }
    else{
        reg_ptr = (uint32_t *) CLP_SHA512_REG_SHA512_DIGEST_0;
        printf("Load DIGEST data from SHA384\n");
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_SHA512_REG_SHA512_DIGEST_11) {
            sha_digest[offset] = *reg_ptr;
            if (sha_digest[offset] != expected_digest[offset]) {
                printf("At offset [%d], sha_digest data mismatch!\n", offset);
                printf("Actual   data: 0x%x\n", sha_digest[offset]);
                printf("Expected data: 0x%x\n", expected_digest[offset]);
                printf("%c", fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }

}

void sha512_zeroize(){
    printf("SHA512 zeroize flow.\n");
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL, (1 << SHA512_REG_SHA512_CTRL_ZEROIZE_LOW) & SHA512_REG_SHA512_CTRL_ZEROIZE_MASK);
}

void sha512_flow(sha512_io block, uint8_t mode, sha512_io digest){
    volatile uint32_t * reg_ptr;
    uint8_t offset;
    uint8_t fail_cmd = 0x1;
    uint32_t sha512_digest [16];

    // wait for SHA to be ready
    while((lsu_read_32(CLP_SHA512_REG_SHA512_STATUS) & SHA512_REG_SHA512_STATUS_READY_MASK) == 0);

    // Write SHA512 block
    reg_ptr = (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_31) {
        *reg_ptr++ = block.data[offset++];
    }

    // Enable SHA512 core 
    VPRINTF(LOW, "Enable SHA512\n");
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL, SHA512_REG_SHA512_CTRL_INIT_MASK | 
                                            (mode << SHA512_REG_SHA512_CTRL_MODE_LOW) & SHA512_REG_SHA512_CTRL_MODE_MASK);
    
    // wait for SHA to be valid
    wait_for_sha512_intr();

    reg_ptr = (uint32_t *) CLP_SHA512_REG_SHA512_DIGEST_0;
    printf("Load DIGEST data from SHA512\n");
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_SHA512_REG_SHA512_DIGEST_15) {
        sha512_digest[offset] = *reg_ptr;
        if (sha512_digest[offset] != digest.data[offset]) {
            printf("At offset [%d], sha_digest data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", sha512_digest[offset]);
            printf("Expected data: 0x%x\n", digest.data[offset]);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

}