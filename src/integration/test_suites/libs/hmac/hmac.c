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
#include "hmac.h"
#include "caliptra_isr.h"

extern volatile caliptra_intr_received_s cptra_intr_rcv;

void wait_for_hmac_intr(){
    printf("HMAC flow in progress...\n");
    while((cptra_intr_rcv.hmac_error == 0) & (cptra_intr_rcv.hmac_notif == 0)){
        __asm__ volatile ("wfi"); // "Wait for interrupt"
        // Sleep during HMAC operation to allow ISR to execute and show idle time in sims
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    };
    //printf("Received HMAC error intr with status = %d\n", cptra_intr_rcv.hmac_error);
    printf("Received HMAC notif/err intr with status = %d/ %d\n", cptra_intr_rcv.hmac_notif, cptra_intr_rcv.hmac_error);
}

void hmac_zeroize(){
    printf("HMAC zeroize flow.\n");
    lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, (1 << HMAC_REG_HMAC512_CTRL_ZEROIZE_LOW) & HMAC_REG_HMAC512_CTRL_ZEROIZE_MASK);
}

void hmac384_flow(hmac_io key, hmac_io block, hmac_io lfsr_seed, hmac_io tag, BOOL init){
    uint8_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t hmac_tag   [12];


    // wait for HMAC to be ready
    while((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    if (key.kv_intf){
        // Program KEY Read with 12 dwords from key_kv_id
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                        ((key.kv_id << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

        VPRINTF(LOW, "Try to Overwrite Key data in HMAC384\n");
        reg_ptr         = (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_11) {
            *reg_ptr++ = 0;
        }

        // Check that HMAC KEY is loaded
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK) == 0);

    }
    else{
        // Load key from hw_data and write to HMAC core
        VPRINTF(LOW, "Load Key data to HMAC\n");
        reg_ptr         = (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_11) {
            *reg_ptr++ = key.data[offset++];
        }
    }

    
    if (block.kv_intf){
        // Program HMAC_BLOCK
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL, HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_EN_MASK |
                                                            ((block.kv_id << HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_MASK));

        VPRINTF(LOW, "Try to Overwrite Block data in HMAC\n");
        reg_ptr         = (uint32_t*) CLP_HMAC_REG_HMAC512_BLOCK_0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_BLOCK_31) {
            *reg_ptr++ = 0;
        }

        // Check that HMAC BLOCK is loaded
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS) & HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_VALID_MASK) == 0);
    }
    else{
        reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC512_BLOCK_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_BLOCK_31) {
            *reg_ptr++ = block.data[offset++];
        }
    }

    // Program LFSR_SEED
    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC512_LFSR_SEED_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_LFSR_SEED_11) {
        *reg_ptr++ = lfsr_seed.data[offset++];
    }

    // if we want to store the results into kv
    // set tag DEST to write
    if (tag.kv_intf){
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL, HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK |
                                                      ((tag.kv_id << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) & HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK));
    }

    // Enable HMAC core
    if (init) {
        lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK |
                                                (HMAC384_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));
    }
    else {
        lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_NEXT_MASK |
                                                (HMAC384_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));
    }

    // wait for HMAC process to be done
    wait_for_hmac_intr();

    if (tag.kv_intf){
        // wait for HMAC process - check dest done
        printf("Load TAG data from HMAC to KV\n");
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS) & HMAC_REG_HMAC512_KV_WR_STATUS_VALID_MASK) == 0);
    }
    else{
        printf("Load TAG data from HMAC\n");
        reg_ptr = (uint32_t *) CLP_HMAC_REG_HMAC512_TAG_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_TAG_11) {
            hmac_tag[offset] = *reg_ptr;
            if (hmac_tag[offset] != tag.data[offset]) {
                printf("At offset [%d], hmac_tag data mismatch!\n", offset);
                printf("Actual   data: 0x%x\n", hmac_tag[offset]);
                printf("Expected data: 0x%x\n", tag.data[offset]);
                printf("%c", fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }
}

void hmac512_flow(hmac_io key, hmac_io block, hmac_io lfsr_seed, hmac_io tag, BOOL init){
    uint8_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t hmac_tag   [16];


    // wait for HMAC to be ready
    while((lsu_read_32(CLP_HMAC_REG_HMAC512_STATUS) & HMAC_REG_HMAC512_STATUS_READY_MASK) == 0);

    if (key.kv_intf){
        // Program KEY Read with 12 dwords from key_kv_id
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                        ((key.kv_id << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

        VPRINTF(LOW, "Try to Overwrite Key data in HMAC512\n");
        reg_ptr         = (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_15) {
            *reg_ptr++ = 0;
        }

        // Check that HMAC KEY is loaded
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK) == 0);

    }
    else{
        // Load key from hw_data and write to HMAC core
        VPRINTF(LOW, "Load Key data to HMAC\n");
        reg_ptr         = (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_KEY_15) {
            *reg_ptr++ = key.data[offset++];
        }
    }

    
    if (block.kv_intf){
        // Program HMAC_BLOCK
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL, HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_EN_MASK |
                                                            ((block.kv_id << HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_MASK));

        VPRINTF(LOW, "Try to Overwrite Block data in HMAC\n");
        reg_ptr         = (uint32_t*) CLP_HMAC_REG_HMAC512_BLOCK_0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_BLOCK_31) {
            *reg_ptr++ = 0;
        }

        // Check that HMAC BLOCK is loaded
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS) & HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_VALID_MASK) == 0);
    }
    else{
        reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC512_BLOCK_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_BLOCK_31) {
            *reg_ptr++ = block.data[offset++];
        }
    }

    // Program LFSR_SEED
    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC512_LFSR_SEED_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_LFSR_SEED_11) {
        *reg_ptr++ = lfsr_seed.data[offset++];
    }

    // if we want to store the results into kv
    // set tag DEST to write
    if (tag.kv_intf){
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_WR_CTRL, HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_EN_MASK |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC512_KV_WR_CTRL_AES_KEY_DEST_VALID_MASK  |
                                                      ((tag.kv_id << HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_LOW) & HMAC_REG_HMAC512_KV_WR_CTRL_WRITE_ENTRY_MASK));
    }

    // Enable HMAC core
    if (init) {
        lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_INIT_MASK |
                                                (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));
    }
    else {
        lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, HMAC_REG_HMAC512_CTRL_NEXT_MASK |
                                                (HMAC512_MODE << HMAC_REG_HMAC512_CTRL_MODE_LOW));
    }

    // wait for HMAC process to be done
    wait_for_hmac_intr();

    if (tag.kv_intf){
        // wait for HMAC process - check dest done
        printf("Load TAG data from HMAC to KV\n");
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_WR_STATUS) & HMAC_REG_HMAC512_KV_WR_STATUS_VALID_MASK) == 0);
    }
    else{
        printf("Load TAG data from HMAC\n");
        reg_ptr = (uint32_t *) CLP_HMAC_REG_HMAC512_TAG_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC512_TAG_15) {
            hmac_tag[offset] = *reg_ptr;
            if (hmac_tag[offset] != tag.data[offset]) {
                printf("At offset [%d], hmac_tag data mismatch!\n", offset);
                printf("Actual   data: 0x%x\n", hmac_tag[offset]);
                printf("Expected data: 0x%x\n", tag.data[offset]);
                printf("%c", fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }
}