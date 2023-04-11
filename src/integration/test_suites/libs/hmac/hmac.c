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

void hmac_flow(hmac_io key, hmac_io block, hmac_io lfsr_seed, hmac_io tag){
    uint8_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t hmac_tag   [12];


    // wait for HMAC to be ready
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_STATUS) & HMAC_REG_HMAC384_STATUS_READY_MASK) == 0);

    if (key.kv_intf){
        // Program KEY Read with 12 dwords from key_kv_id
        lsu_write_32(CLP_HMAC_REG_HMAC384_KV_RD_KEY_CTRL, HMAC_REG_HMAC384_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                        ((key.kv_id << HMAC_REG_HMAC384_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC384_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

        // Check that HMAC KEY is loaded
        while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_RD_KEY_STATUS) & HMAC_REG_HMAC384_KV_RD_KEY_STATUS_VALID_MASK) == 0);

    }
    else{
        // Load key from hw_data and write to HMAC core
        VPRINTF(LOW, "Load Key data to HMAC\n");
        reg_ptr         = (uint32_t*) CLP_HMAC_REG_HMAC384_KEY_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC384_KEY_11) {
            *reg_ptr++ = key.data[offset++];
        }
    }

    
    if (block.kv_intf){
        // Program HMAC_BLOCK
        lsu_write_32(CLP_HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL, HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL_READ_EN_MASK |
                                                            ((block.kv_id << HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL_READ_ENTRY_MASK));

        // Check that HMAC BLOCK is loaded
        while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_RD_BLOCK_STATUS) & HMAC_REG_HMAC384_KV_RD_BLOCK_STATUS_VALID_MASK) == 0);
    }
    else{
        reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC384_BLOCK_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC384_BLOCK_31) {
            *reg_ptr++ = block.data[offset++];
        }
    }

    // Program LFSR_SEED
    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC384_LFSR_SEED_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC384_LFSR_SEED_4) {
        *reg_ptr++ = lfsr_seed.data[offset++];
    }

    // if we want to store the results into kv
    // set tag DEST to write
    if (tag.kv_intf){
        lsu_write_32(CLP_HMAC_REG_HMAC384_KV_WR_CTRL, HMAC_REG_HMAC384_KV_WR_CTRL_WRITE_EN_MASK |
                                                      HMAC_REG_HMAC384_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC384_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                      HMAC_REG_HMAC384_KV_WR_CTRL_SHA_BLOCK_DEST_VALID_MASK |
                                                      HMAC_REG_HMAC384_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                      HMAC_REG_HMAC384_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                      ((tag.kv_id << HMAC_REG_HMAC384_KV_WR_CTRL_WRITE_ENTRY_LOW) & HMAC_REG_HMAC384_KV_WR_CTRL_WRITE_ENTRY_MASK));
    }

    // Enable HMAC core
    lsu_write_32(CLP_HMAC_REG_HMAC384_CTRL, HMAC_REG_HMAC384_CTRL_INIT_MASK);

    // wait for HMAC process to be done
    if (tag.kv_intf){
        // wait for HMAC process - check dest done
        printf("Load TAG data from HMAC to KV\n");
        while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_WR_STATUS) & HMAC_REG_HMAC384_KV_WR_STATUS_VALID_MASK) == 0);
    }
    else{
        printf("Load TAG data from HMAC\n");
        reg_ptr = (uint32_t *) CLP_HMAC_REG_HMAC384_TAG_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC384_TAG_11) {
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