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

#include "keyvault.h"
#include "riscv_hw_if.h"
#include "caliptra_defines.h"
#include "printf.h"

void kv_error_check(uint32_t reg_addr) {
    VPRINTF(MEDIUM,"KV: checking for errors\n");
    if ((lsu_read_32(reg_addr) & KV_RD_STATUS_ERROR_MASK) != 0) {
        VPRINTF(FATAL,"KV ERROR\n");
        SEND_STDOUT_CTRL( 0x01);
    }
}

void kv_read_ctrl(uint32_t reg_addr, uint32_t read_entry) {
    VPRINTF(MEDIUM,"KV: prog kv read ctrl\n");
    uint32_t wr_data;

    //assemble write data
    wr_data = (KV_RD_CTRL_READ_EN_MASK) |
              ((read_entry << KV_RD_CTRL_READ_ENTRY_LOW) & KV_RD_CTRL_READ_ENTRY_MASK);

    //write to the appropriate read control register
    lsu_write_32(reg_addr, wr_data);
}

void kv_write_ctrl(uint32_t reg_addr, uint32_t write_entry, dest_valid_t dest_valid) {
    VPRINTF(MEDIUM,"KV: prog kv write ctrl\n");
    uint32_t wr_data;

    //assemble write data
    wr_data = (KV_WR_CTRL_WRITE_EN_MASK) |
              ((write_entry << KV_WR_CTRL_WRITE_ENTRY_LOW) & KV_WR_CTRL_WRITE_ENTRY_MASK) |
              ((dest_valid.hmac_key << KV_WR_CTRL_HMAC_KEY_DEST_VALID_LOW) & KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK) |
              ((dest_valid.hmac_block << KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_LOW) & KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK) |
              ((dest_valid.sha_block << KV_WR_CTRL_SHA_BLOCK_DEST_VALID_LOW) & KV_WR_CTRL_SHA_BLOCK_DEST_VALID_MASK) |
              ((dest_valid.ecc_pkey << KV_WR_CTRL_ECC_PKEY_DEST_VALID_LOW) & KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK) |
              ((dest_valid.ecc_seed << KV_WR_CTRL_ECC_SEED_DEST_VALID_LOW) & KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK) |
              ((dest_valid.ecc_msg << KV_WR_CTRL_ECC_MSG_DEST_VALID_LOW) & KV_WR_CTRL_ECC_MSG_DEST_VALID_MASK);

    //write to the appropriate read control register
    lsu_write_32(reg_addr, wr_data);

}

void pv_hash_extend(uint32_t pcr_entry) {
    VPRINTF(MEDIUM,"PV: prog kv read ctrl in SHA to do hash extend\n");
    uint32_t wr_data;

    //assemble write data
    wr_data = (KV_RD_CTRL_READ_EN_MASK) |
              ((pcr_entry << KV_RD_CTRL_READ_ENTRY_LOW) & KV_RD_CTRL_READ_ENTRY_MASK) |
              KV_RD_CTRL_PCR_HASH_EXTEND_MASK;


    //write to the appropriate read control register
    lsu_write_32(CLP_SHA512_REG_SHA512_VAULT_RD_CTRL, wr_data);

}
