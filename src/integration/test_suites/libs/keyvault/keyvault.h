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

#ifndef KEYVAULT_H
  #define KEYVAULT_H

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"

/* --------------- symbols/typedefs --------------- */
//need generic read/write control defines
#define KV_RD_CTRL_READ_EN_LOW (SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_LOW)
#define KV_RD_CTRL_READ_EN_MASK (SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_MASK)
#define KV_RD_CTRL_READ_ENTRY_LOW (SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_LOW)
#define KV_RD_CTRL_READ_ENTRY_MASK (SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_MASK)
#define KV_RD_CTRL_PCR_HASH_EXTEND_LOW (SHA512_REG_SHA512_VAULT_RD_CTRL_PCR_HASH_EXTEND_LOW)
#define KV_RD_CTRL_PCR_HASH_EXTEND_MASK (SHA512_REG_SHA512_VAULT_RD_CTRL_PCR_HASH_EXTEND_MASK)
#define KV_RD_CTRL_RSVD_LOW (SHA512_REG_SHA512_VAULT_RD_CTRL_RSVD_LOW)
#define KV_RD_CTRL_RSVD_MASK (SHA512_REG_SHA512_VAULT_RD_CTRL_RSVD_MASK)

#define KV_WR_CTRL_WRITE_EN_LOW (SHA512_REG_SHA512_KV_WR_CTRL_WRITE_EN_LOW)
#define KV_WR_CTRL_WRITE_EN_MASK (SHA512_REG_SHA512_KV_WR_CTRL_WRITE_EN_MASK)
#define KV_WR_CTRL_WRITE_ENTRY_LOW (SHA512_REG_SHA512_KV_WR_CTRL_WRITE_ENTRY_LOW)
#define KV_WR_CTRL_WRITE_ENTRY_MASK (SHA512_REG_SHA512_KV_WR_CTRL_WRITE_ENTRY_MASK)
#define KV_WR_CTRL_HMAC_KEY_DEST_VALID_LOW (SHA512_REG_SHA512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_LOW)
#define KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK (SHA512_REG_SHA512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK)
#define KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_LOW (SHA512_REG_SHA512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_LOW)
#define KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK (SHA512_REG_SHA512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK)
#define KV_WR_CTRL_SHA_BLOCK_DEST_VALID_LOW (SHA512_REG_SHA512_KV_WR_CTRL_SHA_BLOCK_DEST_VALID_LOW)
#define KV_WR_CTRL_SHA_BLOCK_DEST_VALID_MASK (SHA512_REG_SHA512_KV_WR_CTRL_SHA_BLOCK_DEST_VALID_MASK)
#define KV_WR_CTRL_ECC_PKEY_DEST_VALID_LOW (SHA512_REG_SHA512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_LOW)
#define KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK (SHA512_REG_SHA512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK)
#define KV_WR_CTRL_ECC_SEED_DEST_VALID_LOW (SHA512_REG_SHA512_KV_WR_CTRL_ECC_SEED_DEST_VALID_LOW)
#define KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK (SHA512_REG_SHA512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK)

#define KV_RD_STATUS_READY_MASK (SHA512_REG_SHA512_VAULT_RD_STATUS_READY_MASK)
#define KV_RD_STATUS_VALID_MASK (SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_MASK)
#define KV_RD_STATUS_ERROR_MASK (SHA512_REG_SHA512_VAULT_RD_STATUS_ERROR_MASK)

typedef struct {
    unsigned hmac_key:1;
    unsigned hmac_block:1;
    unsigned sha_block:1;
    unsigned ecc_pkey:1;
    unsigned ecc_seed:1;
} dest_valid_t;

/* --------------- Function Prototypes --------------- */
void kv_set_lock_use(uint32_t entry);
void kv_set_lock_wr(uint32_t entry);
void kv_set_clear(uint32_t entry);

void kv_error_check(uint32_t reg_addr);
void kv_read_ctrl(uint32_t reg_addr, uint32_t read_entry);
void kv_write_ctrl(uint32_t reg_addr, uint32_t write_entry, dest_valid_t dest_valid);

void pv_hash_extend(uint32_t pcr_entry);

//polls until kv control is ready to be used
inline void kv_poll_ready(uint32_t reg_addr) {
    while((lsu_read_32(reg_addr) & KV_RD_STATUS_READY_MASK) == 0);
}
//polls until kv control is done and valid is set
inline void kv_poll_valid(uint32_t reg_addr) {
    while((lsu_read_32(reg_addr) & KV_RD_STATUS_VALID_MASK) == 0);
}


#endif
