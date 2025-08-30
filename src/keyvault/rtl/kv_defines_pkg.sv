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
`ifndef CALIPTRA_KV_DEFINES_PKG
`define CALIPTRA_KV_DEFINES_PKG

package kv_defines_pkg;

parameter KV_NUM_DWORDS = 16; //number of dwords per key
parameter KV_NUM_KEYS = 24;
parameter KV_ADDR_W = 13;
parameter KV_DATA_W = 32;
parameter KV_ENTRY_ADDR_W = $clog2(KV_NUM_KEYS);
parameter KV_ENTRY_SIZE_W = $clog2(KV_NUM_DWORDS);
parameter KV_NUM_READ=9;
parameter KV_NUM_WRITE=5;
parameter ECC_NUM_DWORDS = 12;
parameter MLDSA_NUM_DWORDS = 8;

parameter KV_ENTRY_FOR_ECC_SIGNING = 7;
parameter KV_ENTRY_FOR_MLDSA_SIGNING = 8;
parameter PCR_HASH_NUM_DWORDS = 16;

localparam KV_STANDARD_SLOT_LOW            = 0;
localparam KV_STANDARD_SLOT_HI             = 15;
localparam KV_OCP_LOCK_SLOT_LOW            = 16;
localparam KV_OCP_LOCK_SLOT_HI             = 23;

localparam OCP_LOCK_RT_OBF_KEY_KV_SLOT  = 16; // Stores the runtime MEK obf key (derived from devid chain). aka MDK
localparam OCP_LOCK_HEK_SEED_KV_SLOT    = 22; // Destination for deobf HEK seed, also for derived HEK
localparam OCP_LOCK_KEY_RELEASE_KV_SLOT = 23; // Stores the fully decrypted MEK
localparam OCP_LOCK_HEK_NUM_DWORDS      = 8;  // 256b HEK Seed -- used to define the write-size from DOE
localparam OCP_LOCK_MEK_NUM_DWORDS      = 16; // 512b MEK -- used to define the entry size fetched from KV

localparam KV_WRITE_IDX_HMAC      = 0;
localparam KV_WRITE_IDX_MLKEM     = 1;
localparam KV_WRITE_IDX_ECC       = 2;
localparam KV_WRITE_IDX_DOE       = 3;
localparam KV_WRITE_IDX_AES       = 4;

localparam KV_DEST_IDX_HMAC_KEY   = 0;
localparam KV_DEST_IDX_HMAC_BLOCK = 1;
localparam KV_DEST_IDX_MLDSA_SEED = 2;
localparam KV_DEST_IDX_ECC_PKEY   = 3;
localparam KV_DEST_IDX_ECC_SEED   = 4;
localparam KV_DEST_IDX_AES_KEY    = 5;
localparam KV_DEST_IDX_MLKEM_SEED = 6;
localparam KV_DEST_IDX_MLKEM_MSG  = 7;
localparam KV_DEST_IDX_DMA_DATA   = 8;
    
// HEK seed (deobfuscated) is used as context for SP 800-108 KDF when deriving
// the HEK
localparam OCP_LOCK_HEK_SEED_DEST_VALID = (1 << KV_DEST_IDX_HMAC_BLOCK);

typedef struct packed {
    logic   [KV_ADDR_W-1:0] addr;
    logic   [KV_DATA_W-1:0] wdata;
    logic                   write;
} kv_uc_req_t;

typedef struct packed {
    logic   [KV_ENTRY_ADDR_W-1:0] read_entry;
    logic   [KV_ENTRY_SIZE_W-1:0] read_offset;
} kv_read_t;

typedef struct packed {
    logic                         write_en;
    logic   [KV_ENTRY_ADDR_W-1:0] write_entry;
    logic   [KV_ENTRY_SIZE_W-1:0] write_offset;
    logic   [KV_DATA_W-1:0]       write_data;
    logic   [KV_NUM_READ-1:0]     write_dest_valid;
} kv_write_t;

typedef struct packed {
    logic          error;
} kv_wr_resp_t;

typedef struct packed {
    logic                   error;
    logic                   last;
    logic   [KV_DATA_W-1:0] read_data;
} kv_rd_resp_t;

//control register for KV reads
localparam KV_READ_CTRL_RSVD_MSB = 32 - KV_ENTRY_SIZE_W - 1 - 1;
typedef struct packed {
    logic [KV_READ_CTRL_RSVD_MSB:0] rsvd;
    logic [KV_ENTRY_ADDR_W-1:0] read_entry;
    logic pcr_hash_extend;
    logic read_en;
} kv_read_ctrl_reg_t;

//control register for KV writes
localparam KV_WRITE_CTRL_RSVD_MSB = 32 - KV_NUM_READ - KV_ENTRY_ADDR_W - 1;
typedef struct packed {
    logic [KV_WRITE_CTRL_RSVD_MSB:0] rsvd;
    logic [KV_NUM_READ-1:0] write_dest_vld;
    logic [KV_ENTRY_ADDR_W-1:0] write_entry;
    logic write_en;
} kv_write_ctrl_reg_t;

typedef enum logic [7:0] {
    KV_SUCCESS = 8'h00,
    KV_READ_FAIL = 8'h01,
    KV_WRITE_FAIL = 8'h02
} kv_error_code_e;

typedef struct packed {
    logic [PCR_HASH_NUM_DWORDS-1:0][31:0]   pcr_hash;
    logic [ECC_NUM_DWORDS-1:0][31:0]        pcr_ecc_signing_privkey;
    logic [MLDSA_NUM_DWORDS-1:0][31:0]      pcr_mldsa_signing_seed;
} pcr_signing_t;

typedef struct packed {
    logic                       ocp_lock_in_progress;
    logic [KV_NUM_READ-1:0]     kv_read_dest;
    logic [KV_ENTRY_ADDR_W-1:0] kv_key_entry;
} kv_read_filter_metrics_t;

typedef struct packed {
    logic                       ocp_lock_in_progress;
    logic                       kv_data0_present;
    logic [KV_ENTRY_ADDR_W-1:0] kv_data0_entry;
    logic                       kv_data1_present;
    logic [KV_ENTRY_ADDR_W-1:0] kv_data1_entry;
    logic [KV_NUM_WRITE-1:0]    kv_write_src;
    logic [KV_ENTRY_ADDR_W-1:0] kv_write_entry;
    logic                       aes_decrypt_ecb_op;
} kv_write_filter_metrics_t;
endpackage

`endif


