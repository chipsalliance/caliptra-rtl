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

#ifndef AES_H
  #define AES_H

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"
#include "keyvault.h"

typedef uint8_t BOOL;
#define FALSE 0u
#define TRUE 1u

typedef enum {
  AES_ECB = (1 << 0),
  AES_CBC = (1 << 1),
  AES_CFB = (1 << 2),
  AES_OFB = (1 << 3),
  AES_CTR = (1 << 4),
  AES_GCM = (1 << 5)
} aes_mode_e;

typedef enum {
  AES_ENC = (1 << 0),
  AES_DEC = (1 << 1)
} aes_op_e;

typedef enum {
  AES_128 = (1 << 0),
  AES_192 = (1 << 1),
  AES_256 = (1 << 2)
} aes_key_len_e;

typedef enum {
  GCM_INIT    = (1 << 0),
  GCM_RESTORE = (1 << 1),
  GCM_AAD     = (1 << 2),
  GCM_TEXT    = (1 << 3),
  GCM_SAVE    = (1 << 4),
  GCM_TAG     = (1 << 5)
} gcm_phase_e;

typedef struct {
    BOOL      kv_intf;
    BOOL      kv_reuse_key;
    BOOL      kv_expect_err;
    uint8_t   kv_id;
    uint32_t  key_share0[8];
    uint32_t  key_share1[8];
} aes_key_t;

typedef struct {
    BOOL      kv_intf;
    uint8_t   kv_id;
    BOOL      kv_expect_err;
    dest_valid_t dest_valid;
} aes_key_o_t;

typedef enum {
    AES_DATA_DIRECT, // Use pointers in aes_flow_t
    AES_DATA_DMA     // Use DMA parameters in aes_flow_t
} aes_data_src_e;

typedef struct packed {
  uint64_t src_addr;
  uint64_t dst_addr;
} dma_transfer_data_t;

typedef struct {
  aes_key_t key;
  aes_key_o_t key_o;
  uint32_t *iv;
  uint32_t text_len;
  uint32_t *plaintext;
  uint32_t *ciphertext;
  uint32_t aad_len;
  uint32_t *aad;
  uint32_t *tag;
  aes_data_src_e data_src_mode;
  dma_transfer_data_t dma_transfer_data;
} aes_flow_t;

void hex_to_uint32_array(const char *hex_str, uint32_t *array, uint32_t *array_size);
void aes_wait_idle();
void aes_flow(aes_op_e op, aes_mode_e mode, aes_key_len_e key_len, aes_flow_t aes_input);
void aes_zeroize();
void populate_kv_slot_aes(aes_key_o_t aes_key_o, aes_key_t aes_key, uint32_t override_text_length, uint32_t expected_key[16], uint8_t encrypt, aes_mode_e mode);

#endif
