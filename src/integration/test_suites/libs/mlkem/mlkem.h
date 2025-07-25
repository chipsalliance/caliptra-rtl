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

#ifndef MLKEM_H
  #define MLKEM_H

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"

#define MLKEM_CMD_KEYGEN        0x1
#define MLKEM_CMD_ENCAPS        0x2
#define MLKEM_CMD_DECAPS        0x3
#define MLKEM_CMD_KEYGEN_DECAPS 0x4

#define MLKEM_SEED_SIZE 8
#define ABR_ENTROPY_SIZE 16
#define MLKEM_EK_SIZE 392
#define MLKEM_DK_SIZE 792
#define MLKEM_MSG_SIZE 8
#define MLKEM_SHAREDKEY_SIZE 8
#define MLKEM_CIPHERTEXT_SIZE 392

typedef uint8_t BOOL;
#define FALSE 0u
#define TRUE 1u


typedef struct {
  BOOL      kv_intf;
  uint8_t   kv_id;
  uint32_t  data[2][MLKEM_SEED_SIZE];
} mlkem_seed;

typedef struct {
  BOOL      kv_intf;
  uint8_t   kv_id;
  uint32_t  data[MLKEM_MSG_SIZE];
} mlkem_msg;

typedef struct {
  BOOL      kv_intf;
  uint8_t   kv_id;
  uint32_t data[MLKEM_SHAREDKEY_SIZE];
} mlkem_shared_key;

void mlkem_hex_to_uint32_array(const char *hex_str, uint32_t *array);
void mlkem_zeroize();
void wait_for_mlkem_intr();
void write_mlkem_reg(volatile uint32_t *base_addr, uint32_t *data, uint32_t size);

//These check the results of the flow against expected values
void mlkem_keygen_check(mlkem_seed seed, uint32_t entropy[ABR_ENTROPY_SIZE], uint32_t encaps_key[MLKEM_EK_SIZE], uint32_t decaps_key[MLKEM_DK_SIZE]);
void mlkem_encaps_check(uint32_t encaps_key[MLKEM_EK_SIZE], mlkem_msg msg, uint32_t entropy[ABR_ENTROPY_SIZE], uint32_t ciphertext[MLKEM_CIPHERTEXT_SIZE], mlkem_shared_key shared_key);
void mlkem_decaps_check(uint32_t decaps_key[MLKEM_DK_SIZE], uint32_t ciphertext[MLKEM_CIPHERTEXT_SIZE], uint32_t entropy[ABR_ENTROPY_SIZE], mlkem_shared_key shared_key);
void mlkem_keygen_decaps_check(mlkem_seed seed, uint32_t ciphertext[MLKEM_CIPHERTEXT_SIZE], uint32_t entropy[ABR_ENTROPY_SIZE], mlkem_shared_key shared_key);

//These return the results of the flow
void mlkem_keygen_flow(mlkem_seed seed, uint32_t entropy[ABR_ENTROPY_SIZE], uint32_t encaps_key[MLKEM_EK_SIZE], uint32_t decaps_key[MLKEM_DK_SIZE]);
void mlkem_encaps_flow(uint32_t encaps_key[MLKEM_EK_SIZE], mlkem_msg msg, uint32_t entropy[ABR_ENTROPY_SIZE], uint32_t ciphertext[MLKEM_CIPHERTEXT_SIZE], mlkem_shared_key shared_key, uint32_t* shared_key_o);
void mlkem_decaps_flow(uint32_t decaps_key[MLKEM_DK_SIZE], uint32_t ciphertext[MLKEM_CIPHERTEXT_SIZE], uint32_t entropy[ABR_ENTROPY_SIZE], mlkem_shared_key shared_key);
void mlkem_keygen_decaps_flow(mlkem_seed seed, uint32_t ciphertext[MLKEM_CIPHERTEXT_SIZE], uint32_t entropy[ABR_ENTROPY_SIZE], mlkem_shared_key shared_key);

#endif
