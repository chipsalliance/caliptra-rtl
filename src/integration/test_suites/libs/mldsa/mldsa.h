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

#ifndef MLDSA_H
  #define MLDSA_H

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"

#define MLDSA_CMD_KEYGEN       0x1
#define MLDSA_CMD_SIGNING      0x2
#define MLDSA_CMD_VERIFYING    0x3
#define MLDSA_CMD_KEYGEN_SIGN  0x4

#define MLDSA87_SEED_SIZE 8
#define MLDSA87_SIGN_RND_SIZE 8
#define MLDSA87_ENTROPY_SIZE 16
#define MLDSA87_PRIVKEY_SIZE 1224
#define MLDSA87_PUBKEY_SIZE 648
#define MLDSA87_MSG_SIZE 16
#define MLDSA87_EXTERNAL_MU_SIZE 16
#define MLDSA87_PUBKEY_HASH_SIZE 16
#define MLDSA87_SIGN_SIZE 1157
#define MLDSA_VERIFY_RES_SIZE 16

typedef uint8_t BOOL;
#define FALSE 0u
#define TRUE 1u


typedef struct {
  BOOL      kv_intf;
  uint8_t   kv_id;
  uint32_t  data[MLDSA87_SEED_SIZE];
} mldsa_io;

void mldsa_zeroize();
void wait_for_mldsa_intr();
void write_mldsa_reg(volatile uint32_t *base_addr, uint32_t *data, uint32_t size);
void mldsa_keygen_flow(mldsa_io seed, uint32_t entropy[MLDSA87_ENTROPY_SIZE], uint32_t privkey[MLDSA87_PRIVKEY_SIZE], uint32_t pubkey[MLDSA87_PUBKEY_SIZE]);
void mldsa_signing_flow(uint32_t privkey[MLDSA87_PRIVKEY_SIZE], uint32_t msg[MLDSA87_MSG_SIZE], uint32_t sign_rnd[MLDSA87_SIGN_RND_SIZE], uint32_t entropy[MLDSA87_ENTROPY_SIZE], uint32_t sign[MLDSA87_SIGN_SIZE]);
void mldsa_verifying_flow(uint32_t msg[MLDSA87_MSG_SIZE], uint32_t pubkey[MLDSA87_PUBKEY_SIZE], uint32_t sign[MLDSA87_SIGN_SIZE], uint32_t verify_res[MLDSA_VERIFY_RES_SIZE]);
void mldsa_keygen_signing_flow(mldsa_io seed, uint32_t msg[MLDSA87_MSG_SIZE], uint32_t sign_rnd[MLDSA87_SIGN_RND_SIZE], uint32_t entropy[MLDSA87_ENTROPY_SIZE], uint32_t sign[MLDSA87_SIGN_SIZE]);

void mldsa_signing_external_mu_flow(uint32_t privkey[MLDSA87_PRIVKEY_SIZE], uint32_t external_mu[MLDSA87_EXTERNAL_MU_SIZE], uint32_t sign_rnd[MLDSA87_SIGN_RND_SIZE], uint32_t entropy[MLDSA87_ENTROPY_SIZE], uint32_t sign[MLDSA87_SIGN_SIZE]);
void mldsa_verifying_external_mu_flow(uint32_t external_mu[MLDSA87_EXTERNAL_MU_SIZE], uint32_t pubkey[MLDSA87_PUBKEY_SIZE], uint32_t sign[MLDSA87_SIGN_SIZE], uint32_t verify_res[MLDSA_VERIFY_RES_SIZE]);
void mldsa_keygen_signing_external_mu_flow(mldsa_io seed, uint32_t external_mu[MLDSA87_EXTERNAL_MU_SIZE], uint32_t sign_rnd[MLDSA87_SIGN_RND_SIZE], uint32_t entropy[MLDSA87_ENTROPY_SIZE], uint32_t sign[MLDSA87_SIGN_SIZE]);

void mldsa_keyload_error_flow(mldsa_io seed);
#endif
