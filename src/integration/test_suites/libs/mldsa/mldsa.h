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

#define MLDSA87_SEED_SIZE 8
#define MLDSA87_SIGN_RND_SIZE 8
#define MLDSA87_ENTROPY_SIZE 16
#define MLDSA87_PRIVKEY_SIZE 1224
#define MLDSA87_PUBKEY_SIZE 648
#define MLDSA87_MSG_SIZE 16
#define MLDSA87_SIGN_SIZE 1157
#define MLDSA_VERIFY_RES_SIZE 16

typedef uint8_t BOOL;
#define FALSE 0u
#define TRUE 1u


typedef struct {
  BOOL      kv_intf;
  uint8_t   kv_id;
  uint32_t  data[8];
} mldsa_io;

void mldsa_zeroize();
void wait_for_mldsa_intr();
void mldsa_keygen_flow(mldsa_io seed, uint32_t sign_rnd[8], uint32_t entropy[16], uint32_t privkey[1224], uint32_t pubkey[648]);
void mldsa_signing_flow(uint32_t privkey[1224], uint32_t msg[16], uint32_t entropy[16], uint32_t sign[1157]);
void mldsa_verifying_flow(uint32_t msg[16], uint32_t pubkey[648], uint32_t sign[1157], uint32_t verifyres[16]);
void mldsa_keygen_signing_flow(mldsa_io seed, uint32_t sign_rnd[8], uint32_t msg[16], uint32_t privkey[1224], uint32_t pubkey[648], uint32_t sign[1157]);
#endif
