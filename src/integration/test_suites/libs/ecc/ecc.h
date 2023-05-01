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

#ifndef ECC_H
  #define ECC_H

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"

typedef uint8_t BOOL;
#define FALSE 0u
#define TRUE 1u

typedef struct {
    BOOL      kv_intf;
    uint8_t   kv_id;
    uint32_t  data[12];
}ecc_io;

void ecc_keygen_flow(ecc_io seed, ecc_io nonce, ecc_io iv, ecc_io privkey, ecc_io pubkey_x, ecc_io pubkey_y);
void ecc_signing_flow(ecc_io privkey, ecc_io msg, ecc_io iv, ecc_io sign_r, ecc_io sign_s);
void ecc_verifying_flow(ecc_io msg, ecc_io pubkey_x, ecc_io pubkey_y, ecc_io sign_r, ecc_io sign_s);
void ecc_pcr_signing_flow(ecc_io iv, ecc_io sign_r, ecc_io sign_s);
void ecc_zeroize();

#endif
