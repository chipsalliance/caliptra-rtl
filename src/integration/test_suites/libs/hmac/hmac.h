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

#ifndef HMAC_H
  #define HMAC_H

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"

typedef uint8_t BOOL;
#define FALSE 0u
#define TRUE 1u

#define HMAC512_KEY_SIZE 16
#define HMAC384_KEY_SIZE 12
#define HMAC512_BLOCK_SIZE 32
#define HMAC512_LFSR_SEED_SIZE 12
#define HMAC512_TAG_SIZE 16

typedef struct {
    BOOL      kv_intf;
    uint8_t   kv_id;
    uint8_t   data_size;
    uint32_t  data[32];
}hmac_io;

void hmac384_flow(hmac_io hmac_key, hmac_io block, hmac_io lfsr_seed, hmac_io tag, BOOL init);
void hmac512_flow(hmac_io hmac_key, hmac_io block, hmac_io lfsr_seed, hmac_io tag, BOOL init);
void hmac512_flow_csr(hmac_io hmac_key, hmac_io block, hmac_io lfsr_seed, hmac_io tag, BOOL init);
void hmac512_flow_return(hmac_io hmac_key, hmac_io block, hmac_io lfsr_seed, hmac_io tag, BOOL init, uint32_t* actual_tag);
void hmac_zeroize();
void wait_for_hmac_intr();
void write_hmac_reg(volatile uint32_t *base_addr, uint32_t *data, uint32_t size);


#endif
