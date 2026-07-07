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

#ifndef HMAC256_H
  #define HMAC256_H

#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"

#ifndef BOOL
typedef uint8_t BOOL;
#define FALSE 0u
#define TRUE  1u
#endif

#define HMAC256_KEY_SIZE   16
#define HMAC256_BLOCK_SIZE 16
#define HMAC256_TAG_SIZE    8
#define HMAC224_TAG_SIZE    7
#define HMAC256_LFSR_SEED_SIZE 6

typedef struct {
    uint8_t   data_size;
    uint32_t  data[16];
} hmac256_io;

void hmac256_flow(hmac256_io key, hmac256_io block, hmac256_io lfsr_seed,
                  hmac256_io tag, BOOL init, BOOL last, BOOL mode);
void hmac256_zeroize(void);
void wait_for_hmac256_intr(void);

#endif
