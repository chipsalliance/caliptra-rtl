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

#ifndef SHA512_H
  #define SHA512_H
  
#include "caliptra_defines.h"
#include "caliptra_reg.h"
#include "riscv_hw_if.h"

/* --------------- symbols/typedefs --------------- */
enum sha512_mode_e {
    SHA512_224_MODE = 0x0,
    SHA512_256_MODE = 0x1,
    SHA512_384_MODE = 0x2,
    SHA512_512_MODE = 0x3
};

/* --------------- Function Prototypes --------------- */
void sha_init(enum sha512_mode_e mode);
void sha_next(enum sha512_mode_e mode);
void sha_init_last(enum sha512_mode_e mode);
void sha_next_last(enum sha512_mode_e mode);

//polls until sha512 is ready to be used
inline void sha512_poll_ready() {
    while((lsu_read_32(CLP_SHA512_REG_SHA512_STATUS) & SHA512_REG_SHA512_STATUS_READY_MASK) == 0);
}
//polls until sha512 is done and valid is set
inline void sha512_poll_valid() {
    while((lsu_read_32(CLP_SHA512_REG_SHA512_STATUS) & SHA512_REG_SHA512_STATUS_VALID_MASK) == 0);
}
//Gen hash functions
void sha_gen_hash_start();
inline void sha_poll_gen_hash_ready() {
    while((lsu_read_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_STATUS) & SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_READY_MASK) == 0);
}
inline void sha_poll_gen_hash_valid() {
    while((lsu_read_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_STATUS) & SHA512_REG_SHA512_GEN_PCR_HASH_STATUS_VALID_MASK) == 0);
}

#endif
