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

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "keyvault.h"
#include "sha512.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t rst_count __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = MEDIUM;
#endif

volatile uint32_t * reset_reason  = (uint32_t *) CLP_SOC_IFC_REG_CPTRA_RESET_REASON;

void main() {
    VPRINTF(LOW,"---------------------------\n");
    VPRINTF(LOW," KV PCR Hash Extend Test !!\n");
    VPRINTF(LOW,"---------------------------\n");

    uint32_t msg[] = {0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000,
                      0x00000000};

    uint32_t exp1[] = {0xf57bb7ed,
                       0x82c6ae4a,
                       0x29e6c987,
                       0x9338c592,
                       0xc7d42a39,
                       0x135583e8,
                       0xccbe3940,
                       0xf2344b0e,
                       0xb6eb8503,
                       0xdb0ffd6a,
                       0x39ddd00c,
                       0xd07d8317};

    uint32_t exp2[] = {0x11143121,
                       0xbeb365e6,
                       0x3826e7de,
                       0x89f9c76a,
                       0xe1100411,
                       0xfb9643d1,
                       0x98e730b7,
                       0x603a83a4,
                       0x977c76ee,
                       0xe6ddf74f,
                       0xa0b43fbf,
                       0x49897978};

    uint32_t exp3[] = {0x9bad51d7,
                       0x287c2244,
                       0x154b6f2d,
                       0x77bd52ea,
                       0x0213d314,
                       0x6f4cb39f,
                       0xe27a6d42,
                       0x8886bf0e,
                       0xaab4310a,
                       0x53946e9b,
                       0x70cbd1e7,
                       0xfb158bab};

    uint32_t exp_sign_r[] = {0x4783887c, 
                             0xe3e20caa, 
                             0x4a10c8ef, 
                             0x929fdc23, 
                             0x1c389ab7, 
                             0x72cf8b35, 
                             0xfc1647a5, 
                             0xf1205a1e, 
                             0x50d92ac9, 
                             0x1b5a549a, 
                             0x3944f5aa, 
                             0x52f32b23};

    uint32_t exp_sign_s[] = {0x44bd1e3b, 
                             0x6cb57584, 
                             0x304f77b9, 
                             0xee4a6599, 
                             0x38e3b614, 
                             0x00db744e, 
                             0x6227cbb3, 
                             0x6bbfbbbd, 
                             0xbe1d0815, 
                             0x71fba315, 
                             0xeb049b1e, 
                             0x437af8aa};

    volatile uint32_t* reg_ptr;
    uint8_t offset;
    uint32_t read_data;
    uint32_t reg;

    //init_interrupts();
  
    if(rst_count == 0) {

        SEND_STDOUT_CTRL(0xf3); //init pcr vault entry 1f


        sha_poll_gen_hash_ready();
        lsu_write_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE,0x12345678);
        sha_gen_hash_start();
        
        rst_count++;
        SEND_STDOUT_CTRL(0xee);
        VPRINTF(LOW, "Issuing a warm reset");
        sha_poll_gen_hash_valid();

        //check expected output from digest
        reg_ptr = (uint32_t*) CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_11) {
            read_data = *reg_ptr++;
            if (exp3[offset] != read_data) {
                VPRINTF(FATAL,"SHA Result Mismatch - EXP: 0x%x RECVD: 0x%x\n", exp3[offset], read_data);
                SEND_STDOUT_CTRL( 0x01);
            }
            offset++;
        }

        //Wait for reset to be asserted before advancing
        while(*reset_reason & SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK != SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK);

        VPRINTF(LOW,"----------------------------------\n");
        VPRINTF(LOW," KV PCR Hash Extend Test Complete!\n");
        VPRINTF(LOW,"----------------------------------\n");

        SEND_STDOUT_CTRL( 0xff);
    }  
}
