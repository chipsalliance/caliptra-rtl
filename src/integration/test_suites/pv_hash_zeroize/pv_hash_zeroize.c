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

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = MEDIUM;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};


    // exp3 = SHA512(31*384'h0 | expected2 | nonce)
const uint32_t exp3[] = {0x4f373650,
                       0x83ef4325,
                       0x29e9bcdb,
                       0x404adf86,
                       0x05566e5c,
                       0xe1f01af8,
                       0x01a485ec,
                       0x46d049d1,
                       0x48028f54,
                       0x31afc07f,
                       0x4abc21c1,
                       0x5df9f791,
                       0x125cff3b,
                       0xbff7aa9f,
                       0x7610ca06,
                       0x819ec76a};

const uint32_t nonce[] = {0x01234567,
                        0x11111111,
                        0x22222222,
                        0x33333333,
                        0x44444444,
                        0x55555555,
                        0x66666666,
                        0x77777777};


void main() {
    VPRINTF(LOW,"----------------------------\n");
    VPRINTF(LOW," KV PCR Hash Zeroize Test !!\n");
    VPRINTF(LOW,"----------------------------\n");

    volatile uint32_t* reg_ptr;
    uint8_t offset;
    uint32_t read_data;
    uint32_t reg;

    //init_interrupts();

    SEND_STDOUT_CTRL(0xf3); //init pcr vault entry 1f

    sha_poll_gen_hash_ready();
    lsu_write_32(CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_0,0x00000000);
    sha_gen_hash_start();
    
    sha512_zeroize();

    sha_poll_gen_hash_ready();
    //check expected output from digest
    reg_ptr = (uint32_t*) CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_SHA512_REG_SHA512_GEN_PCR_HASH_DIGEST_11) {
        read_data = *reg_ptr++;
        if (read_data != 0) {
            VPRINTF(FATAL,"SHA Result Mismatch - EXP: 0x%x RECVD: 0x%x\n", 0, read_data);
            SEND_STDOUT_CTRL( 0x01);
        }
        offset++;
    }
    VPRINTF(MEDIUM,"Zeroize for sha is completed\n");

    SEND_STDOUT_CTRL(0xf3); //init pcr vault entry 1f
    sha_poll_gen_hash_ready();
    reg_ptr = (uint32_t*) CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_SHA512_REG_SHA512_GEN_PCR_HASH_NONCE_7) {
        *reg_ptr++ = nonce[offset++];
    }
    sha_gen_hash_start();

    //issue init/next while engine is busy
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL,((1 << SHA512_REG_SHA512_CTRL_INIT_LOW) & SHA512_REG_SHA512_CTRL_INIT_MASK));
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL,((1 << SHA512_REG_SHA512_CTRL_NEXT_LOW) & SHA512_REG_SHA512_CTRL_NEXT_MASK));

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

    VPRINTF(LOW,"----------------------------------\n");
    VPRINTF(LOW," KV PCR Hash Extend Test Complete!\n");
    VPRINTF(LOW,"----------------------------------\n");

    SEND_STDOUT_CTRL( 0xff); 
}
