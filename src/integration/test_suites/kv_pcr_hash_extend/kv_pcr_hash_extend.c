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
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = MEDIUM;
#endif

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

    volatile uint32_t* reg_ptr;
    uint8_t offset;
    uint32_t read_data;

    //init_interrupts();

    //set hash extend for entry 0
    pv_hash_extend(0x1f);
    kv_poll_valid(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);
    kv_error_check(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);

    //Write junk to test lock
    reg_ptr = (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_0;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_12) {
        *reg_ptr++ = 0x01234567;
    }
    //Extend hash
    VPRINTF(MEDIUM,"KV: Writing SHA Block with known answer\n");
    offset = 0;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_24) {
        *reg_ptr++ = msg[offset++];
    }
    //Add padding to extended value
    VPRINTF(MEDIUM,"KV: Padding extended hash value\n");
    *reg_ptr++ = 0x80000000;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_31) {
        *reg_ptr++ = 0x00000000;
    }
    //Add length to last dword
    *reg_ptr = 0x00000300;

    //run the sha function
    VPRINTF(MEDIUM,"KV: polling for sha ready\n");
    sha512_poll_ready();
    sha_init_last(SHA512_384_MODE);
    VPRINTF(MEDIUM,"KV: polling for sha valid\n");
    sha512_poll_valid();
    VPRINTF(MEDIUM,"KV: polling for kv valid\n");
    kv_poll_valid(CLP_SHA512_REG_SHA512_KV_WR_STATUS);
    kv_error_check(CLP_SHA512_REG_SHA512_KV_WR_STATUS);

    //check expected output from PCR0
    reg_ptr = (uint32_t*) CLP_PV_REG_PCR_ENTRY_31_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_PV_REG_PCR_ENTRY_31_11) {
        read_data = lsu_read_32(reg_ptr++);
        if (exp1[offset] != read_data) {
            VPRINTF(FATAL,"SHA Result Mismatch - EXP: 0x%x RECVD: 0x%x\n", exp1[offset], read_data);
            SEND_STDOUT_CTRL( 0x01);
        }
        offset++;
    }

    //read 384 bits from PCR 0 and write to SHA512 BLOCK
    VPRINTF(MEDIUM,"KV: polling for kv ready\n");
    kv_poll_ready(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);
    pv_hash_extend(0x1f);
    VPRINTF(MEDIUM,"KV: polling for kv valid\n");
    kv_poll_valid(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);
    kv_error_check(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS);

    //Write junk to test lock
    reg_ptr = (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_0;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_12) {
        *reg_ptr++ = 0x01234567;
    }
    //Extend hash
    VPRINTF(MEDIUM,"KV: Writing SHA Block with known answer\n");
    offset = 0;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_24) {
        *reg_ptr++ = msg[offset++];
    }
    //Add padding to extended value
    VPRINTF(MEDIUM,"KV: Padding extended hash value\n");
    *reg_ptr++ = 0x80000000;
    while (reg_ptr < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_31) {
        *reg_ptr++ = 0x00000000;
    }
    //Add length to last dword
    *reg_ptr = 0x00000300;

    VPRINTF(MEDIUM,"KV: polling for sha ready\n");
    sha512_poll_ready();
    sha_init_last(SHA512_384_MODE);
    VPRINTF(MEDIUM,"KV: polling for sha valid\n");
    sha512_poll_valid();
    VPRINTF(MEDIUM,"KV: polling for kv valid\n");
    kv_poll_valid(CLP_SHA512_REG_SHA512_KV_WR_STATUS);
    kv_error_check(CLP_SHA512_REG_SHA512_KV_WR_STATUS);

    //check expected output from PCR0
    reg_ptr = (uint32_t*) CLP_PV_REG_PCR_ENTRY_31_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_PV_REG_PCR_ENTRY_31_11) {
        read_data = lsu_read_32(reg_ptr++);
        if (exp2[offset] != read_data) {
            VPRINTF(FATAL,"SHA Result Mismatch - EXP: 0x%x RECVD: 0x%x\n", exp2[offset], read_data);
            SEND_STDOUT_CTRL( 0x01);
        }
        offset++;
    }

    VPRINTF(LOW,"----------------------------------\n");
    VPRINTF(LOW," KV PCR Hash Extend Test Complete!\n");
    VPRINTF(LOW,"----------------------------------\n");
    
    SEND_STDOUT_CTRL( 0xff);
}