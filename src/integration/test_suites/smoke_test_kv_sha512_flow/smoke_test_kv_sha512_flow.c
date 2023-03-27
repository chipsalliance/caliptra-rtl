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
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t rst_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

uint8_t fail_cmd = 0x1;

/* SHA384 test vector:
    block = b1eeef324b499f19eba322215fe3ce19c9f000b698d2b2dab7145015046cc86d049ee15ad59dcd1564f30112e06444cb
    digest = 38742d18bfa6e918b888d68d1034e61f65dec0759172c2dbf08cf1e132b217eaf4ec29e15db7f4b07e08a70cc5662012
*/

void sha384_kvflow_test(uint8_t sha_kv_id, uint8_t store_to_kv, uint8_t digest_kv_id, uint32_t expected_digest[12]){
    uint8_t block_inject_cmd;
    volatile uint32_t * reg_ptr;

    uint32_t sha_digest [12];

    //inject sha block to kv key reg (in RTL)
    block_inject_cmd = 0x90 + (sha_kv_id & 0x7);
    printf("%c", block_inject_cmd);

    // wait for SHA to be ready
    while((lsu_read_32(CLP_SHA512_REG_SHA512_STATUS) & SHA512_REG_SHA512_STATUS_READY_MASK) == 0);


    // Program block Read with 12 dwords from sha_kv_id
    lsu_write_32(CLP_SHA512_REG_SHA512_VAULT_RD_CTRL, SHA512_REG_SHA512_VAULT_RD_CTRL_READ_EN_MASK |
                                                   ((sha_kv_id & 0x7) << SHA512_REG_SHA512_VAULT_RD_CTRL_READ_ENTRY_LOW));

    // Check that SHA BLOCK is loaded
    while((lsu_read_32(CLP_SHA512_REG_SHA512_VAULT_RD_STATUS) & SHA512_REG_SHA512_VAULT_RD_STATUS_VALID_MASK) == 0);

    // if we want to store the results into kv 
    if (store_to_kv) {
        // set digest DEST to write
        lsu_write_32(CLP_SHA512_REG_SHA512_KV_WR_CTRL,  SHA512_REG_SHA512_KV_WR_CTRL_WRITE_EN_MASK |
                                                        SHA512_REG_SHA512_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                        SHA512_REG_SHA512_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                        SHA512_REG_SHA512_KV_WR_CTRL_SHA_BLOCK_DEST_VALID_MASK |
                                                        SHA512_REG_SHA512_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                        SHA512_REG_SHA512_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                        SHA512_REG_SHA512_KV_WR_CTRL_ECC_MSG_DEST_VALID_MASK |
                                                        ((digest_kv_id & 0x7) << SHA512_REG_SHA512_KV_WR_CTRL_WRITE_ENTRY_LOW));
    }    


    // Enable SHA core in SHA384 MODE
    lsu_write_32(CLP_SHA512_REG_SHA512_CTRL, SHA512_REG_SHA512_CTRL_INIT_MASK | 
                                            (0x2 << SHA512_REG_SHA512_CTRL_MODE_LOW) |
                                             SHA512_REG_SHA512_CTRL_LAST_MASK);

    // if we want to store the results into kv
    printf("check digest\n");
    if (store_to_kv) {
        // wait for SHA process - check dest done
        while((lsu_read_32(CLP_SHA512_REG_SHA512_KV_WR_STATUS) & SHA512_REG_SHA512_KV_WR_STATUS_VALID_MASK) == 0);
    }
    else{
        reg_ptr = (uint32_t *) CLP_SHA512_REG_SHA512_DIGEST_0;
        //printf("\nsha_digest: 0x");
        for (uint32_t i=0; i<12; i++){  // the first 12 digests for SHA384
            sha_digest[i] = *(reg_ptr++);
            //printf("%08x", sha_digest[i]);
        }
        //printf("\n");
        if (memcmp(sha_digest, expected_digest, sizeof(expected_digest)) != 0){
            printf("DIGEST MISMATCH!\n");
            printf("%c", fail_cmd);
        }
    }

}

void main() {
    printf("----------------------------------\n");
    printf(" KV Smoke Test With SHA384 flow !!\n");
    printf("----------------------------------\n");

    //Call interrupt init
    //init_interrupts();

    uint32_t expected_digest[] =   {0x38742d18,
                                    0xbfa6e918,
                                    0xb888d68d,
                                    0x1034e61f,
                                    0x65dec075,
                                    0x9172c2db,
                                    0xf08cf1e1,
                                    0x32b217ea,
                                    0xf4ec29e1,
                                    0x5db7f4b0,
                                    0x7e08a70c,
                                    0xc5662012};

    uint8_t shablock_kv_id = 0x0;
    uint8_t store_to_kv = 0x1;
    uint8_t digest_kv_id = 0x0;
    sha384_kvflow_test(shablock_kv_id, store_to_kv, digest_kv_id, expected_digest);
    
    printf("%c",0xff); //End the test
    
}
