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
#include "hmac.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {
    .doe_error        = 0,
    .doe_notif        = 0,
    .ecc_error        = 0,
    .ecc_notif        = 0,
    .hmac_error       = 0,
    .hmac_notif       = 0,
    .kv_error         = 0,
    .kv_notif         = 0,
    .sha512_error     = 0,
    .sha512_notif     = 0,
    .sha256_error     = 0,
    .sha256_notif     = 0,
    .qspi_error       = 0,
    .qspi_notif       = 0,
    .uart_error       = 0,
    .uart_notif       = 0,
    .i3c_error        = 0,
    .i3c_notif        = 0,
    .soc_ifc_error    = 0,
    .soc_ifc_notif    = 0,
    .sha512_acc_error = 0,
    .sha512_acc_notif = 0,
};


/* HMAC384 test vector
    KEY = 0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
    BLOCK = 4869205468657265800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000440
    LFSR_SEED = C8F518D4F3AA1BD46ED56C1C3C9E16FB800AF504
    TAG = b6a8d5636f5c6a7224f9977dcf7ee6c7fb6d0c48cbdee9737a959796489bddbc4c5df61d5b3297b4fb68dab9f1b582c2
*/




void main() {
    printf("----------------------------------\n");
    printf(" Smoke Test With Crypto Zeroize !!\n");
    printf("----------------------------------\n");

    //Call interrupt init
    init_interrupts();

    uint32_t block[32] =   {0x48692054,
                            0x68657265,
                            0x80000000,
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
                            0x00000000,
                            0x00000000,
                            0x00000000,
                            0x00000000,
                            0x00000000,
                            0x00000000,
                            0x00000000,
                            0x00000000,
                            0x00000440};

    //this is a random lfsr_seed 160-bit
    uint32_t lfsr_seed_data[5] = {0xC8F518D4,
                                 0xF3AA1BD4,
                                 0x6ED56C1C,
                                 0x3C9E16FB,
                                 0x800AF504}; 

    uint32_t expected_tag[12] =   {0xb6a8d563,
                                    0x6f5c6a72,
                                    0x24f9977d,
                                    0xcf7ee6c7,
                                    0xfb6d0c48,
                                    0xcbdee973,
                                    0x7a959796,
                                    0x489bddbc,
                                    0x4c5df61d,
                                    0x5b3297b4,
                                    0xfb68dab9,
                                    0xf1b582c2}; 


    uint8_t hmackey_kv_id       = 0x2;
    uint8_t tag_kv_id           = 0x0;
    uint8_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;
    uint32_t check_data;

    //inject hmac_key to kv key reg (in RTL)
    uint8_t key_inject_cmd = 0xa0 + (hmackey_kv_id & 0x7);
    printf("%c", key_inject_cmd);

    // wait for HMAC to be ready
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_STATUS) & HMAC_REG_HMAC384_STATUS_READY_MASK) == 0);


    // Program KEY Read with 12 dwords from key_kv_id
    lsu_write_32(CLP_HMAC_REG_HMAC384_KV_RD_KEY_CTRL, HMAC_REG_HMAC384_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                    ((hmackey_kv_id << HMAC_REG_HMAC384_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC384_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

    // Check that HMAC KEY is loaded
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_RD_KEY_STATUS) & HMAC_REG_HMAC384_KV_RD_KEY_STATUS_VALID_MASK) == 0);



    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC384_BLOCK_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC384_BLOCK_31) {
        *reg_ptr++ = block[offset++];
    }


    // Program LFSR_SEED
    reg_ptr = (uint32_t*) CLP_HMAC_REG_HMAC384_LFSR_SEED_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC384_LFSR_SEED_4) {
        *reg_ptr++ = lfsr_seed_data[offset++];
    }

    // if we want to store the results into kv
    // set tag DEST to write

    lsu_write_32(CLP_HMAC_REG_HMAC384_KV_WR_CTRL, HMAC_REG_HMAC384_KV_WR_CTRL_WRITE_EN_MASK |
                                                HMAC_REG_HMAC384_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                HMAC_REG_HMAC384_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                HMAC_REG_HMAC384_KV_WR_CTRL_SHA_BLOCK_DEST_VALID_MASK |
                                                HMAC_REG_HMAC384_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                HMAC_REG_HMAC384_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                ((tag_kv_id << HMAC_REG_HMAC384_KV_WR_CTRL_WRITE_ENTRY_LOW) & HMAC_REG_HMAC384_KV_WR_CTRL_WRITE_ENTRY_MASK));


    //inject zeroize command (in RTL)
    SEND_STDOUT_CTRL(0x99);

    // Enable HMAC core
    lsu_write_32(CLP_HMAC_REG_HMAC384_CTRL, HMAC_REG_HMAC384_CTRL_INIT_MASK);

    // wait for HMAC to be ready
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_STATUS) & HMAC_REG_HMAC384_STATUS_READY_MASK) == 0);

    // check that dest valid bits are 0 since the key generation was interrupted
    check_data = lsu_read_32(CLP_KV_REG_KEY_CTRL_0);
    if ((check_data & (KV_REG_KEY_CTRL_0_DEST_VALID_MASK)) != 0) {
        VPRINTF(ERROR, "ERROR: Dest valid mismatch actual (0x%x) expected (0x00000000)\n", check_data);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    } else {
        SEND_STDOUT_CTRL(0xff); //End the test
    }

    
}
