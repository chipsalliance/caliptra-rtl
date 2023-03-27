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

/*

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"


static void ecc_keygen_kvflow(uint8_t seed_kv_id, uint8_t privkey_kv_id, uint32_t ecc_iv[12], uint32_t expected_pubkey_x[12], uint32_t expected_pubkey_y[12]){
    uint8_t seed_inject_cmd;
    uint8_t offset;
    volatile uint32_t * reg_ptr;

    uint32_t ecc_pubkey_x [12];
    uint32_t ecc_pubkey_y [12];

    //inject seed to kv key reg (in RTL)
    seed_inject_cmd = 0x80 + (seed_kv_id & 0x7);
    printf("%c", seed_inject_cmd);

    // wait for ECC to be ready
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    // Program ECC_SEED Read with 12 dwords from seed_kv_id
    lsu_write_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL, (ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK |
                                                                ((seed_kv_id & 0x7) << ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW) |
                                                                (0xB << ECC_REG_ECC_KV_RD_SEED_CTRL_ENTRY_DATA_SIZE_LOW)));

    // Check that ECC SEED is loaded
    while((lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_STATUS) & ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_MASK) == 0);

    // set privkey DEST to write
    lsu_write_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, (ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                                                                ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK |
                                                                ((privkey_kv_id & 0x7) << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW)));

    
    // Write ECC IV
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
        *reg_ptr++ = ecc_iv[offset++];
    }

    // Enable ECC KEYGEN core
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, 0x1);

    // wait for ECC KEYGEN process to be done
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_VALID_MASK) == 0);
    
    // check dest done
    while((lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_STATUS) & ECC_REG_ECC_KV_WR_PKEY_STATUS_VALID_MASK) == 0);

    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_PUBKEY_X_0;
    //printf("\npubkey_x: 0x");
    for (uint32_t i=0; i<12; i++){
        ecc_pubkey_x[i] = *(reg_ptr++);
        //printf("%08x", ecc_pubkey_x[i]);
    }
    //printf("\n");
    if (memcmp(ecc_pubkey_x, expected_pubkey_x, sizeof(expected_pubkey_x)) != 0){
        printf("PUBKEY_X MISMATCH!\n");
        printf("%c", fail_cmd);
    }
    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_PUBKEY_Y_0;
    //printf("\npubkey_y: 0x");
    for (uint32_t i=0; i<12; i++){
        ecc_pubkey_y[i] = *(reg_ptr++);
        //printf("%08x", ecc_pubkey_y[i]);
    };
    //printf("\n");
    if (memcmp(ecc_pubkey_y, expected_pubkey_y, sizeof(expected_pubkey_y)) != 0){
        printf("PUBKEY_Y MISMATCH!\n");
        printf("%c", fail_cmd);
    }

}


static void ecc_signing_kvflow(uint8_t privkey_kv_id, uint32_t ecc_msg[12], uint32_t ecc_iv[12], uint32_t expected_sign_r[12], uint32_t expected_sign_s[12]){
    uint8_t offset;
    volatile uint32_t * reg_ptr;

    uint32_t ecc_sign_r [12];
    uint32_t ecc_sign_s [12];

    //inject privkey to kv key reg
    //suppose privkey is stored by ecc_keygen

    // wait for ECC to be ready
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    // Program ECC_PRIVKEY Read with 12 dwords from privkey_kv_id
    lsu_write_32(CLP_ECC_REG_ECC_KV_RD_PKEY_CTRL, (ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_MASK |
                                                                ((privkey_kv_id & 0x7) << ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_LOW) |
                                                                (0xB << ECC_REG_ECC_KV_RD_PKEY_CTRL_ENTRY_DATA_SIZE_LOW)));

    // Check that ECC PRIVKEY is loaded
    while((lsu_read_32(CLP_ECC_REG_ECC_KV_RD_PKEY_STATUS) & ECC_REG_ECC_KV_RD_PKEY_STATUS_VALID_MASK) == 0);
    

    
    // Program ECC MSG
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_MSG_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_MSG_11) {
        *reg_ptr++ = ecc_msg[offset++];
    }

    // Program ECC IV
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
        *reg_ptr++ = ecc_iv[offset++];
    }

    // Enable ECC SIGNING core
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, 0x2);
    
    // wait for ECC SIGNING process to be done
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_VALID_MASK) == 0);
    
    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_SIGN_R_0;
    //printf("\nsign_r: 0x");
    for (uint32_t i=0; i<12; i++){
        ecc_sign_r[i] = *(reg_ptr++);
        //printf("%08x", ecc_sign_r[i]);
    }
    if (memcmp(ecc_sign_r, expected_sign_r, sizeof(expected_sign_r)) != 0){
        printf("SIGN_R MISMATCH!\n");
        printf("%c", fail_cmd);
    }
    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_SIGN_S_0;
    //printf("\nsign_s: 0x");
    for (uint32_t i=0; i<12; i++){
        ecc_sign_s[i] = *(reg_ptr++);
        //printf("%08x", ecc_sign_s[i]);
    };
    if (memcmp(ecc_sign_s, expected_sign_s, sizeof(expected_sign_s)) != 0){
        printf("SIGN_S MISMATCH!\n");
        printf("%c", fail_cmd);
    }
    //printf("\n");

}
*/
