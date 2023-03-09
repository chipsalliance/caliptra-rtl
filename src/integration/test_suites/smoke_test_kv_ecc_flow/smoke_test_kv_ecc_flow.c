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
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

uint8_t fail_cmd = 0x1;

/* ECC test vector:
    MSG      = C8F518D4F3AA1BD46ED56C1C3C9E16FB800AF504DB98843548C5F623EE115F73D4C62ABC06D303B5D90D9A175087290D
    PRIVKEY  = F274F69D163B0C9F1FC3EBF4292AD1C4EB3CEC1C5A7DDE6F80C14292934C2055E087748D0A169C772483ADEE5EE70E17
    PUBKEY_X = D79C6D972B34A1DFC916A7B6E0A99B6B5387B34DA2187607C1AD0A4D1A8C2E4172AB5FA5D9AB58FE45E43F56BBB66BA4
    PUBKEY_Y = 5A7363932B06B4F223BEF0B60A6390265112DBBD0AAE67FEF26B465BE935B48E451E68D16F1118F2B32B4C28608749ED
    SEED     = 8FA8541C82A392CA74F23ED1DBFD73541C5966391B97EA73D744B0E34B9DF59ED0158063E39C09A5A055371EDF7A5441
    NONCE    = 1B7EC5E548E8AAA92EC77097CA9551C9783CE682CA18FB1EDBD9F1E50BC382DB8AB39496C8EE423F8CA105CBBA7B6588
    Sign_R   = 871E6EA4DDC5432CDDAA60FD7F055472D3C4DD41A5BFB26709E88C311A97093599A7C8F55B3974C19E4F5A7BFC1DD2AC
    SIGN_S   = 3E5552DE6403350EE70AD74E4B854D2DC4126BBF9C153A5D7A07BD4B85D06E45F850920E898FB7D34F80796DAE29365C
    IV       = 3401CEFAE20A737649073AC1A351E32926DB9ED0DB6B1CFFAB0493DAAFB93DDDD83EDEA28A803D0D003B2633B9D0F1BF
*/

void ecc_keygen_kvflow(uint8_t seed_kv_id, uint8_t privkey_kv_id, uint32_t ecc_nonce[12], uint32_t ecc_iv[12], uint32_t expected_pubkey_x[12], uint32_t expected_pubkey_y[12]){
    uint8_t seed_inject_cmd;
    uint8_t offset;
    volatile uint32_t * reg_ptr;
    volatile uint32_t * pubkey_x_reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_PUBKEY_X_0;
    volatile uint32_t * pubkey_y_reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_PUBKEY_Y_0;

    uint32_t ecc_pubkey_x [12];
    uint32_t ecc_pubkey_y [12];

    //inject seed to kv key reg (in RTL)
    printf("Inject SEED into ECC\n");
    seed_inject_cmd = 0x80 + (seed_kv_id & 0x7);
    printf("%c", seed_inject_cmd);

    // wait for ECC to be ready
    while((lsu_read_32((uint32_t *) CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    // Program ECC_SEED Read with 12 dwords from seed_kv_id
    lsu_write_32((uint32_t *) CLP_ECC_REG_ECC_KV_RD_SEED_CTRL, (ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK |
                                                                ((seed_kv_id & 0x7) << ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW)));

    // Check that ECC SEED is loaded
    while((lsu_read_32((uint32_t *) CLP_ECC_REG_ECC_KV_RD_SEED_STATUS) & ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_MASK) == 0);

    // set privkey DEST to write
    lsu_write_32((uint32_t *) CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, (ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                                                                ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK |
                                                                ((privkey_kv_id & 0x7) << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW)));

    
    // Write ECC nonce
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_NONCE_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_NONCE_11) {
        *reg_ptr++ = ecc_nonce[offset++];
    }

    // Write ECC IV
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
        *reg_ptr++ = ecc_iv[offset++];
    }

    printf("ECC KEYGEN\n");
    // Enable ECC KEYGEN core
    lsu_write_32((uint32_t *) CLP_ECC_REG_ECC_CTRL, ECC_CMD_KEYGEN);

    printf("Wait for ECC KEYGEN\n");
    // wait for ECC KEYGEN process to be done
    while((lsu_read_32((uint32_t *) CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_VALID_MASK) == 0);
        
    printf("Wait for KV write\n");
    // check dest done
    while((lsu_read_32((uint32_t *) CLP_ECC_REG_ECC_KV_WR_PKEY_STATUS) & ECC_REG_ECC_KV_WR_PKEY_STATUS_VALID_MASK) == 0);

    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_PUBKEY_X_0;
    // Read the data back from ECC register
    printf("Load PUBKEY_X data from ECC\n");
    offset = 0;
    while (pubkey_x_reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_11) {
        ecc_pubkey_x[offset] = *pubkey_x_reg_ptr;
        if (ecc_pubkey_x[offset] != expected_pubkey_x[offset]) {
            printf("At offset [%d], ecc_pubkey_x data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", ecc_pubkey_x[offset]);
            printf("Expected data: 0x%x\n", expected_pubkey_x[offset]);
            printf("%c", fail_cmd);
            while(1);
        } /*else {
            printf("[%d] :: 0x%x matches 0x%x\n", offset, ecc_pubkey_x[offset], expected_pubkey_x[offset]);
        }*/
        pubkey_x_reg_ptr++;
        offset++;
    }

    printf("Load PUBKEY_Y data from ECC\n");
    offset = 0;
    while (pubkey_y_reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_11) {
        ecc_pubkey_y[offset] = *pubkey_y_reg_ptr;
        if (ecc_pubkey_y[offset] != expected_pubkey_y[offset]) {
            printf("At offset [%d], ecc_pubkey_y data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", ecc_pubkey_y[offset]);
            printf("Expected data: 0x%x\n", expected_pubkey_y[offset]);
            printf("%c", fail_cmd);
            while(1);
        } /*else {
            printf("[%d] :: 0x%x matches 0x%x\n", offset, ecc_pubkey_y[offset], expected_pubkey_y[offset]);
        }*/
        pubkey_y_reg_ptr++;
        offset++;
    }
    
}


void ecc_signing_kvflow(uint8_t privkey_kv_id, uint32_t ecc_msg[12], uint32_t ecc_iv[12], uint32_t expected_sign_r[12], uint32_t expected_sign_s[12]){
    uint8_t offset;
    volatile uint32_t * reg_ptr;
    volatile uint32_t * sign_r_reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_SIGN_R_0;
    volatile uint32_t * sign_s_reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_SIGN_S_0;

    uint32_t ecc_sign_r [12];
    uint32_t ecc_sign_s [12];

    //inject privkey to kv key reg
    //suppose privkey is stored by ecc_keygen

    // wait for ECC to be ready
    while((lsu_read_32((uint32_t *) CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    // Program ECC_PRIVKEY Read with 12 dwords from privkey_kv_id
    lsu_write_32((uint32_t *) CLP_ECC_REG_ECC_KV_RD_PKEY_CTRL, (ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_MASK |
                                                                ((privkey_kv_id & 0x7) << ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_LOW)));

    // Check that ECC PRIVKEY is loaded
    while((lsu_read_32((uint32_t *) CLP_ECC_REG_ECC_KV_RD_PKEY_STATUS) & ECC_REG_ECC_KV_RD_PKEY_STATUS_VALID_MASK) == 0);
    

    
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
    lsu_write_32((uint32_t *) CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING);
    
    // wait for ECC SIGNING process to be done
    while((lsu_read_32((uint32_t *) CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_VALID_MASK) == 0);
    
    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_SIGN_R_0;
    // Read the data back from ECC register
    printf("Load SIGN_R data from ECC\n");
    offset = 0;
    while (sign_r_reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_11) {
        ecc_sign_r[offset] = *sign_r_reg_ptr;
        if (ecc_sign_r[offset] != expected_sign_r[offset]) {
            printf("At offset [%d], ecc_sign_r data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", ecc_sign_r[offset]);
            printf("Expected data: 0x%x\n", expected_sign_r[offset]);
            printf("%c", fail_cmd);
            while(1);
        } /*else {
            printf("[%d] :: 0x%x matches 0x%x\n", offset, ecc_sign_r[offset], expected_sign_r[offset]);
        }*/
        sign_r_reg_ptr++;
        offset++;
    }

    printf("Load SIGN_S data from ECC\n");
    offset = 0;
    while (sign_s_reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_11) {
        ecc_sign_s[offset] = *sign_s_reg_ptr;
        if (ecc_sign_s[offset] != expected_sign_s[offset]) {
            printf("At offset [%d], ecc_sign_s data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", ecc_sign_s[offset]);
            printf("Expected data: 0x%x\n", expected_sign_s[offset]);
            printf("%c", fail_cmd);
            while(1);
        } /*else {
            printf("[%d] :: 0x%x matches 0x%x\n", offset, ecc_sign_s[offset], expected_sign_s[offset]);
        }*/
        sign_s_reg_ptr++;
        offset++;
    }

}

void ecc_kvflow_test(uint8_t seed_kv_id, uint32_t privkey_kv_id){
    uint32_t ecc_msg[] =           {0xC8F518D4,
                                    0xF3AA1BD4,
                                    0x6ED56C1C,
                                    0x3C9E16FB,
                                    0x800AF504,
                                    0xDB988435,
                                    0x48C5F623,
                                    0xEE115F73,
                                    0xD4C62ABC,
                                    0x06D303B5,
                                    0xD90D9A17,
                                    0x5087290D};

    uint32_t expected_pubkey_x[] = {0xD79C6D97,
                                    0x2B34A1DF,
                                    0xC916A7B6,
                                    0xE0A99B6B,
                                    0x5387B34D,
                                    0xA2187607,
                                    0xC1AD0A4D,
                                    0x1A8C2E41,
                                    0x72AB5FA5,
                                    0xD9AB58FE,
                                    0x45E43F56,
                                    0xBBB66BA4};

    uint32_t expected_pubkey_y[] = {0x5A736393,
                                    0x2B06B4F2,
                                    0x23BEF0B6,
                                    0x0A639026,
                                    0x5112DBBD,
                                    0x0AAE67FE,
                                    0xF26B465B,
                                    0xE935B48E,
                                    0x451E68D1,
                                    0x6F1118F2,
                                    0xB32B4C28,
                                    0x608749ED};

    uint32_t ecc_nonce[] =         {0x1B7EC5E5,
                                    0x48E8AAA9,
                                    0x2EC77097,
                                    0xCA9551C9,
                                    0x783CE682,
                                    0xCA18FB1E,
                                    0xDBD9F1E5,
                                    0x0BC382DB,
                                    0x8AB39496,
                                    0xC8EE423F,
                                    0x8CA105CB,
                                    0xBA7B6588};

    uint32_t expected_sign_r[] =   {0x871E6EA4,
                                    0xDDC5432C,
                                    0xDDAA60FD,
                                    0x7F055472,
                                    0xD3C4DD41,
                                    0xA5BFB267,
                                    0x09E88C31,
                                    0x1A970935,
                                    0x99A7C8F5,
                                    0x5B3974C1,
                                    0x9E4F5A7B,
                                    0xFC1DD2AC};

    uint32_t expected_sign_s[] =   {0x3E5552DE,
                                    0x6403350E,
                                    0xE70AD74E,
                                    0x4B854D2D,
                                    0xC4126BBF,
                                    0x9C153A5D,
                                    0x7A07BD4B,
                                    0x85D06E45,
                                    0xF850920E,
                                    0x898FB7D3,
                                    0x4F80796D,
                                    0xAE29365C};

    
    uint32_t ecc_iv[] =            {0x3401CEFA,
                                    0xE20A7376,
                                    0x49073AC1,
                                    0xA351E329,
                                    0x26DB9ED0,
                                    0xDB6B1CFF,
                                    0xAB0493DA,
                                    0xAFB93DDD,
                                    0xD83EDEA2,
                                    0x8A803D0D,
                                    0x003B2633,
                                    0xB9D0F1BF};

    ecc_keygen_kvflow(seed_kv_id, privkey_kv_id, ecc_nonce, ecc_iv, expected_pubkey_x, expected_pubkey_y);

    ecc_signing_kvflow(privkey_kv_id, ecc_msg, ecc_iv, expected_sign_r, expected_sign_s);
}


void main() {
    printf("----------------------------------\n");
    printf(" KV Smoke Test With ECC flow !!\n");
    printf("----------------------------------\n");

    //Call interrupt init
    //init_interrupts();

    uint8_t seed_kv_id = 0x1;
    uint8_t privkey_kv_id = 0x2;
    
    //privkey_kv_id = rand() % 8;

    ecc_kvflow_test(seed_kv_id, privkey_kv_id);
    

    printf("%c",0xff); //End the test
    
}