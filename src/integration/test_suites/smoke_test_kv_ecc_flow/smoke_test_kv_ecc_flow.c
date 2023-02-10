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
    MSG      = A5E390D7271F2A323851FC869E7AAA9EF8F42FBF49D88D37E6CCF5968F14852CAC76E9519AFBFD37C611709549172AE9
    PRIVKEY  = 4726C8664D2058CECD9826C54E8DF046AAF35131199B8169F96DBB87EE7F2D6E2B7DD5BC9CD68E926773F62D4D4F0772
    PUBKEY_X = 0C66B5F38178FCFC1F41F8E0715FB25DC819BBF0B378C70CB9C9119EC13B86B13766A7C79C5299EF0B89D8F269CD4FE9
    PUBKEY_Y = E4A1E6C8E4F7FECD8FDBC01AC87DC4F71BA5F3271C6AFEF30866F08B0EBF4CA5A424636C93D66C70F5978CC21B95DBB1
    SEED     = 7F3654EFC470468CB14662D5B27C588758C68F3065623694C34A57405AE03CF401786957C5B89983293586D28F12482B
    Sign_R   = 2C13C633B28A53CB46AB6C8BCA5ADE24EE2F6E9BF81634944E458F838FD620C0DB2B19157C47BA87E9602C4E69FCA51D
    SIGN_S   = 070013921E4051308A47457CE14FC33392330A87456B3F542CCA42A0DE04E15F4A0D7C6C0B7FC91DA9FF028949B031BE
    IV       = 9A2FF93FA143DC40AF213DF8F9F622CE596AE0CE1C5D8A8D5D0AE1CDC97FBFB700698B307BD85798E24DE0566DE1B892
*/

void ecc_keygen_kvflow(uint8_t seed_kv_id, uint8_t privkey_kv_id, uint32_t ecc_iv[12], uint32_t expected_pubkey_x[12], uint32_t expected_pubkey_y[12]){
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
                                                                ((seed_kv_id & 0x7) << ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW) |
                                                                (0xB << ECC_REG_ECC_KV_RD_SEED_CTRL_ENTRY_DATA_SIZE_LOW)));

    // Check that ECC SEED is loaded
    while((lsu_read_32((uint32_t *) CLP_ECC_REG_ECC_KV_RD_SEED_STATUS) & ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_MASK) == 0);

    // set privkey DEST to write
    lsu_write_32((uint32_t *) CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, (ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                                                                ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK |
                                                                ((privkey_kv_id & 0x7) << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW)));

    
    // Write ECC IV
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
        *reg_ptr++ = ecc_iv[offset++];
    }

    printf("ECC KEYGEN\n");
    // Enable ECC KEYGEN core
    lsu_write_32((uint32_t *) CLP_ECC_REG_ECC_CTRL, 0x1);

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
                                                                ((privkey_kv_id & 0x7) << ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_LOW) |
                                                                (0xB << ECC_REG_ECC_KV_RD_PKEY_CTRL_ENTRY_DATA_SIZE_LOW)));

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
    lsu_write_32((uint32_t *) CLP_ECC_REG_ECC_CTRL, 0x2);
    
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
    uint32_t ecc_msg[] =   {0xA5E390D7,
                            0X271F2A32,
                            0X3851FC86,
                            0X9E7AAA9E,
                            0XF8F42FBF,
                            0X49D88D37,
                            0XE6CCF596,
                            0X8F14852C,
                            0XAC76E951,
                            0X9AFBFD37,
                            0XC6117095,
                            0X49172AE9};
    
    uint32_t ecc_iv[] =    {0x9A2FF93F,
                            0xA143DC40,
                            0xAF213DF8,
                            0xF9F622CE,
                            0x596AE0CE,
                            0x1C5D8A8D,
                            0x5D0AE1CD,
                            0xC97FBFB7,
                            0x00698B30,
                            0x7BD85798,
                            0xE24DE056,
                            0x6DE1B892};

    uint32_t expected_pubkey_x[] = {0x0C66B5F3,
                                    0x8178FCFC,
                                    0x1F41F8E0,
                                    0x715FB25D,
                                    0xC819BBF0,
                                    0xB378C70C,
                                    0xB9C9119E,
                                    0xC13B86B1,
                                    0x3766A7C7,
                                    0x9C5299EF,
                                    0x0B89D8F2,
                                    0x69CD4FE9};

    uint32_t expected_pubkey_y[] = {0xE4A1E6C8,
                                    0xE4F7FECD,
                                    0x8FDBC01A,
                                    0xC87DC4F7,
                                    0x1BA5F327,
                                    0x1C6AFEF3,
                                    0x0866F08B,
                                    0x0EBF4CA5,
                                    0xA424636C,
                                    0x93D66C70,
                                    0xF5978CC2,
                                    0x1B95DBB1};

    uint32_t expected_sign_r[] =   {0x2C13C633,
                                    0xB28A53CB,
                                    0x46AB6C8B,
                                    0xCA5ADE24,
                                    0xEE2F6E9B,
                                    0xF8163494,
                                    0x4E458F83,
                                    0x8FD620C0,
                                    0xDB2B1915,
                                    0x7C47BA87,
                                    0xE9602C4E,
                                    0x69FCA51D};

    uint32_t expected_sign_s[] =   {0x07001392,
                                    0x1E405130,
                                    0x8A47457C,
                                    0xE14FC333,
                                    0x92330A87,
                                    0x456B3F54,
                                    0x2CCA42A0,
                                    0xDE04E15F,
                                    0x4A0D7C6C,
                                    0x0B7FC91D,
                                    0xA9FF0289,
                                    0x49B031BE};

    ecc_keygen_kvflow(seed_kv_id, privkey_kv_id, ecc_iv, expected_pubkey_x, expected_pubkey_y);

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