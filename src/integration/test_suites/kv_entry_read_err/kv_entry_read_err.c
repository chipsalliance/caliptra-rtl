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
#include "printf.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {
    VPRINTF(LOW, "---------------------------------\n");
    VPRINTF(LOW, " Read KV entries and expect not success !!\n");
    VPRINTF(LOW, "---------------------------------\n");

    int num_keys = 24;

    SEND_STDOUT_CTRL(0xcd); //Enable kv error injection mode

    VPRINTF(LOW, "Testing ECC KV reads\n");
    for (int i = 0; i < num_keys; i++) {
        // Program ECC_PRIVKEY Read
        lsu_write_32(CLP_ECC_REG_ECC_KV_RD_PKEY_CTRL, (ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_MASK |
                                                      ((i << ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_LOW) & ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_MASK)));

        // Check that ECC PRIVKEY is loaded
        while((lsu_read_32(CLP_ECC_REG_ECC_KV_RD_PKEY_STATUS) & ECC_REG_ECC_KV_RD_PKEY_STATUS_VALID_MASK) == 0);

        // Check that we got a KV error
        if ( (lsu_read_32(CLP_ECC_REG_ECC_KV_RD_PKEY_STATUS) & ECC_REG_ECC_KV_RD_PKEY_STATUS_ERROR_MASK) == 0){
            VPRINTF(ERROR, "ERROR: Expected ECC PKEY KV read entry %d error not detected!\n", i);
            SEND_STDOUT_CTRL(0x1); // Indicate failure
            while(1);
        }

        // Program ECC SEED Read
        lsu_write_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL, (ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK |
                                                      ((num_keys-1-i << ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW) & ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_MASK)));

        // Check that ECC SEED is loaded
        while((lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_STATUS) & ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_MASK) == 0);

        // Check that we got a KV error
        if ( (lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_STATUS) & ECC_REG_ECC_KV_RD_SEED_STATUS_ERROR_MASK) == 0){
            VPRINTF(ERROR, "ERROR: Expected ECC SEED KV read entry %d error not detected!\n", i);
            SEND_STDOUT_CTRL(0x1); // Indicate failure
            while(1);
        }
        // Zeroize ECC engine
        lsu_write_32(CLP_ECC_REG_ECC_CTRL, (1 << ECC_REG_ECC_CTRL_ZEROIZE_LOW) & ECC_REG_ECC_CTRL_ZEROIZE_MASK);

        // wait for ECC to be ready
        while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
    }

    VPRINTF(LOW, "Testing HMAC KV reads\n");
    for (int i = 0; i < num_keys; i++) {
        // Program HMAC KEY Read
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_CTRL, (HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                      ((i << HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_KEY_CTRL_READ_ENTRY_MASK)));

        // Check that HMAC KEY is loaded
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_VALID_MASK) == 0);

        // Check that we got a KV error
        if ( (lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_KEY_STATUS) & HMAC_REG_HMAC512_KV_RD_KEY_STATUS_ERROR_MASK) == 0){
            VPRINTF(ERROR, "ERROR: Expected HMAC KEY KV read entry %d error not detected!\n", i);
            SEND_STDOUT_CTRL(0x1); // Indicate failure
            while(1);
        }

        // Program HMAC BLOCK Read
        lsu_write_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL, (HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_EN_MASK |
                                                      ((num_keys-1-i << HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW) & HMAC_REG_HMAC512_KV_RD_BLOCK_CTRL_READ_ENTRY_MASK)));

        // Check that HMAC BLOCK is loaded
        while((lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS) & HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_VALID_MASK) == 0);

        // Check that we got a KV error
        if ( (lsu_read_32(CLP_HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS) & HMAC_REG_HMAC512_KV_RD_BLOCK_STATUS_ERROR_MASK) == 0){
            VPRINTF(ERROR, "ERROR: Expected EHMAC BLOCK KV read entry %d error not detected!\n", num_keys-1-i);
            SEND_STDOUT_CTRL(0x1); // Indicate failure
            while(1);
        }
        // Zeroize HMAC engine
        lsu_write_32(CLP_HMAC_REG_HMAC512_CTRL, (1 << HMAC_REG_HMAC512_CTRL_ZEROIZE_LOW) & HMAC_REG_HMAC512_CTRL_ZEROIZE_MASK);
    }

    VPRINTF(LOW, "Testing AES KV reads\n");
    for (int i = 0; i < num_keys; i++) {
        // Program AES KEY Read
        lsu_write_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL, (AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                      ((i << AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_MASK)));

        // Check that AES KEY is loaded
        while((lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS) & AES_CLP_REG_AES_KV_RD_KEY_STATUS_VALID_MASK) == 0);

        // Check that we got a KV error
        if ( (lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS) & AES_CLP_REG_AES_KV_RD_KEY_STATUS_ERROR_MASK) == 0){
            VPRINTF(ERROR, "ERROR: Expected AES KEY KV read entry %d error not detected!\n", i);
            SEND_STDOUT_CTRL(0x1); // Indicate failure
            while(1);
        }
    }

    VPRINTF(LOW, "Testing MLDSA KV reads\n");
    for (int i = 0; i < num_keys; i++) {
        // Program MLDSA SEED Read
        lsu_write_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_CTRL, (ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_EN_MASK |
                                                      ((i << ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_MASK)));

        // Check that MLDSA SEED is loaded
        while((lsu_read_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_STATUS) & ABR_REG_KV_MLDSA_SEED_RD_STATUS_VALID_MASK) == 0);

        // Check that we got a KV error
        if ( (lsu_read_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_STATUS) & ABR_REG_KV_MLDSA_SEED_RD_STATUS_ERROR_MASK) == 0){
            VPRINTF(ERROR, "ERROR: Expected MLDSA SEED KV read entry %d error not detected!\n", i);
            SEND_STDOUT_CTRL(0x1); // Indicate failure
            while(1);
        }
        // Zeroize ABR engine
        lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, (1 << ABR_REG_MLDSA_CTRL_ZEROIZE_LOW) & ABR_REG_MLDSA_CTRL_ZEROIZE_MASK);

        // wait for ABR to be ready
        while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);
    }

    VPRINTF(LOW, "Testing MLKEM KV reads\n");
    for (int i = 0; i < num_keys; i++) {
        // Program MLKEM SEED Read
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_CTRL, (ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_MASK |
                                                      ((i << ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_MASK)));

        // Check that MLKEM SEED is loaded
        while((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_STATUS) & ABR_REG_KV_MLKEM_SEED_RD_STATUS_VALID_MASK) == 0);

        // Check that we got a KV error
        if ( (lsu_read_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_STATUS) & ABR_REG_KV_MLKEM_SEED_RD_STATUS_ERROR_MASK) == 0){
            VPRINTF(ERROR, "ERROR: Expected MLKEM SEED KV read entry %d error not detected!\n", i);
            SEND_STDOUT_CTRL(0x1); // Indicate failure
            while(1);
        }
        
        // Program MLKEM MSG Read
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_MSG_RD_CTRL, (ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_EN_MASK |
                                                      ((num_keys-1-i << ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_MASK)));

        // Check that MLKEM MSG is loaded
        while((lsu_read_32(CLP_ABR_REG_KV_MLKEM_MSG_RD_STATUS) & ABR_REG_KV_MLKEM_MSG_RD_STATUS_VALID_MASK) == 0);

        // Check that we got a KV error
        if ( (lsu_read_32(CLP_ABR_REG_KV_MLKEM_MSG_RD_STATUS) & ABR_REG_KV_MLKEM_MSG_RD_STATUS_ERROR_MASK) == 0){
            VPRINTF(ERROR, "ERROR: Expected MLKEM MSG KV read entry %d error not detected!\n", num_keys-1-i);
            SEND_STDOUT_CTRL(0x1); // Indicate failure
            while(1);
        }
        // Zeroize ABR engine
        lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, (1 << ABR_REG_MLKEM_CTRL_ZEROIZE_LOW) & ABR_REG_MLKEM_CTRL_ZEROIZE_MASK);

        // wait for ABR to be ready
        while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);
    }

    SEND_STDOUT_CTRL(0xcd); //Disable kv error injection mode

    SEND_STDOUT_CTRL(0xff); //End the test
    
}


