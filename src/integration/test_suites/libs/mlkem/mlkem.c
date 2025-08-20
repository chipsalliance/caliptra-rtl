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
#include "printf.h"
#include "mlkem.h"
#include "caliptra_isr.h"
#include <stdint.h>
#include <string.h>

extern volatile caliptra_intr_received_s cptra_intr_rcv;

void wait_for_mlkem_intr(){
    VPRINTF(LOW, "[MLKEM] Waiting for interrupt\n");
    while((cptra_intr_rcv.abr_error == 0) & (cptra_intr_rcv.abr_notif == 0)){
        __asm__ volatile ("wfi"); // "Wait for interrupt"
        // Sleep during MLKEM operation to allow ISR to execute and show idle time in sims
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    };
    VPRINTF(LOW, "Received MLKEM notif/ err intr with status = %d/ %d\n", cptra_intr_rcv.abr_notif, cptra_intr_rcv.abr_error);
}

void mlkem_zeroize(){
    VPRINTF(LOW, "[MLKEM] Starting zeroize\n");
    lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, (1 << ABR_REG_MLKEM_CTRL_ZEROIZE_LOW) & ABR_REG_MLKEM_CTRL_ZEROIZE_MASK);

    // wait for MLKEM to be ready
    VPRINTF(LOW, "[MLKEM] Waiting for ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

}

void write_mlkem_reg(volatile uint32_t *base_addr, uint32_t *data, uint32_t size) {
    for (uint32_t i = 0; i < size; i++) {
        base_addr[i] = data[i];
    }
}

void mlkem_keygen_check(mlkem_seed seed, uint32_t entropy[ABR_ENTROPY_SIZE], uint32_t encaps_key[MLKEM_EK_SIZE], uint32_t decaps_key[MLKEM_DK_SIZE])
{
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;
    
    // wait for ABR to be ready
    VPRINTF(LOW, "[MLKEM KeyGen] Waiting for ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

    //Program mlkem seed
    if(seed.kv_intf){
        // Program MLKEM_SEED Read with 12 dwords from seed_kv_id
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_CTRL, (ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_MASK |
                                                          ((seed.kv_id << ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_MASK)));

        VPRINTF(LOW, "[MLKEM KeyGen] Try to Overwrite seed d data\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_7) {
             *reg_ptr++ = 0;
        }

        VPRINTF(LOW, "[MLKEM KeyGen] Try to Overwrite seed z data\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_7) {
             *reg_ptr++ = 0;
        }

         // Check that MLKEM SEED is loaded
         while((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_STATUS) & ABR_REG_KV_MLKEM_SEED_RD_STATUS_VALID_MASK) == 0);
     }
     else{
        write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_0, seed.data[0], MLKEM_SEED_SIZE);
        write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_0, seed.data[1], MLKEM_SEED_SIZE);
    }

    // Write MLKEM ENTROPY
    VPRINTF(LOW, "[MLKEM KeyGen] Writing entropy\n");
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, ABR_ENTROPY_SIZE);

    VPRINTF(LOW, "[MLKEM KeyGen] Sending command\n");
    // Enable MLKEM KEYGEN flow
    lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_KEYGEN);

    // // wait for MLKEM KEYGEN process to be done
    wait_for_mlkem_intr();
    
    // Read the data back from MLKEM register
    VPRINTF(LOW, "[MLKEM KeyGen] Checking encaps key\n");
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_ENCAPS_KEY_BASE_ADDR;
    offset = 0;
    while (offset < MLKEM_EK_SIZE) {
        actual_data = *reg_ptr;
        if (actual_data != encaps_key[offset]) {
            VPRINTF(LOW, "At offset [%d], mlkem_encaps_key data mismatch!\n", offset);
            VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
            VPRINTF(LOW, "Expected data: 0x%x\n", encaps_key[offset]);
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }
        
    if(!seed.kv_intf){
        VPRINTF(LOW, "[MLKEM KeyGen] Checking decaps key\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_DECAPS_KEY_BASE_ADDR;
        offset = 0;
        while (offset < MLKEM_DK_SIZE) {
            actual_data = *reg_ptr;
            if (actual_data != decaps_key[offset]) {
                VPRINTF(LOW, "At offset [%d], mlkem_decaps_key data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", decaps_key[offset]);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }
    
}

void mlkem_keygen_flow(mlkem_seed seed, uint32_t entropy[ABR_ENTROPY_SIZE], uint32_t encaps_key[MLKEM_EK_SIZE], uint32_t decaps_key[MLKEM_DK_SIZE]) {
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;
    
    // wait for ABR to be ready
    VPRINTF(LOW, "[MLKEM KeyGen] Waiting for ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

    //Program mlkem seed
    if(seed.kv_intf){
        // Program MLKEM_SEED Read with 12 dwords from seed_kv_id
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_CTRL, (ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_MASK |
                                                          ((seed.kv_id << ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_MASK)));

        VPRINTF(LOW, "[MLKEM KeyGen] Try to Overwrite seed d data\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_7) {
            *reg_ptr++ = 0;
        }

        VPRINTF(LOW, "[MLKEM KeyGen] Try to Overwrite seed z data\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_7) {
            *reg_ptr++ = 0;
        }

        // Check that MLKEM SEED is loaded
        while((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_STATUS) & ABR_REG_KV_MLKEM_SEED_RD_STATUS_VALID_MASK) == 0);

        VPRINTF(LOW, "[MLKEM KeyGen] Check that SEED_D api has 0s\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_7) {
            actual_data = *reg_ptr;
            if (actual_data != 0x0) {
                VPRINTF(LOW, "At offset [%d], mlkem_seed_d data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", 0x0);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            *reg_ptr++;
            offset++;
        }

        VPRINTF(LOW, "[MLKEM KeyGen] Check that SEED_Z api has 0s\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_7) {
            actual_data = *reg_ptr;
            if (actual_data != 0x0) {
                VPRINTF(LOW, "At offset [%d], mlkem_seed_z data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", 0x0);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            *reg_ptr++;
            offset++;
        }
     }
     else{
        write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_0, seed.data[0], MLKEM_SEED_SIZE);
        write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_0, seed.data[1], MLKEM_SEED_SIZE);
    }

    // Write MLKEM ENTROPY
    VPRINTF(LOW, "[MLKEM KeyGen] Writing entropy\n");
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, ABR_ENTROPY_SIZE);

    VPRINTF(LOW, "[MLKEM KeyGen] Sending command\n");
    // Enable MLKEM KEYGEN flow
    lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_KEYGEN);

    // // wait for MLKEM KEYGEN process to be done
    wait_for_mlkem_intr();
    
    // Read the data back from MLKEM register
    VPRINTF(LOW, "[MLKEM KeyGen] Read Encaps Key\n");
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_ENCAPS_KEY_BASE_ADDR;
    offset = 0;
    while (offset < MLKEM_EK_SIZE) {
        encaps_key[offset] = *reg_ptr;
        reg_ptr++;
        offset++;
    }
        
    if(!seed.kv_intf){
        VPRINTF(LOW, "[MLKEM KeyGen] Read Decaps Key\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_DECAPS_KEY_BASE_ADDR;
        offset = 0;
        while (offset < MLKEM_DK_SIZE) {
            decaps_key[offset]= *reg_ptr;
            reg_ptr++;
            offset++;
        }
    } else {
        VPRINTF(LOW, "[MLKEM KeyGen] Check that DK api has 0s\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_DECAPS_KEY_BASE_ADDR;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_DECAPS_KEY_END_ADDR) {
            actual_data = *reg_ptr;
            if (actual_data != 0x0) {
                VPRINTF(LOW, "At offset [%d], mlkem_dk data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", 0x0);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            *reg_ptr++;
            offset++;
        }
    }
}

void mlkem_encaps_check(uint32_t encaps_key[MLKEM_EK_SIZE], mlkem_msg msg, uint32_t entropy[ABR_ENTROPY_SIZE], uint32_t ciphertext[MLKEM_CIPHERTEXT_SIZE], mlkem_shared_key shared_key)
{
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;

    VPRINTF(LOW, "[MLKEM Encaps] Waiting for ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

    // Program MLKEM Encaps Key
    VPRINTF(LOW, "[MLKEM Encaps] Writing encaps key\n");
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_ENCAPS_KEY_BASE_ADDR, encaps_key, MLKEM_EK_SIZE);

    // Program MLKEM MSG
    if(msg.kv_intf){
        // Program keyvault msg read
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_MSG_RD_CTRL, (ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_EN_MASK |
                                                          ((msg.kv_id << ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_MASK)));

        VPRINTF(LOW, "[MLKEM Encaps] Try to Overwrite msg\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_MSG_BASE_ADDR;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_MSG_END_ADDR) {
            *reg_ptr++ = 0;
        }

        while((lsu_read_32(CLP_ABR_REG_KV_MLKEM_MSG_RD_STATUS) & ABR_REG_KV_MLKEM_MSG_RD_STATUS_VALID_MASK) == 0);

        VPRINTF(LOW, "[MLKEM Encaps] Check that MSG api has 0s\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_MSG_BASE_ADDR;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_MSG_END_ADDR) {
            actual_data = *reg_ptr;
            if (actual_data != 0x0) {
                VPRINTF(LOW, "At offset [%d], mlkem_msg data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", 0x0);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            *reg_ptr++;
            offset++;
        }
     }
     else{
        write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_MSG_BASE_ADDR, msg.data, MLKEM_MSG_SIZE);
    }

    // Write MLKEM ENTROPY
    VPRINTF(LOW, "[MLKEM Encaps] Writing entropy\n");
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, ABR_ENTROPY_SIZE);

    // Enable MLKEM ENCAPS flow
    VPRINTF(LOW, "[MLKEM Encaps] Sending command\n");
    lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_ENCAPS);

    // wait for MLKEM ENCAPS process to be done
    wait_for_mlkem_intr();

    // Read the data back from MLKEM register
    VPRINTF(LOW, "[MLKEM Encaps] Check Ciphertext\n");
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_CIPHERTEXT_BASE_ADDR;
    offset = 0;
    while (offset < MLKEM_CIPHERTEXT_SIZE) {
        actual_data = *reg_ptr;
        if (actual_data != ciphertext[offset]) {
            VPRINTF(LOW, "At offset [%d], mlkem_ciphertext data mismatch!\n", offset);
            VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
            VPRINTF(LOW, "Expected data: 0x%x\n", ciphertext[offset]);
            SEND_STDOUT_CTRL(fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

    if(!msg.kv_intf & !shared_key.kv_intf){
        // Read the shared key from MLKEM register
        VPRINTF(LOW, "[MLKEM Encaps] Check Shared Key\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SHARED_KEY_0;
        offset = 0;
        while (offset < MLKEM_SHAREDKEY_SIZE) {
            actual_data = *reg_ptr;
            if (actual_data != shared_key.data[offset]) {
                VPRINTF(LOW, "At offset [%d], mlkem_shared_key data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", shared_key.data[offset]);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    } else {
        if((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS) >> 2) == 0) {
            lsu_write_32(STDOUT, (shared_key.kv_id << 8) | 0xb3); //Check KV result in KV
        }

        // Read the shared key from MLKEM register
        VPRINTF(LOW, "[MLKEM Encaps] KV used, check Shared Key is 0\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SHARED_KEY_0;
        offset = 0;
        while (offset < MLKEM_SHAREDKEY_SIZE) {
            actual_data = *reg_ptr;
            if (actual_data != 0) {
                VPRINTF(LOW, "At offset [%d], mlkem_shared_key data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", 0x0);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }
}

void mlkem_encaps_flow(uint32_t encaps_key[MLKEM_EK_SIZE], mlkem_msg msg, uint32_t entropy[ABR_ENTROPY_SIZE], uint32_t ciphertext[MLKEM_CIPHERTEXT_SIZE], mlkem_shared_key shared_key, uint32_t* shared_key_o)
{
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;

    VPRINTF(LOW, "[MLKEM Encaps] Waiting for ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

    // Program MLKEM Encaps Key
    VPRINTF(LOW, "[MLKEM Encaps] Writing encaps key\n");
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_ENCAPS_KEY_BASE_ADDR, encaps_key, MLKEM_EK_SIZE);

    // Program MLKEM MSG
    if(msg.kv_intf){
        // Program keyvault msg read
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_MSG_RD_CTRL, (ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_EN_MASK |
                                                          ((msg.kv_id << ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_MSG_RD_CTRL_READ_ENTRY_MASK)));

        VPRINTF(LOW, "[MLKEM Encaps] Try to Overwrite msg\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_MSG_BASE_ADDR;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_MSG_END_ADDR) {
            *reg_ptr++ = 0;
        }

        // Check that MLKEM SEED is loaded
        while((lsu_read_32(CLP_ABR_REG_KV_MLKEM_MSG_RD_STATUS) & ABR_REG_KV_MLKEM_MSG_RD_STATUS_VALID_MASK) == 0);

        VPRINTF(LOW, "[MLKEM Encaps] Check that MSG api has 0s\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_MSG_BASE_ADDR;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_MSG_END_ADDR) {
            actual_data = *reg_ptr;
            if (actual_data != 0x0) {
                VPRINTF(LOW, "At offset [%d], mlkem_msg data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", 0x0);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            *reg_ptr++;
        }
     }
     else{
        write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_MSG_BASE_ADDR, msg.data, MLKEM_MSG_SIZE);
    }

    // Write MLKEM ENTROPY
    VPRINTF(LOW, "[MLKEM Encaps] Writing entropy\n");
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, ABR_ENTROPY_SIZE);

    //program KV destination for shared key
    //if we want to store the results into kv
    if (shared_key.kv_intf){
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL, ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_EN_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_AES_KEY_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK |
                                                      ((shared_key.kv_id << ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_LOW) & ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_MASK));
    }



    // Enable MLKEM ENCAPS flow
    VPRINTF(LOW, "[MLKEM Encaps] Sending Command\n");
    lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_ENCAPS);

    // wait for MLKEM ENCAPS process to be done
    wait_for_mlkem_intr();

    // Read the data back from MLKEM register
    VPRINTF(LOW, "[MLKEM Encaps] Read Ciphertext\n");
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_CIPHERTEXT_BASE_ADDR;
    offset = 0;
    while (offset < MLKEM_CIPHERTEXT_SIZE) {
        ciphertext[offset] = *reg_ptr;
        reg_ptr++;
        offset++;
    }

    if (shared_key.kv_intf) {
        if((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS) >> 2) == 0) {
            lsu_write_32(STDOUT, (shared_key.kv_id << 8) | 0xb3); //Check KV result in KV
        }
    }
    else if (!msg.kv_intf & !shared_key.kv_intf){
        // Read the shared key from MLKEM register
        VPRINTF(LOW, "[MLKEM Encaps] Read Shared Key\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SHARED_KEY_0;
        offset = 0;
        while (offset < MLKEM_SHAREDKEY_SIZE) {
            shared_key_o[offset] = *reg_ptr;
            reg_ptr++;
            offset++;
        }
    } else {
        // Read the shared key from MLKEM register
        VPRINTF(LOW, "[MLKEM Encaps] KV used, check Shared Key is 0\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SHARED_KEY_0;
        offset = 0;
        while (offset < MLKEM_SHAREDKEY_SIZE) {
            actual_data = *reg_ptr;
            if (actual_data != 0) {
                VPRINTF(LOW, "At offset [%d], mlkem_shared_key data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", 0x0);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }
}

void mlkem_decaps_check(uint32_t decaps_key[MLKEM_DK_SIZE], uint32_t ciphertext[MLKEM_CIPHERTEXT_SIZE], uint32_t entropy[ABR_ENTROPY_SIZE], mlkem_shared_key shared_key)
{
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;

    VPRINTF(LOW, "[MLKEM Decaps] Waiting for ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

    // Program MLKEM Decaps Key
    VPRINTF(LOW, "[MLKEM Decaps] Writing decaps key\n");
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_DECAPS_KEY_BASE_ADDR, decaps_key, MLKEM_DK_SIZE);

    // Program MLKEM Ciphertext
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_CIPHERTEXT_BASE_ADDR, ciphertext, MLKEM_CIPHERTEXT_SIZE);

    // Write MLKEM ENTROPY
    VPRINTF(LOW, "[MLKEM Decaps] Writing entropy\n");
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, ABR_ENTROPY_SIZE);
    
    //program KV destination for shared key
    //if we want to store the results into kv
    if (shared_key.kv_intf){
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL, ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_EN_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_AES_KEY_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK |
                                                      ((shared_key.kv_id << ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_LOW) & ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_MASK));
    }

    // Enable MLKEM DECAPS flow
    VPRINTF(LOW, "[MLKEM Decaps] Sending command\n");
    lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_DECAPS);

    // wait for MLKEM DECAPS process to be done
    wait_for_mlkem_intr();

    // Read the shared key from MLKEM register
    if (!shared_key.kv_intf) {
        VPRINTF(LOW, "[MLKEM Decaps] Check Shared Key\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SHARED_KEY_0;
        offset = 0;
        while (offset < MLKEM_SHAREDKEY_SIZE) {
            actual_data = *reg_ptr;
            if (actual_data != shared_key.data[offset]) {
                VPRINTF(LOW, "At offset [%d], mlkem_shared_key data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", shared_key.data[offset]);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    } else {
        if((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS) >> 2) == 0) {
            lsu_write_32(STDOUT, (shared_key.kv_id << 8) | 0xb3); //Check KV result in KV
        }

        // Read the shared key from MLKEM register
        VPRINTF(LOW, "[MLKEM Decaps] KV used, check Shared Key is 0\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SHARED_KEY_0;
        offset = 0;
        while (offset < MLKEM_SHAREDKEY_SIZE) {
            actual_data = *reg_ptr;
            if (actual_data != 0) {
                VPRINTF(LOW, "At offset [%d], mlkem_shared_key data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", 0x0);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }
}

void mlkem_decaps_flow(uint32_t decaps_key[MLKEM_DK_SIZE], uint32_t ciphertext[MLKEM_CIPHERTEXT_SIZE], uint32_t entropy[ABR_ENTROPY_SIZE], mlkem_shared_key shared_key)
{
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;

    VPRINTF(LOW, "[MLKEM Decaps] Waiting for ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

    // Program MLKEM Decaps Key
    VPRINTF(LOW, "[MLKEM Decaps] Writing decaps key\n");
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_DECAPS_KEY_BASE_ADDR, decaps_key, MLKEM_DK_SIZE);

    // Program MLKEM Ciphertext
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_CIPHERTEXT_BASE_ADDR, ciphertext, MLKEM_CIPHERTEXT_SIZE);

    // Write MLKEM ENTROPY
    VPRINTF(LOW, "[MLKEM Decaps] Writing entropy\n");
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, ABR_ENTROPY_SIZE);
    
    //program KV destination for shared key
    //if we want to store the results into kv
    if (shared_key.kv_intf){
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL, ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_EN_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_AES_KEY_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK |
                                                      ((shared_key.kv_id << ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_LOW) & ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_MASK));
    }
    
    // Enable MLKEM DECAPS flow
    VPRINTF(LOW, "[MLKEM Decaps] Sending command\n");
    lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_DECAPS);

    // wait for MLKEM DECAPS process to be done
    wait_for_mlkem_intr();

    if (!shared_key.kv_intf) {
        // Read the shared key from MLKEM register
        VPRINTF(LOW, "[MLKEM Decaps] Read Shared Key\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SHARED_KEY_0;
        offset = 0;
        while (offset < MLKEM_SHAREDKEY_SIZE) {
            shared_key.data[offset] = *reg_ptr;
            reg_ptr++;
            offset++;
        }
    } else {
        if((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS) >> 2) == 0) {
            lsu_write_32(STDOUT, (shared_key.kv_id << 8) | 0xb3); //Check KV result in KV
        }

        // Read the shared key from MLKEM register
        VPRINTF(LOW, "[MLKEM KeyGen Decaps] KV used, check Shared Key is 0\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SHARED_KEY_0;
        offset = 0;
        while (offset < MLKEM_SHAREDKEY_SIZE) {
            actual_data = *reg_ptr;
            if (actual_data != 0) {
                VPRINTF(LOW, "At offset [%d], mlkem_shared_key data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", 0x0);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }
}

void mlkem_keygen_decaps_check(mlkem_seed seed, uint32_t ciphertext[MLKEM_CIPHERTEXT_SIZE], uint32_t entropy[ABR_ENTROPY_SIZE], mlkem_shared_key shared_key){

    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;

    VPRINTF(LOW, "[MLKEM KeyGen Decaps] Waiting for ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

    //Program mlkem seed
    if(seed.kv_intf){
        // Program MLKEM_SEED Read with 12 dwords from seed_kv_id
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_CTRL, (ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_MASK |
                                                          ((seed.kv_id << ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_MASK)));

        VPRINTF(LOW, "[MLKEM KeyGen Decaps] Try to Overwrite seed d\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_7) {
             *reg_ptr++ = 0;
        }

        VPRINTF(LOW, "[MLKEM KeyGen Decaps] Try to Overwrite seed z\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_7) {
             *reg_ptr++ = 0;
        }

         // Check that MLKEM SEED is loaded
         while((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_STATUS) & ABR_REG_KV_MLKEM_SEED_RD_STATUS_VALID_MASK) == 0);
     }
     else{
        write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_0, seed.data[0], MLKEM_SEED_SIZE);
        write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_0, seed.data[1], MLKEM_SEED_SIZE);
    }

    // Program MLKEM Ciphertext
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_CIPHERTEXT_BASE_ADDR, ciphertext, MLKEM_CIPHERTEXT_SIZE);

    // Write MLKEM ENTROPY
    VPRINTF(LOW, "[MLKEM KeyGen Decaps] Writing entropy\n");
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, ABR_ENTROPY_SIZE);
    
    //program KV destination for shared key
    //if we want to store the results into kv
    if (shared_key.kv_intf){
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL, ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_EN_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_AES_KEY_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK |
                                                      ((shared_key.kv_id << ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_LOW) & ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_MASK));
    }
    
    // Enable MLKEM KEYGEN DECAPS flow
    VPRINTF(LOW, "[MLKEM KeyGen Decaps] Sending command\n");
    lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_KEYGEN_DECAPS);

    // wait for MLKEM DECAPS process to be done
    wait_for_mlkem_intr();

    // Read the data back from MLKEM register
    if (shared_key.kv_intf) {
        if((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_STATUS) >> 2) == 0) {
            lsu_write_32(STDOUT, (shared_key.kv_id << 8) | 0xb3); //Check KV result in KV
        }
    }
    else if(!seed.kv_intf & !shared_key.kv_intf){
        // Read the shared key from MLKEM register
        VPRINTF(LOW, "[MLKEM KeyGen Decaps] Check Shared Key\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SHARED_KEY_0;
        offset = 0;
        while (offset < MLKEM_SHAREDKEY_SIZE) {
            actual_data = *reg_ptr;
            if (actual_data != shared_key.data[offset]) {
                VPRINTF(LOW, "At offset [%d], mlkem_shared_key data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", shared_key.data[offset]);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    } else {
        // Read the shared key from MLKEM register
        VPRINTF(LOW, "[MLKEM KeyGen Decaps] KV used, check Shared Key is 0\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SHARED_KEY_0;
        offset = 0;
        while (offset < MLKEM_SHAREDKEY_SIZE) {
            actual_data = *reg_ptr;
            if (actual_data != 0) {
                VPRINTF(LOW, "At offset [%d], mlkem_shared_key data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", 0x0);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }
}


void mlkem_keygen_decaps_flow(mlkem_seed seed, uint32_t ciphertext[MLKEM_CIPHERTEXT_SIZE], uint32_t entropy[ABR_ENTROPY_SIZE], mlkem_shared_key shared_key){

    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;

    VPRINTF(LOW, "[MLKEM KeyGen Decaps] Waiting for ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLKEM_STATUS) & ABR_REG_MLKEM_STATUS_READY_MASK) == 0);

    //Program mlkem seed
    if(seed.kv_intf){
        // Program MLKEM_SEED Read with 12 dwords from seed_kv_id
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_CTRL, (ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_EN_MASK |
                                                          ((seed.kv_id << ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLKEM_SEED_RD_CTRL_READ_ENTRY_MASK)));

        VPRINTF(LOW, "[MLKEM KeyGen Decaps] Try to Overwrite seed d\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_7) {
             *reg_ptr++ = 0;
        }

        VPRINTF(LOW, "[MLKEM KeyGen Decaps] Try to Overwrite seed z\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_7) {
             *reg_ptr++ = 0;
        }

         // Check that MLKEM SEED is loaded
         while((lsu_read_32(CLP_ABR_REG_KV_MLKEM_SEED_RD_STATUS) & ABR_REG_KV_MLKEM_SEED_RD_STATUS_VALID_MASK) == 0);
     }
     else{
        write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_SEED_D_0, seed.data[0], MLKEM_SEED_SIZE);
        write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_SEED_Z_0, seed.data[1], MLKEM_SEED_SIZE);
    }

    // Program MLKEM Ciphertext
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_MLKEM_CIPHERTEXT_BASE_ADDR, ciphertext, MLKEM_CIPHERTEXT_SIZE);

    // Write MLKEM ENTROPY
    VPRINTF(LOW, "[MLKEM KeyGen Decaps] Writing entropy\n");
    write_mlkem_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, ABR_ENTROPY_SIZE);
    
    //program KV destination for shared key
    //if we want to store the results into kv
    if (shared_key.kv_intf){
        lsu_write_32(CLP_ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL, ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_EN_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLDSA_SEED_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_AES_KEY_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_SEED_DEST_VALID_MASK |
                                                      ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_MLKEM_MSG_DEST_VALID_MASK |
                                                      ((shared_key.kv_id << ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_LOW) & ABR_REG_KV_MLKEM_SHAREDKEY_WR_CTRL_WRITE_ENTRY_MASK));
    }

    // Enable MLKEM KEYGEN DECAPS flow
    VPRINTF(LOW, "[MLKEM KeyGen Decaps] Sending command\n");
    lsu_write_32(CLP_ABR_REG_MLKEM_CTRL, MLKEM_CMD_KEYGEN_DECAPS);

    // wait for MLKEM DECAPS process to be done
    wait_for_mlkem_intr();

    // Read the data back from MLKEM register
    if(!seed.kv_intf){
        // Read the shared key from MLKEM register
        VPRINTF(LOW, "[MLKEM KeyGen Decaps] Read Shared Key\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SHARED_KEY_0;
        offset = 0;
        while (offset < MLKEM_SHAREDKEY_SIZE) {
            shared_key.data[offset] = *reg_ptr;
            reg_ptr++;
            offset++;
        }
    } else {
        // Read the shared key from MLKEM register
        VPRINTF(LOW, "[MLKEM KeyGen Decaps] KV used, check Shared Key is 0\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLKEM_SHARED_KEY_0;
        offset = 0;
        while (offset < MLKEM_SHAREDKEY_SIZE) {
            actual_data = *reg_ptr;
            if (actual_data != 0) {
                VPRINTF(LOW, "At offset [%d], mlkem_shared_key data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", 0x0);
                SEND_STDOUT_CTRL(fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }    
    }
}
