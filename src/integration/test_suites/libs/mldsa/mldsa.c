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
//#include "riscv_hw_if.h"
//#include <string.h>
//#include <stdint.h>
#include "printf.h"
#include "mldsa.h"
#include "caliptra_isr.h"

extern volatile caliptra_intr_received_s cptra_intr_rcv;

void wait_for_mldsa_intr(){
    VPRINTF(LOW, "MLDSA flow in progress...\n");
    while((cptra_intr_rcv.abr_error == 0) & (cptra_intr_rcv.abr_notif == 0)){
        __asm__ volatile ("wfi"); // "Wait for interrupt"
        // Sleep during MLDSA operation to allow ISR to execute and show idle time in sims
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    };
    //VPRINTF(LOW, "Received MLDSA error intr with status = %d\n", cptra_intr_rcv.abr_error);
    VPRINTF(LOW, "Received MLDSA notif/ err intr with status = %d/ %d\n", cptra_intr_rcv.abr_notif, cptra_intr_rcv.abr_error);
}

void mldsa_zeroize(){
    VPRINTF(LOW, "MLDSA zeroize flow.\n");
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, (1 << ABR_REG_MLDSA_CTRL_ZEROIZE_LOW) & ABR_REG_MLDSA_CTRL_ZEROIZE_MASK);

    // wait for MLDSA to be ready
    VPRINTF(LOW, "Waiting for mldsa status ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

}

void write_mldsa_reg(volatile uint32_t *base_addr, uint32_t *data, uint32_t size) {
    for (uint32_t i = 0; i < size; i++) {
        base_addr[i] = data[i];
    }
}

void mldsa_keygen_flow(mldsa_io seed, uint32_t entropy[MLDSA87_ENTROPY_SIZE], uint32_t privkey[MLDSA87_PRIVKEY_SIZE], uint32_t pubkey[MLDSA87_PUBKEY_SIZE])
{
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;
    
    // wait for MLDSA to be ready
    VPRINTF(LOW, "Waiting for mldsa status ready in keygen\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    //Program mldsa seed
    if(seed.kv_intf){
        // Program MLDSA_SEED Read with 12 dwords from seed_kv_id
        lsu_write_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_CTRL, (ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_EN_MASK |
                                                          ((seed.kv_id << ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_MASK)));

        VPRINTF(LOW, "Try to Overwrite seed data in MLDSA\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLDSA_SEED_0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLDSA_SEED_7) {
             *reg_ptr++ = 0;
        }

         // Check that MLDSA SEED is loaded
         while((lsu_read_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_STATUS) & ABR_REG_KV_MLDSA_SEED_RD_STATUS_VALID_MASK) == 0);
     }
     else{
        write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_SEED_0, seed.data, MLDSA87_SEED_SIZE);
    }

    // Write MLDSA ENTROPY
    VPRINTF(LOW, "Writing entropy\n");
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, MLDSA87_ENTROPY_SIZE);

    VPRINTF(LOW, "\nMLDSA KEYGEN\n");
    // Enable MLDSA KEYGEN core
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN);

    // // wait for MLDSA KEYGEN process to be done
    wait_for_mldsa_intr();
    
    if(!seed.kv_intf){
        // Read the data back from MLDSA register
        VPRINTF(LOW, "Load PRIVKEY data from MLDSA\n");
        reg_ptr = (uint32_t *) CLP_ABR_REG_MLDSA_PRIVKEY_OUT_BASE_ADDR;
        offset = 0;
        while (offset < MLDSA87_PRIVKEY_SIZE) {
            actual_data = *reg_ptr;
            if (actual_data != privkey[offset]) {
                VPRINTF(LOW, "At offset [%d], mldsa_privkey data mismatch!\n", offset);
                VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
                VPRINTF(LOW, "Expected data: 0x%x\n", privkey[offset]);
                VPRINTF(LOW, "%c", fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }

    // Read the data back from MLDSA register
    VPRINTF(LOW, "Load PUBKEY data from MLDSA\n");
    reg_ptr = (uint32_t*) CLP_ABR_REG_MLDSA_PUBKEY_BASE_ADDR;
    offset = 0;
    while (offset < MLDSA87_PUBKEY_SIZE) {
        actual_data = *reg_ptr;
        if (actual_data != pubkey[offset]) {
            VPRINTF(LOW, "At offset [%d], mldsa_pubkey data mismatch!\n", offset);
            VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
            VPRINTF(LOW, "Expected data: 0x%x\n", pubkey[offset]);
            VPRINTF(LOW, "%c", fail_cmd);
            while(1);
        } 
        reg_ptr++;
        offset++;
    }
    
}

void mldsa_keygen_signing_flow(mldsa_io seed, uint32_t msg[MLDSA87_MSG_SIZE], uint32_t sign_rnd[MLDSA87_SIGN_RND_SIZE], uint32_t entropy[MLDSA87_ENTROPY_SIZE], uint32_t sign[MLDSA87_SIGN_SIZE])
{
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;
    
    // wait for MLDSA to be ready
    VPRINTF(LOW, "Waiting for mldsa status ready in keygen\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    //Program mldsa seed
    if(seed.kv_intf){
        // Program MLDSA_SEED Read with 12 dwords from seed_kv_id
        lsu_write_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_CTRL, (ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_EN_MASK |
                                                          ((seed.kv_id << ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_MASK)));

        VPRINTF(LOW, "Try to Overwrite seed data in MLDSA\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLDSA_SEED_0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLDSA_SEED_7) {
             *reg_ptr++ = 0;
        }

         // Check that MLDSA SEED is loaded
         while((lsu_read_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_STATUS) & ABR_REG_KV_MLDSA_SEED_RD_STATUS_VALID_MASK) == 0);
     }
     else{
        write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_SEED_0, seed.data, MLDSA87_SEED_SIZE);
    }

    // Program MLDSA MSG
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_MSG_0, msg, MLDSA87_MSG_SIZE);

    // Program MLDSA Sign Rnd
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_SIGN_RND_0, sign_rnd, MLDSA87_SIGN_RND_SIZE);

    // Write MLDSA ENTROPY
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, MLDSA87_ENTROPY_SIZE);

    // Enable MLDSA KEYGEN + SIGNING core
    VPRINTF(LOW, "\nMLDSA KEYGEN + SIGNING\n");
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN);

    // wait for MLDSA SIGNING process to be done
    wait_for_mldsa_intr();

    // Read the data back from MLDSA register
    VPRINTF(LOW, "Load SIGN data from MLDSA\n");
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLDSA_SIGNATURE_BASE_ADDR;
    offset = 0;
    while (offset < MLDSA87_SIGN_SIZE) {
        actual_data = *reg_ptr;
        if (actual_data != sign[offset]) {
            VPRINTF(LOW, "At offset [%d], mldsa_sign data mismatch!\n", offset);
            VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
            VPRINTF(LOW, "Expected data: 0x%x\n", sign[offset]);
            VPRINTF(LOW, "%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

}


void mldsa_signing_flow(uint32_t privkey[MLDSA87_PRIVKEY_SIZE], uint32_t msg[MLDSA87_MSG_SIZE], uint32_t sign_rnd[MLDSA87_SIGN_RND_SIZE], uint32_t entropy[MLDSA87_ENTROPY_SIZE], uint32_t sign[MLDSA87_SIGN_SIZE])
{
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;

    VPRINTF(LOW, "Waiting for mldsa status ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    // Program MLDSA PRIVKEY
    VPRINTF(LOW, "Writing privkey\n");
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_PRIVKEY_IN_BASE_ADDR, privkey, MLDSA87_PRIVKEY_SIZE);
    
    // Program MLDSA MSG
    VPRINTF(LOW, "Writing msg\n");
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_MSG_0, msg, MLDSA87_MSG_SIZE);

    // Program MLDSA Sign Rnd
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_SIGN_RND_0, sign_rnd, MLDSA87_SIGN_RND_SIZE);

    // Program MLDSA ENTROPY
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, MLDSA87_ENTROPY_SIZE);

    // Enable MLDSA SIGNING core
    VPRINTF(LOW, "\nMLDSA SIGNING\n");
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_SIGNING);
    
    // wait for MLDSA SIGNING process to be done
    wait_for_mldsa_intr();
        
    // // Read the data back from MLDSA register
    VPRINTF(LOW, "Load SIGN data from MLDSA\n");
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLDSA_SIGNATURE_BASE_ADDR;
    offset = 0;
    while (offset < MLDSA87_SIGN_SIZE) {
        actual_data = *reg_ptr;
        if (actual_data != sign[offset]) {
            VPRINTF(LOW, "At offset [%d], mldsa_sign data mismatch!\n", offset);
            VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
            VPRINTF(LOW, "Expected data: 0x%x\n", sign[offset]);
            VPRINTF(LOW, "%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

}

void mldsa_verifying_flow(uint32_t msg[MLDSA87_MSG_SIZE], uint32_t pubkey[MLDSA87_PUBKEY_SIZE], uint32_t sign[MLDSA87_SIGN_SIZE], uint32_t verify_res[MLDSA_VERIFY_RES_SIZE])
{
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;

    // wait for MLDSA to be ready
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);
    
    // Program MLDSA MSG
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_MSG_0, msg, MLDSA87_MSG_SIZE);

    // Program MLDSA PUBKEY
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_PUBKEY_BASE_ADDR, pubkey, MLDSA87_PUBKEY_SIZE);

    // Program MLDSA SIGNATURE
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_SIGNATURE_BASE_ADDR, sign, MLDSA87_SIGN_SIZE);

    // Enable MLDSA VERIFYING core
    VPRINTF(LOW, "\nMLDSA VERIFYING\n");
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_VERIFYING);
    
    // wait for MLDSA VERIFYING process to be done
    wait_for_mldsa_intr();
    
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLDSA_VERIFY_RES_0;
    // Read the data back from MLDSA register
    VPRINTF(LOW, "Load VERIFY_RES data from MLDSA\n");
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLDSA_VERIFY_RES_15) {
        actual_data = *reg_ptr;
        if (actual_data != verify_res[offset]) {
            VPRINTF(LOW, "At offset [%d], mldsa_verify_res data mismatch!\n", offset);
            VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
            VPRINTF(LOW, "Expected data: 0x%x\n", verify_res[offset]);
            VPRINTF(LOW, "%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

}

void mldsa_keygen_signing_external_mu_flow(mldsa_io seed, uint32_t external_mu[MLDSA87_EXTERNAL_MU_SIZE], uint32_t sign_rnd[MLDSA87_SIGN_RND_SIZE], uint32_t entropy[MLDSA87_ENTROPY_SIZE], uint32_t sign[MLDSA87_SIGN_SIZE])
{
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;
    
    // wait for MLDSA to be ready
    VPRINTF(LOW, "Waiting for mldsa status ready in keygen\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    //Program mldsa seed
    if(seed.kv_intf){
        // Program MLDSA_SEED Read with 12 dwords from seed_kv_id
        lsu_write_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_CTRL, (ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_EN_MASK |
                                                          ((seed.kv_id << ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_MASK)));

        VPRINTF(LOW, "Try to Overwrite seed data in MLDSA\n");
        reg_ptr = (uint32_t*) CLP_ABR_REG_MLDSA_SEED_0;
        while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLDSA_SEED_7) {
             *reg_ptr++ = 0;
        }

         // Check that MLDSA SEED is loaded
         while((lsu_read_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_STATUS) & ABR_REG_KV_MLDSA_SEED_RD_STATUS_VALID_MASK) == 0);
     }
     else{
        write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_SEED_0, seed.data, MLDSA87_SEED_SIZE);
    }

    // Program MLDSA EXTERNAL_MU
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_EXTERNAL_MU_0, external_mu, MLDSA87_EXTERNAL_MU_SIZE);

    // Program MLDSA Sign Rnd
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_SIGN_RND_0, sign_rnd, MLDSA87_SIGN_RND_SIZE);

    // Write MLDSA ENTROPY
    VPRINTF(LOW, "Writing entropy\n");
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, MLDSA87_ENTROPY_SIZE);

    // Enable MLDSA KEYGEN + SIGNING core
    VPRINTF(LOW, "\nMLDSA KEYGEN + SIGNING in ExternalMu mode\n");
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN | 
                                           ABR_REG_MLDSA_CTRL_EXTERNAL_MU_MASK);

    // wait for MLDSA SIGNING process to be done
    wait_for_mldsa_intr();

    // Read the data back from MLDSA register
    VPRINTF(LOW, "Load SIGN data from MLDSA\n");
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLDSA_SIGNATURE_BASE_ADDR;
    offset = 0;
    while (offset < MLDSA87_SIGN_SIZE) {
        actual_data = *reg_ptr;
        if (actual_data != sign[offset]) {
            VPRINTF(LOW, "At offset [%d], mldsa_sign data mismatch!\n", offset);
            VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
            VPRINTF(LOW, "Expected data: 0x%x\n", sign[offset]);
            VPRINTF(LOW, "%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

}


void mldsa_signing_external_mu_flow(uint32_t privkey[MLDSA87_PRIVKEY_SIZE], uint32_t external_mu[MLDSA87_EXTERNAL_MU_SIZE], uint32_t sign_rnd[MLDSA87_SIGN_RND_SIZE], uint32_t entropy[MLDSA87_ENTROPY_SIZE], uint32_t sign[MLDSA87_SIGN_SIZE])
{
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data;

    //  wait for MLDSA to be ready
    VPRINTF(LOW, "Waiting for mldsa status ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    // Program MLDSA PRIVKEY
    VPRINTF(LOW, "Writing privkey\n");
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_PRIVKEY_IN_BASE_ADDR, privkey, MLDSA87_PRIVKEY_SIZE);
    
    VPRINTF(LOW, "Writing ExternalMu\n");
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_EXTERNAL_MU_0, external_mu, MLDSA87_EXTERNAL_MU_SIZE);

    // Program MLDSA Sign Rnd
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_SIGN_RND_0, sign_rnd, MLDSA87_SIGN_RND_SIZE);

    // Program MLDSA ENTROPY
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_ABR_ENTROPY_0, entropy, MLDSA87_ENTROPY_SIZE);

    // Enable MLDSA SIGNING core
    VPRINTF(LOW, "\nMLDSA SIGNING in ExternalMu mode\n");
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_SIGNING | 
                                           ABR_REG_MLDSA_CTRL_EXTERNAL_MU_MASK);
    
    // wait for MLDSA SIGNING process to be done
    wait_for_mldsa_intr();
        
    // // Read the data back from MLDSA register
    VPRINTF(LOW, "Load SIGN data from MLDSA\n");
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLDSA_SIGNATURE_BASE_ADDR;
    offset = 0;
    while (offset < MLDSA87_SIGN_SIZE) {
        actual_data = *reg_ptr;
        if (actual_data != sign[offset]) {
            VPRINTF(LOW, "At offset [%d], mldsa_sign data mismatch!\n", offset);
            VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
            VPRINTF(LOW, "Expected data: 0x%x\n", sign[offset]);
            VPRINTF(LOW, "%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

}

void mldsa_verifying_external_mu_flow(uint32_t external_mu[MLDSA87_EXTERNAL_MU_SIZE], uint32_t pubkey[MLDSA87_PUBKEY_SIZE], uint32_t sign[MLDSA87_SIGN_SIZE], uint32_t verify_res[MLDSA_VERIFY_RES_SIZE])
{
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t actual_data; ;

    // wait for MLDSA to be ready
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);
    
    VPRINTF(LOW, "Writing ExternalMu\n");
    // Program MLDSA EXTERNAL_MU
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_EXTERNAL_MU_0, external_mu, MLDSA87_EXTERNAL_MU_SIZE);

    // Program MLDSA PUBKEY
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_PUBKEY_BASE_ADDR, pubkey, MLDSA87_PUBKEY_SIZE);

    // Program MLDSA SIGNATURE
    write_mldsa_reg((uint32_t*) CLP_ABR_REG_MLDSA_SIGNATURE_BASE_ADDR, sign, MLDSA87_SIGN_SIZE);

    // Enable MLDSA VERIFYING core
    VPRINTF(LOW, "\nMLDSA VERIFYING in ExternalMu mode\n");
    lsu_write_32(CLP_ABR_REG_MLDSA_CTRL, MLDSA_CMD_VERIFYING | 
                                           ABR_REG_MLDSA_CTRL_EXTERNAL_MU_MASK);
    
    // wait for MLDSA VERIFYING process to be done
    wait_for_mldsa_intr();
    
    reg_ptr = (uint32_t *) CLP_ABR_REG_MLDSA_VERIFY_RES_0;
    // Read the data back from MLDSA register
    VPRINTF(LOW, "Load VERIFY_RES data from MLDSA\n");
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ABR_REG_MLDSA_VERIFY_RES_15) {
        actual_data = *reg_ptr;
        if (actual_data != verify_res[offset]) {
            VPRINTF(LOW, "At offset [%d], actual_data data mismatch!\n", offset);
            VPRINTF(LOW, "Actual   data: 0x%x\n", actual_data);
            VPRINTF(LOW, "Expected data: 0x%x\n", verify_res[offset]);
            VPRINTF(LOW, "%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }
}

void mldsa_keyload_error_flow(mldsa_io seed)
{
    // wait for MLDSA to be ready
    VPRINTF(LOW, "Waiting for mldsa status ready\n");
    while((lsu_read_32(CLP_ABR_REG_MLDSA_STATUS) & ABR_REG_MLDSA_STATUS_READY_MASK) == 0);

    //Enable force of zeroize during keyvault read
    VPRINTF(LOW, "%c",0x9b);

    // Program MLDSA_SEED Read with 12 dwords from seed_kv_id
    lsu_write_32(CLP_ABR_REG_KV_MLDSA_SEED_RD_CTRL, (ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_EN_MASK |
                                                          ((seed.kv_id << ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_LOW) & ABR_REG_KV_MLDSA_SEED_RD_CTRL_READ_ENTRY_MASK)));
}
