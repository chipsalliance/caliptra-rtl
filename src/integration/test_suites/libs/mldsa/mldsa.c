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
    printf("MLDSA flow in progress...\n");
    while((cptra_intr_rcv.mldsa_error == 0) & (cptra_intr_rcv.mldsa_notif == 0)){
        __asm__ volatile ("wfi"); // "Wait for interrupt"
        // Sleep during MLDSA operation to allow ISR to execute and show idle time in sims
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    };
    //printf("Received MLDSA error intr with status = %d\n", cptra_intr_rcv.mldsa_error);
    printf("Received MLDSA notif/ err intr with status = %d/ %d\n", cptra_intr_rcv.mldsa_notif, cptra_intr_rcv.mldsa_error);
}

void mldsa_zeroize(){
    printf("MLDSA zeroize flow.\n");
    lsu_write_32(CLP_MLDSA_REG_MLDSA_CTRL, (1 << MLDSA_REG_MLDSA_CTRL_ZEROIZE_LOW) & MLDSA_REG_MLDSA_CTRL_ZEROIZE_MASK);
}



void mldsa_keygen_flow(uint32_t seed[8], uint32_t sign_rnd[8], uint32_t entropy[16], uint32_t privkey[1224], uint32_t pubkey[648]){
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t mldsa_privkey  [1224];
    uint32_t mldsa_pubkey   [648];
    
    // wait for MLDSA to be ready
    printf("Waiting for mldsa status ready in keygen\n");
    while((lsu_read_32(CLP_MLDSA_REG_MLDSA_STATUS) & MLDSA_REG_MLDSA_STATUS_READY_MASK) == 0);

    //TODO: modify below after KV intf is ready
    // if(seed.kv_intf){
    //     // Program MLDSA_SEED Read with 12 dwords from seed_kv_id
    //     lsu_write_32(CLP_MLDSA_REG_MLDSA_KV_RD_SEED_CTRL, (MLDSA_REG_MLDSA_KV_RD_SEED_CTRL_READ_EN_MASK |
    //                                                 ((seed.kv_id << MLDSA_REG_MLDSA_KV_RD_SEED_CTRL_READ_ENTRY_LOW) & MLDSA_REG_MLDSA_KV_RD_SEED_CTRL_READ_ENTRY_MASK)));

    //     // Try to overwrite MLDSA SEED from keyvault
    //     reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_SEED_0;
    //     while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_SEED_11) {
    //         *reg_ptr++ = 0;
    //     }

    //     // Check that MLDSA SEED is loaded
    //     while((lsu_read_32(CLP_MLDSA_REG_MLDSA_KV_RD_SEED_STATUS) & MLDSA_REG_MLDSA_KV_RD_SEED_STATUS_VALID_MASK) == 0);
    // }
    // else{
    // printf("Writing seed from tb\n");
    // printf("%c", 0xd9);
        reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_SEED_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_SEED_7) {
            *reg_ptr++ = seed[offset++];
        }
    // }

    // if (privkey.kv_intf){
    //     // set privkey DEST to write
    //     lsu_write_32(CLP_MLDSA_REG_MLDSA_KV_WR_PKEY_CTRL, (MLDSA_REG_MLDSA_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
    //                                                 MLDSA_REG_MLDSA_KV_WR_PKEY_CTRL_MLDSA_PKEY_DEST_VALID_MASK |
    //                                                 ((privkey.kv_id << MLDSA_REG_MLDSA_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) & MLDSA_REG_MLDSA_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK)));
    // }

    // Write MLDSA ENTROPY
    printf("Writing entropy\n");
    reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_ENTROPY_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_ENTROPY_15) {
        *reg_ptr++ = entropy[offset++];
    }

    printf("\nMLDSA KEYGEN\n");
    // Enable MLDSA KEYGEN core
    lsu_write_32(CLP_MLDSA_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN);

    // // wait for MLDSA KEYGEN process to be done
    wait_for_mldsa_intr();
    
    // if (privkey.kv_intf){
    //     printf("Wait for KV write\n");
    //     // check dest done
    //     while((lsu_read_32(CLP_MLDSA_REG_MLDSA_KV_WR_PKEY_STATUS) & MLDSA_REG_MLDSA_KV_WR_PKEY_STATUS_VALID_MASK) == 0);
    // }
    // else{
        // Read the data back from MLDSA register
        printf("Load PRIVKEY data from MLDSA\n");
        reg_ptr = (uint32_t *) CLP_MLDSA_REG_MLDSA_PRIVKEY_OUT_BASE_ADDR;
        offset = 0;
        while (offset <= 1223) {
            mldsa_privkey[offset] = *reg_ptr;
            if (mldsa_privkey[offset] != privkey[offset]) {
                printf("At offset [%d], mldsa_privkey data mismatch!\n", offset);
                printf("Actual   data: 0x%x\n", mldsa_privkey[offset]);
                printf("Expected data: 0x%x\n", privkey[offset]);
                printf("%c", fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    // }

    // Read the data back from MLDSA register
    printf("Load PUBKEY data from MLDSA\n");
    reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_PUBKEY_BASE_ADDR;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_PUBKEY_END_ADDR) {
        mldsa_pubkey[offset] = *reg_ptr;
        if (mldsa_pubkey[offset] != pubkey[offset]) {
            printf("At offset [%d], mldsa_pubkey data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", mldsa_pubkey[offset]);
            printf("Expected data: 0x%x\n", pubkey[offset]);
            printf("%c", fail_cmd);
            while(1);
        } 
        reg_ptr++;
        offset++;
    }
    
}

void mldsa_keygen_signing_flow(uint32_t seed[8], uint32_t sign_rnd[8], uint32_t msg[16], uint32_t privkey[1224], uint32_t pubkey[648], uint32_t sign[1157]) {
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t mldsa_privkey  [1224];
    uint32_t mldsa_pubkey   [648];
    uint32_t mldsa_sign [1157];
    
    // wait for MLDSA to be ready
    printf("Waiting for mldsa status ready in keygen\n");
    while((lsu_read_32(CLP_MLDSA_REG_MLDSA_STATUS) & MLDSA_REG_MLDSA_STATUS_READY_MASK) == 0);

    //Program mldsa seed
    reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_SEED_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_SEED_7) {
        *reg_ptr++ = seed[offset++];
    }

    // Program MLDSA MSG
    reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_MSG_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_MSG_15) {
        *reg_ptr++ = msg[offset++];
    }

    // Program MLDSA Sign Rnd
    reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_SIGN_RND_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_SIGN_RND_7) {
        *reg_ptr++ = sign_rnd[offset++];
    }

    // Enable MLDSA SIGNING core
    printf("\nMLDSA KEYGEN + SIGNING\n");
    lsu_write_32(CLP_MLDSA_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN);
    
    // wait for MLDSA SIGNING process to be done
    wait_for_mldsa_intr();

    // printf("Load PRIVKEY data from MLDSA\n");
    // reg_ptr = (uint32_t *) CLP_MLDSA_REG_MLDSA_PRIVKEY_OUT_BASE_ADDR;
    // // printf("privkey reg addr = %x", reg_ptr);
    // offset = 0;
    // while (offset <= 1223) {
    //     mldsa_privkey[offset] = *reg_ptr;
    //     if (mldsa_privkey[offset] != privkey[offset]) {
    //         printf("At offset [%d], mldsa_privkey data mismatch!\n", offset);
    //         printf("Actual   data: 0x%x\n", mldsa_privkey[offset]);
    //         printf("Expected data: 0x%x\n", privkey[offset]);
    //         printf("%c", fail_cmd);
    //         while(1);
    //     }
    //     reg_ptr++;
    //     offset++;
    // }

    // // Read the data back from MLDSA register
    // printf("Load PUBKEY data from MLDSA\n");
    // reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_PUBKEY_BASE_ADDR;
    // offset = 0;
    // while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_PUBKEY_END_ADDR) {
    //     mldsa_pubkey[offset] = *reg_ptr;
    //     if (mldsa_pubkey[offset] != pubkey[offset]) {
    //         printf("At offset [%d], mldsa_pubkey data mismatch!\n", offset);
    //         printf("Actual   data: 0x%x\n", mldsa_pubkey[offset]);
    //         printf("Expected data: 0x%x\n", pubkey[offset]);
    //         printf("%c", fail_cmd);
    //         while(1);
    //     } 
    //     reg_ptr++;
    //     offset++;
    // }

    // Read the data back from MLDSA register
    printf("Load SIGN data from MLDSA\n");
    reg_ptr = (uint32_t *) CLP_MLDSA_REG_MLDSA_SIGNATURE_BASE_ADDR;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_SIGNATURE_END_ADDR) {
        mldsa_sign[offset] = *reg_ptr;
        if (mldsa_sign[offset] != sign[offset]) {
            printf("At offset [%d], mldsa_sign data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", mldsa_sign[offset]);
            printf("Expected data: 0x%x\n", sign[offset]);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }


}


void mldsa_signing_flow(uint32_t privkey[1224], uint32_t msg[16], uint32_t entropy[16], uint32_t sign[1157]){
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t mldsa_sign [1157];

//  wait for MLDSA to be ready
    printf("Waiting for mldsa status ready\n");
    while((lsu_read_32(CLP_MLDSA_REG_MLDSA_STATUS) & MLDSA_REG_MLDSA_STATUS_READY_MASK) == 0);

//     if (privkey.kv_intf){
//         //inject privkey to kv key reg
//         //suppose privkey is stored by mldsa_keygen
//         printf("Inject PRIVKEY from kv to MLDSA\n");
        
//         // Program MLDSA_PRIVKEY Read with 12 dwords from privkey_kv_id
//         lsu_write_32(CLP_MLDSA_REG_MLDSA_KV_RD_PKEY_CTRL, (MLDSA_REG_MLDSA_KV_RD_PKEY_CTRL_READ_EN_MASK |
//                                                     ((privkey.kv_id << MLDSA_REG_MLDSA_KV_RD_PKEY_CTRL_READ_ENTRY_LOW) & MLDSA_REG_MLDSA_KV_RD_PKEY_CTRL_READ_ENTRY_MASK)));

//         // Try to overwrite MLDSA PRIVKEY from key vault
//         reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_PRIVKEY_IN_0;
//         while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_PRIVKEY_IN_11) {
//             *reg_ptr++ = 0;
//         }

//         // Check that MLDSA PRIVKEY is loaded
//         while((lsu_read_32(CLP_MLDSA_REG_MLDSA_KV_RD_PKEY_STATUS) & MLDSA_REG_MLDSA_KV_RD_PKEY_STATUS_VALID_MASK) == 0);
//     }
//     else{
        // Program MLDSA PRIVKEY
        printf("Writing privkey\n");
        reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_PRIVKEY_IN_BASE_ADDR;
        offset = 0;
        while (offset <= 1223) {
            // printf("offset = %0d, value = %x, reg ptr = %0d\n", offset++, privkey[offset++], reg_ptr);
            *reg_ptr++ = privkey[offset++];
        }
//     }
    

    // Program MLDSA MSG
    printf("Writing msg\n");
    reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_MSG_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_MSG_15) {
        *reg_ptr++ = msg[offset++];
    }

    // Program MLDSA ENTROPY
    printf("Writing entropy\n");
    reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_ENTROPY_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_ENTROPY_15) {
        *reg_ptr++ = entropy[offset++];
    }

    // Enable MLDSA SIGNING core
    printf("\nMLDSA SIGNING\n");
    lsu_write_32(CLP_MLDSA_REG_MLDSA_CTRL, MLDSA_CMD_SIGNING);
    
    // wait for MLDSA SIGNING process to be done
    wait_for_mldsa_intr();
        
    // // Read the data back from MLDSA register
    printf("Load SIGN data from MLDSA\n");
    reg_ptr = (uint32_t *) CLP_MLDSA_REG_MLDSA_SIGNATURE_BASE_ADDR;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_SIGNATURE_END_ADDR) {
        mldsa_sign[offset] = *reg_ptr;
        if (mldsa_sign[offset] != sign[offset]) {
            printf("At offset [%d], mldsa_sign data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", mldsa_sign[offset]);
            printf("Expected data: 0x%x\n", sign[offset]);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

}

void mldsa_verifying_flow(uint32_t msg[16], uint32_t pubkey[648], uint32_t sign[1157],  uint32_t verifyres[16]){
    uint16_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t mldsa_verifyres [16];

    // wait for MLDSA to be ready
    while((lsu_read_32(CLP_MLDSA_REG_MLDSA_STATUS) & MLDSA_REG_MLDSA_STATUS_READY_MASK) == 0);
    
    // Program MLDSA MSG
    reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_MSG_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_MSG_15) {
        *reg_ptr++ = msg[offset++];
    }

    // Program MLDSA PUBKEY
    reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_PUBKEY_BASE_ADDR;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_PUBKEY_END_ADDR) {
        *reg_ptr++ = pubkey[offset++];
    }


    // Program MLDSA SIGNATURE
    reg_ptr = (uint32_t*) CLP_MLDSA_REG_MLDSA_SIGNATURE_BASE_ADDR;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_SIGNATURE_END_ADDR) {
        *reg_ptr++ = sign[offset++];
    }


    // Enable MLDSA VERIFYING core
    printf("\nMLDSA VERIFYING\n");
    lsu_write_32(CLP_MLDSA_REG_MLDSA_CTRL, MLDSA_CMD_VERIFYING);
    
    // wait for MLDSA VERIFYING process to be done
    wait_for_mldsa_intr();
    
    reg_ptr = (uint32_t *) CLP_MLDSA_REG_MLDSA_VERIFY_RES_0;
    // Read the data back from MLDSA register
    printf("Load VERIFY_RES data from MLDSA\n");
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_MLDSA_REG_MLDSA_VERIFY_RES_15) {
        mldsa_verifyres[offset] = *reg_ptr;
        if (mldsa_verifyres[offset] != verifyres[offset]) {
            printf("At offset [%d], mldsa_verifyres data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", mldsa_verifyres[offset]);
            printf("Expected data: 0x%x\n", verifyres[offset]);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

}
