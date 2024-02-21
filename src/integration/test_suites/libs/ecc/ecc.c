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
#include "ecc.h"
#include "caliptra_isr.h"

extern volatile caliptra_intr_received_s cptra_intr_rcv;

void wait_for_ecc_intr(){
    printf("ECC flow in progress...\n");
    while((cptra_intr_rcv.ecc_error == 0) & (cptra_intr_rcv.ecc_notif == 0)){
        __asm__ volatile ("wfi"); // "Wait for interrupt"
        // Sleep during ECC operation to allow ISR to execute and show idle time in sims
        for (uint16_t slp = 0; slp < 100; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    };
    //printf("Received ECC error intr with status = %d\n", cptra_intr_rcv.ecc_error);
    printf("Received ECC notif/ err intr with status = %d/ %d\n", cptra_intr_rcv.ecc_notif, cptra_intr_rcv.ecc_error);
}

void ecc_zeroize(){
    printf("ECC zeroize flow.\n");
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, (1 << ECC_REG_ECC_CTRL_ZEROIZE_LOW) & ECC_REG_ECC_CTRL_ZEROIZE_MASK);
}

void ecc_keygen_flow(ecc_io seed, ecc_io nonce, ecc_io iv, ecc_io privkey, ecc_io pubkey_x, ecc_io pubkey_y){
    uint8_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t ecc_privkey  [12];
    uint32_t ecc_pubkey_x [12];
    uint32_t ecc_pubkey_y [12];
    
    // wait for ECC to be ready
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    if(seed.kv_intf){
        // Program ECC_SEED Read with 12 dwords from seed_kv_id
        lsu_write_32(CLP_ECC_REG_ECC_KV_RD_SEED_CTRL, (ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK |
                                                    ((seed.kv_id << ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW) & ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_MASK)));

        // Check that ECC SEED is loaded
        while((lsu_read_32(CLP_ECC_REG_ECC_KV_RD_SEED_STATUS) & ECC_REG_ECC_KV_RD_SEED_STATUS_VALID_MASK) == 0);
    }
    else{
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SEED_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SEED_11) {
            *reg_ptr++ = seed.data[offset++];
        }
    }

    if (privkey.kv_intf){
        // set privkey DEST to write
        lsu_write_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, (ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                                                    ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK |
                                                    ((privkey.kv_id << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) & ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK)));
    }
    
    // Write ECC nonce
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_NONCE_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_NONCE_11) {
        *reg_ptr++ = nonce.data[offset++];
    }

    // Write ECC IV
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
        *reg_ptr++ = iv.data[offset++];
    }

    printf("\nECC KEYGEN\n");
    // Enable ECC KEYGEN core
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_KEYGEN);

    // wait for ECC KEYGEN process to be done
    wait_for_ecc_intr();
    
    if (privkey.kv_intf){
        printf("Wait for KV write\n");
        // check dest done
        while((lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_STATUS) & ECC_REG_ECC_KV_WR_PKEY_STATUS_VALID_MASK) == 0);
    }
    else{
        // Read the data back from ECC register
        printf("Load PRIVKEY data from ECC\n");
        reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_PRIVKEY_OUT_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_OUT_11) {
            ecc_privkey[offset] = *reg_ptr;
            if (ecc_privkey[offset] != privkey.data[offset]) {
                printf("At offset [%d], ecc_privkey data mismatch!\n", offset);
                printf("Actual   data: 0x%x\n", ecc_privkey[offset]);
                printf("Expected data: 0x%x\n", privkey.data[offset]);
                printf("%c", fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }

    // Read the data back from ECC register
    printf("Load PUBKEY_X data from ECC\n");
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_11) {
        ecc_pubkey_x[offset] = *reg_ptr;
        if (ecc_pubkey_x[offset] != pubkey_x.data[offset]) {
            printf("At offset [%d], ecc_pubkey_x data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", ecc_pubkey_x[offset]);
            printf("Expected data: 0x%x\n", pubkey_x.data[offset]);
            printf("%c", fail_cmd);
            while(1);
        } 
        reg_ptr++;
        offset++;
    }

    printf("Load PUBKEY_Y data from ECC\n");
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_11) {
        ecc_pubkey_y[offset] = *reg_ptr;
        if (ecc_pubkey_y[offset] != pubkey_y.data[offset]) {
            printf("At offset [%d], ecc_pubkey_y data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", ecc_pubkey_y[offset]);
            printf("Expected data: 0x%x\n", pubkey_y.data[offset]);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }
    
}


void ecc_sharedkey_flow(ecc_io nonce, ecc_io iv, ecc_io privkey, ecc_io pubkey_x, ecc_io pubkey_y, ecc_io sharedkey){
    uint8_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t ecc_privkey   [12];
    uint32_t ecc_sharedkey [12];
    
    // wait for ECC to be ready
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    if(privkey.kv_intf){
        // Program PRIVKEY Read with 12 dwords from pkey_kv_id
        lsu_write_32(CLP_ECC_REG_ECC_KV_RD_PKEY_CTRL, (ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_MASK |
                                                    ((privkey.kv_id << ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_LOW) & ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_MASK)));

        // Check that ECC PKEY is loaded
        while((lsu_read_32(CLP_ECC_REG_ECC_KV_RD_PKEY_STATUS) & ECC_REG_ECC_KV_RD_PKEY_STATUS_VALID_MASK) == 0);
    }
    else{
        // Program ECC PRIVKEY
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_11) {
            *reg_ptr++ = privkey.data[offset++];
        }
    }
    
    // Write PUBKEY_X
    printf("Store PUBKEY_X data in ECC\n");
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_11) {
        *reg_ptr++ = pubkey_x.data[offset++];
    }

    // Write PUBKEY_Y
    printf("Store PUBKEY_Y data in ECC\n");
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_11) {
        *reg_ptr++ = pubkey_y.data[offset++];
    }

    // Write ECC nonce
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_NONCE_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_NONCE_11) {
        *reg_ptr++ = nonce.data[offset++];
    }

    // Write ECC IV
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
        *reg_ptr++ = iv.data[offset++];
    }

    if (sharedkey.kv_intf){
        // set privkey DEST to write
        lsu_write_32(CLP_ECC_REG_ECC_KV_WR_PKEY_CTRL, (ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                                                    ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK |
                                                    ((sharedkey.kv_id << ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) & ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK)));
    }

    printf("\nECC SHAREDKEY\n");
    // Enable ECC SHAREDKEY core
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SHAREDKEY);

    // wait for ECC KEYGEN process to be done
    wait_for_ecc_intr();
    
    if (sharedkey.kv_intf){
        printf("Wait for KV write\n");
        // check dest done
        while((lsu_read_32(CLP_ECC_REG_ECC_KV_WR_PKEY_STATUS) & ECC_REG_ECC_KV_WR_PKEY_STATUS_VALID_MASK) == 0);
    }
    else{
        // Read the data back from ECC register
        printf("Load SHAREDKEY data from ECC\n");
        reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_DH_SHARED_KEY_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_DH_SHARED_KEY_11) {
            ecc_sharedkey[offset] = *reg_ptr;
            if (ecc_sharedkey[offset] != sharedkey.data[offset]) {
                printf("At offset [%d], ecc_sharedkey data mismatch!\n", offset);
                printf("Actual   data: 0x%x\n", ecc_sharedkey[offset]);
                printf("Expected data: 0x%x\n", sharedkey.data[offset]);
                printf("%c", fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }
    }
    
}

void ecc_signing_flow(ecc_io privkey, ecc_io msg, ecc_io iv, ecc_io sign_r, ecc_io sign_s){
    uint8_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t ecc_sign_r [12];
    uint32_t ecc_sign_s [12];

    // wait for ECC to be ready
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    if (privkey.kv_intf){
        //inject privkey to kv key reg
        //suppose privkey is stored by ecc_keygen
        printf("Inject PRIVKEY from kv to ECC\n");
        
        // Program ECC_PRIVKEY Read with 12 dwords from privkey_kv_id
        lsu_write_32(CLP_ECC_REG_ECC_KV_RD_PKEY_CTRL, (ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_MASK |
                                                    ((privkey.kv_id << ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_LOW) & ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_MASK)));

        // Check that ECC PRIVKEY is loaded
        while((lsu_read_32(CLP_ECC_REG_ECC_KV_RD_PKEY_STATUS) & ECC_REG_ECC_KV_RD_PKEY_STATUS_VALID_MASK) == 0);
    }
    else{
        // Program ECC PRIVKEY
        reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_0;
        offset = 0;
        while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PRIVKEY_IN_11) {
            *reg_ptr++ = privkey.data[offset++];
        }
    }
    

    // Program ECC MSG
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_MSG_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_MSG_11) {
        *reg_ptr++ = msg.data[offset++];
    }

    // Program ECC IV
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
        *reg_ptr++ = iv.data[offset++];
    }

    // Enable ECC SIGNING core
    printf("\nECC SIGNING\n");
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING);
    
    // wait for ECC SIGNING process to be done
    wait_for_ecc_intr();
    
    // Read the data back from ECC register
    printf("Load SIGN_R data from ECC\n");
    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_SIGN_R_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_11) {
        ecc_sign_r[offset] = *reg_ptr;
        if (ecc_sign_r[offset] != sign_r.data[offset]) {
            printf("At offset [%d], ecc_sign_r data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", ecc_sign_r[offset]);
            printf("Expected data: 0x%x\n", sign_r.data[offset]);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

    printf("Load SIGN_S data from ECC\n");
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_11) {
        ecc_sign_s[offset] = *reg_ptr;
        if (ecc_sign_s[offset] != sign_s.data[offset]) {
            printf("At offset [%d], ecc_sign_s data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", ecc_sign_s[offset]);
            printf("Expected data: 0x%x\n", sign_s.data[offset]);
            printf("%c", fail_cmd);
            while(1);
        } 
        reg_ptr++;
        offset++;
    }

}

void ecc_verifying_flow(ecc_io msg, ecc_io pubkey_x, ecc_io pubkey_y, ecc_io sign_r, ecc_io sign_s){
    uint8_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t ecc_verify_r [12];

    // wait for ECC to be ready
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);
    
    // Program ECC MSG
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_MSG_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_MSG_11) {
        *reg_ptr++ = msg.data[offset++];
    }

    // Program ECC PUBKEY_X
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_X_11) {
        *reg_ptr++ = pubkey_x.data[offset++];
    }

    // Program ECC PUBKEY_Y
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_PUBKEY_Y_11) {
        *reg_ptr++ = pubkey_y.data[offset++];
    }

    // Program ECC SIGN_R
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_11) {
        *reg_ptr++ = sign_r.data[offset++];
    }

    // Program ECC SIGN_S
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_11) {
        *reg_ptr++ = sign_s.data[offset++];
    }

    // Enable ECC VERIFYING core
    printf("\nECC VERIFYING\n");
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_VERIFYING);
    
    // wait for ECC VERIFYING process to be done
    wait_for_ecc_intr();
    
    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_VERIFY_R_0;
    // Read the data back from ECC register
    printf("Load VERIFY_R data from ECC\n");
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_VERIFY_R_11) {
        ecc_verify_r[offset] = *reg_ptr;
        if (ecc_verify_r[offset] != sign_r.data[offset]) {
            printf("At offset [%d], ecc_verify_r data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", ecc_verify_r[offset]);
            printf("Expected data: 0x%x\n", sign_r.data[offset]);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

}

void ecc_pcr_signing_flow(ecc_io iv, ecc_io sign_r, ecc_io sign_s){
    uint8_t offset;
    volatile uint32_t * reg_ptr;
    uint8_t fail_cmd = 0x1;

    uint32_t ecc_sign_r [12];
    uint32_t ecc_sign_s [12];

    // wait for ECC to be ready
    while((lsu_read_32(CLP_ECC_REG_ECC_STATUS) & ECC_REG_ECC_STATUS_READY_MASK) == 0);

    // Program ECC IV
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_IV_11) {
        *reg_ptr++ = iv.data[offset++];
    }

    // Enable ECC PCR SIGNING core
    printf("\nECC PCR SIGNING\n");
    lsu_write_32(CLP_ECC_REG_ECC_CTRL, ECC_CMD_SIGNING | 
                ((1 << ECC_REG_ECC_CTRL_PCR_SIGN_LOW) & ECC_REG_ECC_CTRL_PCR_SIGN_MASK));
    
    // wait for ECC SIGNING process to be done
    wait_for_ecc_intr();
    
    // Read the data back from ECC register
    printf("Load SIGN_R data from ECC\n");
    reg_ptr = (uint32_t *) CLP_ECC_REG_ECC_SIGN_R_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_R_11) {
        ecc_sign_r[offset] = *reg_ptr;
        if (ecc_sign_r[offset] != sign_r.data[offset]) {
            printf("At offset [%d], ecc_sign_r data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", ecc_sign_r[offset]);
            printf("Expected data: 0x%x\n", sign_r.data[offset]);
            printf("%c", fail_cmd);
            while(1);
        }
        reg_ptr++;
        offset++;
    }

    printf("Load SIGN_S data from ECC\n");
    reg_ptr = (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_ECC_REG_ECC_SIGN_S_11) {
        ecc_sign_s[offset] = *reg_ptr;
        if (ecc_sign_s[offset] != sign_s.data[offset]) {
            printf("At offset [%d], ecc_sign_s data mismatch!\n", offset);
            printf("Actual   data: 0x%x\n", ecc_sign_s[offset]);
            printf("Expected data: 0x%x\n", sign_s.data[offset]);
            printf("%c", fail_cmd);
            while(1);
        } 
        reg_ptr++;
        offset++;
    }

}
