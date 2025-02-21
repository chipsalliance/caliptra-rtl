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
#include "mldsa.h"

volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

#ifdef MY_RANDOM_SEED
    unsigned time = (unsigned) MY_RANDOM_SEED;
#else
    unsigned time = 0;
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
    .mldsa_error      = 0,
    .mldsa_notif      = 0,
    .axi_dma_notif    = 0,
    .axi_dma_error    = 0,
};

void inject_command(uint8_t cmd){
    if (cmd == 0){
        lsu_write_32(CLP_MLDSA_REG_MLDSA_CTRL, (1 << MLDSA_REG_MLDSA_CTRL_ZEROIZE_LOW) & MLDSA_REG_MLDSA_CTRL_ZEROIZE_MASK);
    }
    else{
        printf("Enable scan mode\n");
        printf("%c", 0xef);

        for(uint8_t i=0;i<100;i++);
        printf("%c", 0xf6);
    }
} 

void main() {
    printf("---------------------------------------------\n");
    printf(" KV Smoke Test With MLDSA Zeroize/ScanMode !!\n");
    printf("---------------------------------------------\n");

    /* Intializes random number generator */  //TODO    
    srand(time);

    //Call interrupt init
    init_interrupts();
    mldsa_io seed;
    uint32_t sign_rnd[MLDSA87_SIGN_RND_SIZE], entropy[MLDSA87_ENTROPY_SIZE], msg[MLDSA87_MSG_SIZE];
    uint16_t offset, end_addr;
    volatile uint32_t * reg_ptr;
    volatile uint32_t * status_ptr;
    uint8_t fail_cmd = 0x1;

    rst_count++;

    if (rst_count==1){

        seed.kv_intf = TRUE;
        seed.kv_id = 8; //KV_ENTRY_FOR_MLDSA_SIGNING

        for (int i = 0; i < MLDSA87_SIGN_RND_SIZE; i++)
            sign_rnd[i] = rand() % 0xffffffff;

        for (int i = 0; i < MLDSA87_ENTROPY_SIZE; i++)
            entropy[i] = rand() % 0xffffffff;
        
        for (int i = 0; i < MLDSA87_MSG_SIZE; i++)
            msg[i] = rand() % 0xffffffff;

        printf("inject random mldsa seed to kv key reg (in RTL)\n");
        printf("%c", 0x93);
        
        printf("Waiting for mldsa status ready\n");
        while((lsu_read_32(CLP_MLDSA_REG_MLDSA_STATUS) & MLDSA_REG_MLDSA_STATUS_READY_MASK) == 0);

        // Program MLDSA_SEED Read with 12 dwords from seed_kv_id
        lsu_write_32(CLP_MLDSA_REG_MLDSA_KV_RD_SEED_CTRL, (MLDSA_REG_MLDSA_KV_RD_SEED_CTRL_READ_EN_MASK |
                                                            ((seed.kv_id << MLDSA_REG_MLDSA_KV_RD_SEED_CTRL_READ_ENTRY_LOW) & MLDSA_REG_MLDSA_KV_RD_SEED_CTRL_READ_ENTRY_MASK)));

        // Check that MLDSA SEED is loaded
        while((lsu_read_32(CLP_MLDSA_REG_MLDSA_KV_RD_SEED_STATUS) & MLDSA_REG_MLDSA_KV_RD_SEED_STATUS_VALID_MASK) == 0);
        
        // Program MLDSA MSG
        write_mldsa_reg((uint32_t*) CLP_MLDSA_REG_MLDSA_MSG_0, msg, MLDSA87_MSG_SIZE);
        // Program MLDSA Sign Rnd
        write_mldsa_reg((uint32_t*) CLP_MLDSA_REG_MLDSA_SIGN_RND_0, sign_rnd, MLDSA87_SIGN_RND_SIZE);
        // Program MLDSA ENTROPY
        write_mldsa_reg((uint32_t*) CLP_MLDSA_REG_MLDSA_ENTROPY_0, entropy, MLDSA87_ENTROPY_SIZE);

        status_ptr = (uint32_t *) CLP_MLDSA_REG_MLDSA_STATUS;

        uint8_t inject_cmd = rand() % 2;
        uint8_t test_mode = rand() % 16;
        if (test_mode == 0) {
            printf("\nApplying MLDSA zeroize/scan_mode just before enabling MLDSA.\n");
            inject_command(inject_cmd);

            printf("\nMLDSA KEYGEN + SIGNING\n");
            lsu_write_32(CLP_MLDSA_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN);
        }
        else if (test_mode == 1){
            printf("\nMLDSA KEYGEN + SIGNING\n");
            lsu_write_32(CLP_MLDSA_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN);

            printf("\nApplying MLDSA zeroize/scan_mode just after enabling MLDSA.\n");
            inject_command(inject_cmd);
        }
        else {
            printf("\nMLDSA KEYGEN + SIGNING\n");
            lsu_write_32(CLP_MLDSA_REG_MLDSA_CTRL, MLDSA_CMD_KEYGEN_SIGN);
        
            // Randomly apply zeroize during engine execution
            uint32_t zeroize_time = rand() % 3000;
            printf("\nzeroize time is = %d\n", zeroize_time);
            for (uint32_t slp = 0; slp < zeroize_time; slp++) {
                __asm__ volatile ("nop"); // Sleep loop as "nop"
            }

            printf("\nApplying MLDSA zeroize/scan_mode during execution.\n");
            inject_command(inject_cmd);
        }

        // Read the data back from MLDSA register
        uint8_t zeroize_target_api = rand() % 4;
        switch (zeroize_target_api){
            case 0:
                printf("\nTry to Load zeroized Pubkey data from MLDSA\n");
                reg_ptr = (uint32_t *) CLP_MLDSA_REG_MLDSA_PUBKEY_BASE_ADDR;
                end_addr = MLDSA87_PUBKEY_SIZE;
                break;
            case 1:
                printf("\nTry to Load zeroized PRIVKEY_OUT data from MLDSA\n");
                reg_ptr = (uint32_t *) CLP_MLDSA_REG_MLDSA_PRIVKEY_OUT_BASE_ADDR;
                end_addr = MLDSA87_PRIVKEY_SIZE;
                break;
            case 2:
                printf("\nTry to Load zeroized SIGNATURE data from MLDSA\n");
                reg_ptr = (uint32_t *) CLP_MLDSA_REG_MLDSA_SIGNATURE_BASE_ADDR;
                end_addr = MLDSA87_SIGN_SIZE;
                break;
            case 3:
                printf("\nTry to Load zeroized PRIVKEY_IN data from MLDSA\n");
                reg_ptr = (uint32_t *) CLP_MLDSA_REG_MLDSA_PRIVKEY_IN_BASE_ADDR;
                end_addr = MLDSA87_PRIVKEY_SIZE;
                break;
        }

        offset = 0;
        while ((*status_ptr == 0) & (offset < end_addr)) {
            // Try to Overwrite data in MLDSA
            *reg_ptr = rand() % 0xffffffff;
            if (*reg_ptr != 0) {
                printf("At offset [%d], mldsa data mismatch!\n", offset);
                printf("Actual   data: 0x%x\n", *reg_ptr);
                printf("Expected data: 0x%x\n", 0);
                printf("%c", fail_cmd);
                while(1);
            }
            reg_ptr++;
            offset++;
        }

        cptra_intr_rcv.mldsa_notif = 0;
    }

    printf("%c",0xff); //End the test
    
}


