// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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
#include <string.h>
#include <stdint.h>
#include "printf.h"

/* --------------- Global symbols/typedefs --------------- */
enum doe_cmd_e {
    DOE_IDLE = 0,
    DOE_UDS = 1,
    DOE_FE = 2,
    DOE_CLEAR_OBF_SECRETS = 3
};

/* --------------- Global vars --------------- */
volatile char*    stdout           = (char *)STDOUT;
volatile uint32_t intr_count       = 0;

#ifdef CPT_VERBOSITY    
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else    
    enum printf_verbosity verbosity_g = LOW;
#endif

/* --------------- Function Prototypes --------------- */
void init_doe();
void idevid();
void ldevid();
void mbox_fw();

/* --------------- Function Definitions --------------- */
void main() {
    
    printf("----------------------------------\n");
    printf(" Caliptra Crypto Demo!!\n"           );
    printf("----------------------------------\n");

    init_interrupts();

    init_doe();

    idevid();

    ldevid();

    mbox_fw();
    
    printf("----------------------------------\n");
    printf(" Demo completed successfully! \n"    );
    printf("----------------------------------\n");
}

void init_doe() {
    uint8_t offset;
    volatile uint32_t* reg_ptr;
    uint32_t iv_data_uds[] = {0x2eb94297,
                              0x77285196,
                              0x3dd39a1e,
                              0xb95d438f};
    uint32_t iv_data_fe[] = {0x14451624,
                             0x6a752c32,
                             0x9056d884,
                             0xdaf3c89d};

    // Write IV
    reg_ptr = (uint32_t*) CLP_DOE_REG_DOE_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_DOE_REG_DOE_IV_3) {
        *reg_ptr++ = iv_data_uds[offset++];
    }

    //start UDS and store in KV0
    lsu_write_32(CLP_DOE_REG_DOE_CTRL, DOE_UDS);

    // Check that UDS flow is done
    while((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_VALID_MASK) == 0);

    // Write IV
    reg_ptr = (uint32_t*) CLP_DOE_REG_DOE_IV_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_DOE_REG_DOE_IV_3) {
        *reg_ptr++ = iv_data_fe[offset++];
    }

    //start FE and store in KV6/7
    lsu_write_32(CLP_DOE_REG_DOE_CTRL, DOE_FE | (0x6 << DOE_REG_DOE_CTRL_DEST_LOW)); // TODO replace 0x6 with entry indicators

    // Check that FE flow is done
    while((lsu_read_32(CLP_DOE_REG_DOE_STATUS) & DOE_REG_DOE_STATUS_VALID_MASK) == 0);

    // Clear Secrets
    lsu_write_32(CLP_DOE_REG_DOE_CTRL, DOE_CLEAR_OBF_SECRETS);

}

void idevid() {
    uint8_t offset;
    volatile uint32_t* reg_ptr;
    //this is the key 384-bit
    uint32_t hw_data[] = {0x0b0b0b0b,
                          0x0b0b0b0b,
                          0x0b0b0b0b,
                          0x0b0b0b0b,
                          0x0b0b0b0b,
                          0x0b0b0b0b,
                          0x0b0b0b0b,
                          0x0b0b0b0b,
                          0x0b0b0b0b,
                          0x0b0b0b0b,
                          0x0b0b0b0b,
                          0x0b0b0b0b};

    // Load key from hw_data and write to PCR
    reg_ptr = (uint32_t*) CLP_KV_REG_PCR_ENTRY_0_0;
    offset = 0;
    while (offset < HMAC_KEY_NUM_DWORDS) {
        *reg_ptr++ = hw_data[offset++];
    }

    // Program KEY Read
    lsu_write_32(CLP_HMAC_REG_HMAC384_KV_RD_KEY_CTRL, HMAC_REG_HMAC384_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                                  HMAC_REG_HMAC384_KV_RD_KEY_CTRL_ENTRY_IS_PCR_MASK |
                                                                  (0xB << HMAC_REG_HMAC384_KV_RD_KEY_CTRL_ENTRY_DATA_SIZE_LOW));

    // Check that HMAC KEY is loaded
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_RD_KEY_STATUS) & HMAC_REG_HMAC384_KV_RD_KEY_STATUS_VALID_MASK) == 0);

    // Program BLOCK read
    lsu_write_32(CLP_HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL, HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL_READ_EN_MASK |
                                                                    (0xB << HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL_ENTRY_DATA_SIZE_LOW));

    // Check that HMAC BLOCK is loaded
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_RD_BLOCK_STATUS) & HMAC_REG_HMAC384_KV_RD_BLOCK_STATUS_VALID_MASK) == 0);

    // Program DEST write
    lsu_write_32(CLP_HMAC_REG_HMAC384_KV_WR_CTRL, HMAC_REG_HMAC384_KV_WR_CTRL_WRITE_EN_MASK |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_SHA_BLOCK_DEST_VALID_MASK |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_ECC_MSG_DEST_VALID_MASK);

    // Enable HMAC core
    lsu_write_32(CLP_HMAC_REG_HMAC384_CTRL, HMAC_REG_HMAC384_CTRL_INIT_MASK);

    // wait for HMAC process - check dest done
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_WR_STATUS) & HMAC_REG_HMAC384_KV_WR_STATUS_VALID_MASK) == 0);

    //ecc stuff would be here

}

void ldevid() {
    volatile uint32_t* reg_ptr;
    uint8_t offset = 0;
    //this is the pad block 1024-bit
    uint32_t pad_block[] = {0x80000000,
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
                            0x00000000,
                            0x00000000,
                            0x00000800};

    // Program KEY to come from idevid in entry 0 of keyvault
    lsu_write_32(CLP_HMAC_REG_HMAC384_KV_RD_KEY_CTRL, HMAC_REG_HMAC384_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                                  (0xB << HMAC_REG_HMAC384_KV_RD_KEY_CTRL_ENTRY_DATA_SIZE_LOW));

    // Check that HMAC KEY is loaded
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_RD_KEY_STATUS) & HMAC_REG_HMAC384_KV_RD_KEY_STATUS_VALID_MASK) == 0);

    // Program BLOCK to come from FE in entry 6/7 of keyvault
    lsu_write_32(CLP_HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL, HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL_READ_EN_MASK |
                                                                    (0x6 << HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL_READ_ENTRY_LOW) | /* TODO replace 0x6 with entry indicators */
                                                                    (0x1F << HMAC_REG_HMAC384_KV_RD_BLOCK_CTRL_ENTRY_DATA_SIZE_LOW));

    // Check that HMAC BLOCK is loaded
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_RD_BLOCK_STATUS) & HMAC_REG_HMAC384_KV_RD_BLOCK_STATUS_VALID_MASK) == 0);

    // Program DEST write
    lsu_write_32(CLP_HMAC_REG_HMAC384_KV_WR_CTRL, HMAC_REG_HMAC384_KV_WR_CTRL_WRITE_EN_MASK |
                                                              (0x1 << HMAC_REG_HMAC384_KV_WR_CTRL_WRITE_ENTRY_LOW)  | /* TODO replace 0x1 with entry indicators */
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_SHA_BLOCK_DEST_VALID_MASK |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_ECC_MSG_DEST_VALID_MASK);

    // Enable HMAC core
    lsu_write_32(CLP_HMAC_REG_HMAC384_CTRL, HMAC_REG_HMAC384_CTRL_INIT_MASK);

    // wait for HMAC process
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_STATUS) & HMAC_REG_HMAC384_STATUS_VALID_MASK) == 0);

    // Write PAD for 1024 size block
    // FE is 1024 so we did init with the full data
    // Now we need to do next with a full pad and size 
    reg_ptr = (uint32_t *) CLP_HMAC_REG_HMAC384_BLOCK_0;
    offset = 0;
    while (reg_ptr <= (uint32_t*) CLP_HMAC_REG_HMAC384_BLOCK_31) {
        *reg_ptr++ = pad_block[offset++];
    }

    // Program DEST write
    lsu_write_32(CLP_HMAC_REG_HMAC384_KV_WR_CTRL, HMAC_REG_HMAC384_KV_WR_CTRL_WRITE_EN_MASK |
                                                              (0x1 << HMAC_REG_HMAC384_KV_WR_CTRL_WRITE_ENTRY_LOW)  | /* TODO replace 0x1 with entry indicators */
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_HMAC_KEY_DEST_VALID_MASK  |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_HMAC_BLOCK_DEST_VALID_MASK|
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_SHA_BLOCK_DEST_VALID_MASK |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_ECC_PKEY_DEST_VALID_MASK  |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_ECC_SEED_DEST_VALID_MASK  |
                                                              HMAC_REG_HMAC384_KV_WR_CTRL_ECC_MSG_DEST_VALID_MASK);

    // Give the next command to HMAC core
    lsu_write_32(CLP_HMAC_REG_HMAC384_CTRL, HMAC_REG_HMAC384_CTRL_NEXT_MASK);

    // wait for HMAC process - check dest done
    while((lsu_read_32(CLP_HMAC_REG_HMAC384_KV_WR_STATUS) & HMAC_REG_HMAC384_KV_WR_STATUS_VALID_MASK) == 0);
}

void mbox_fw() {
    uint32_t dlen;
    uint32_t data;

    //set ready for FW
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS, SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FW_MASK);

    // Roughly equivalent to .rept 99 "nop" since the loop requires 3 (5?) ops each iteration
    // nop
    // addi slp, slp, 1 (<< may be three ops to lw, addi, and sw)
    // blt slp, 33, forloop
    for (uint16_t slp = 0; slp < 33; slp++) {
        __asm__ volatile ("nop");
    }

    //poll for mbox data avail
    while((lsu_read_32(CLP_MBOX_CSR_MBOX_EXECUTE) & MBOX_CSR_MBOX_EXECUTE_EXECUTE_MASK) == 0);

    //read mbox command
    data = lsu_read_32(CLP_MBOX_CSR_MBOX_CMD);
    /* then drop it on the ground... */

    //read mbox dlen
    dlen = lsu_read_32(CLP_MBOX_CSR_MBOX_DLEN);

    //read from mbox
    for (uint32_t byt_cnt=0; byt_cnt < dlen; byt_cnt += 4) {
        data = lsu_read_32(CLP_MBOX_CSR_MBOX_DATAOUT);
        /* then drop it on the ground... */
    }

    //clear FE 
    lsu_write_32(CLP_KV_REG_KEY_CTRL_6, KV_REG_KEY_CTRL_6_CLEAR_MASK);
    lsu_write_32(CLP_KV_REG_KEY_CTRL_7, KV_REG_KEY_CTRL_7_CLEAR_MASK);

    //set ready for runtime
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS, SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK);
}
