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
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "soc_ifc.h"
#include "hmac.h"
#include "aes.h"
#include "keyvault.h"


volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t  fail      __attribute__((section(".dccm.persistent"))) = 0;
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


volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define MAX_FIFO_SIZE 1024
uint32_t rand_payload[MAX_FIFO_SIZE*2];

enum tb_fifo_mode {
    RCVY_EMU_TOGGLE     = 0x88,
    FIFO_AUTO_READ_ON   = 0x8a,
    FIFO_AUTO_WRITE_ON  = 0x8b,
    FIFO_AUTO_READ_OFF  = 0x8c,
    FIFO_AUTO_WRITE_OFF = 0x8d,
    FIFO_CLEAR          = 0x8e,
    RAND_DELAY_TOGGLE   = 0x8f
};

enum err_inj_type {
//    cmd_inv_rd_route    ,
    cmd_inv_wr_route_kv    ,
    cmd_inv_wr_route_invld_range    ,
    cmd_inv_route_combo ,
    cmd_inv_route_combo_kv ,
    cmd_inv_src_addr    ,
    cmd_inv_dst_addr    ,
    cmd_inv_dst_addr_kv ,
    cmd_inv_byte_count  ,
    cmd_inv_byte_count_kv  ,
    cmd_inv_rd_fixed    ,
    cmd_inv_wr_fixed    ,
    cmd_inv_wr_fixed_kv ,
    cmd_inv_block_size,
    cmd_inv_mbox_lock
//    cmd_inv_sha_lock
};

void nmi_handler() {
    VPRINTF(FATAL, "NMI");
}
uint8_t soc_ifc_axi_dma_inject_inv_error(enum err_inj_type err_type) {
    uint32_t reg;
    uint64_t src_addr;
    uint64_t dst_addr;
    uint32_t rd_route;
    uint32_t wr_route;
    uint8_t  rd_fixed;
    uint8_t  wr_fixed;
    uint32_t byte_count;
    uint16_t block_size;

    src_addr   = AXI_SRAM_BASE_ADDR + ((err_type == cmd_inv_src_addr) ? 0x3 : 0x0);
    dst_addr   = (err_type == cmd_inv_mbox_lock) ? 0x4000 : (AXI_SRAM_BASE_ADDR + 0x4000 + ((err_type == cmd_inv_dst_addr) ? 0x3 : 0x0));
    if (err_type == cmd_inv_mbox_lock) {
        dst_addr = 0x4000; // MBOX base address
    } else if (err_type == cmd_inv_dst_addr) {
        dst_addr = AXI_SRAM_BASE_ADDR + 0x4000 + 0x3; // SRAM address
    } else if (err_type == cmd_inv_dst_addr_kv) {
        uint64_t forbidden_addr = lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_H); 
        forbidden_addr = (forbidden_addr << 32) | 
                    lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_L);
        // Generate dword-aligned addresses directly
        do {
            dst_addr = ((uint64_t)rand() << 34) | ((uint64_t)rand() << 2);  // Always multiple of 4
        } while (dst_addr == forbidden_addr);
    } else {
        dst_addr = lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_H);
        dst_addr = (dst_addr << 32) | 
                    lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_L);
    }

    if(err_type == cmd_inv_rd_fixed) {
        rd_route = axi_dma_rd_route_DISABLE;
    } else if (err_type == cmd_inv_route_combo) {
        rd_route = axi_dma_rd_route_AHB_FIFO;
    } else if (err_type == cmd_inv_mbox_lock) {
        rd_route = axi_dma_rd_route_MBOX;
    } else if (err_type == cmd_inv_route_combo_kv) {
        rd_route = 1 + (rand() % 3);  // 1, 2, or 3 (excludes 0x0/DISABLE)
    } else if (err_type == cmd_inv_wr_route_kv || err_type == cmd_inv_byte_count_kv || err_type == cmd_inv_dst_addr_kv || err_type == cmd_inv_wr_fixed_kv) {
        rd_route = axi_dma_rd_route_DISABLE;
    } else {
        rd_route = axi_dma_rd_route_AXI_WR; // Default to valid route
    }

    if(err_type == cmd_inv_wr_fixed) {
        wr_route = axi_dma_wr_route_DISABLE;
    } else if (err_type == cmd_inv_route_combo) {
        wr_route = axi_dma_wr_route_AHB_FIFO;
    } else if (err_type == cmd_inv_mbox_lock) {
        wr_route = axi_dma_wr_route_DISABLE;
    } else if (err_type == cmd_inv_wr_route_kv || err_type == cmd_inv_byte_count_kv || err_type == cmd_inv_dst_addr_kv || err_type == cmd_inv_wr_fixed_kv || err_type == cmd_inv_route_combo_kv) {
        wr_route = axi_dma_wr_route_KEYVAULT; // Invalid becasue OCP LOCK IN PROGRESS not set
    } else if (err_type == cmd_inv_wr_route_invld_range) {
        // Invalid range 0x5-0xF
        wr_route = 0x5 + (rand() % 11);
    } else {
        wr_route = axi_dma_wr_route_AXI_RD; // Default to valid route
    }
    rd_fixed   = err_type == cmd_inv_rd_fixed;
    wr_fixed   = err_type == cmd_inv_wr_fixed || err_type == cmd_inv_wr_fixed_kv;
    if (err_type == cmd_inv_byte_count) {
        byte_count = 0x43; // Invalid byte count
    } else if (err_type == cmd_inv_byte_count_kv) {
        do {
            byte_count = rand() % 0x10000;  
            byte_count = (byte_count + 3) & ~3;  // Round up to next dword boundary
        } while (byte_count == CLP_SOC_IFC_REG_SS_KEY_RELEASE_SIZE);
    } else {
        byte_count = lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_SIZE) & SOC_IFC_REG_SS_KEY_RELEASE_SIZE_SIZE_MASK; // Invalid byte count
        byte_count = 0x40; // Default valid byte count
    }
    block_size = (err_type == cmd_inv_block_size) ? 0x13 : 0x00;

    VPRINTF(HIGH, "param: src_addr   0x%x 0x%x\n", (uint32_t) (src_addr >> 32) , (uint32_t) (src_addr & 0xffffffff));
    VPRINTF(HIGH, "param: dst_addr   0x%x 0x%x\n", (uint32_t) (dst_addr >> 32) , (uint32_t) (dst_addr & 0xffffffff));
    VPRINTF(HIGH, "param: rd_route   0x%x\n"     , rd_route  );
    VPRINTF(HIGH, "param: wr_route   0x%x\n"     , wr_route  );
    VPRINTF(HIGH, "param: rd_fixed   0x%x\n"     , rd_fixed  );
    VPRINTF(HIGH, "param: wr_fixed   0x%x\n"     , wr_fixed  );
    VPRINTF(HIGH, "param: byte_count 0x%x\n"     , byte_count);
    VPRINTF(HIGH, "param: block_size 0x%x\n"     , block_size);

    // Disable txn_done interrupt since we'll poll it
    reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
    lsu_write_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, reg & ~AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_TXN_DONE_EN_MASK);

    // Arm the Error command
    while (lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_BUSY_MASK);
    VPRINTF(LOW, "FW: Arm err command\n");
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_L,  src_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_H, (src_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_L,  dst_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_H, (dst_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_BYTE_COUNT, byte_count);
    lsu_write_32(CLP_AXI_DMA_REG_BLOCK_SIZE, (uint32_t) block_size);
    reg = (AXI_DMA_REG_CTRL_GO_MASK)                      |
          (rd_route << AXI_DMA_REG_CTRL_RD_ROUTE_LOW)     |
          (wr_route << AXI_DMA_REG_CTRL_WR_ROUTE_LOW)     |
          (rd_fixed ? AXI_DMA_REG_CTRL_RD_FIXED_MASK : 0) |
          (wr_fixed ? AXI_DMA_REG_CTRL_WR_FIXED_MASK : 0);
    lsu_write_32(CLP_AXI_DMA_REG_CTRL, reg);

    // Check completion (error state expected)
    reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    VPRINTF(LOW, "FW: Poll DMA status\n");
    while ((reg & AXI_DMA_REG_STATUS0_BUSY_MASK) && !(reg & AXI_DMA_REG_STATUS0_ERROR_MASK)) {
        reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    }

    // Check status
    VPRINTF(LOW, "FW: Check DMA status\n");
    if (reg & AXI_DMA_REG_STATUS0_ERROR_MASK) {
        VPRINTF(LOW, "AXI DMA reports err status for err injection xfer\n");
        lsu_write_32(CLP_AXI_DMA_REG_CTRL, AXI_DMA_REG_CTRL_FLUSH_MASK);
    } else {
        VPRINTF(ERROR, "ERROR: AXI DMA reports success status for err injection xfer!\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
        //return 1;
    }

    // Reenable txn_done interrupt
    reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
    lsu_write_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, reg | AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_TXN_DONE_EN_MASK);

    return 0;
}

void populate_kv_slot_aes_ecb() {
    //CASE1
    VPRINTF(LOW, "Test Case 1 - ECB\n");
    
    // AES_KEY = e7f1293c6f23a53289143df1399e784cb71180e3830c3869fd725fe78f0b6480
    //const char plaintext_str[]  = "2ea4ca977176ebb032748adee0bafd06e7dff005c5693781e9304ef63013153bf0173c4b62916cb686c11e9632abbc4f31cb6297a018e2d50c9752a6bbde1f3b78b7ba66f9fc1828b262380f8821fa5dbc8fc44985e9b77a533bb43edfa2ca45";
    //const char ciphertext_str[] = "0aa9a935b694b29dd3d3e251084e7c4d393eebd18438b8d2dd609513eb21b039e27a20ca93a08897c4de30ce248867eac0e67fc54595a2559df10d8fb49fd7e1767410960f39e2339ebc793f55ef170e438e9e1061b1b17cbdf39dbd84e7f2db";
    const char plaintext_str[]  = "2ea4ca977176ebb032748adee0bafd06e7dff005c5693781e9304ef63013153bf0173c4b62916cb686c11e9632abbc4f31cb6297a018e2d50c9752a6bbde1f3b";
    const char ciphertext_str[] = "0aa9a935b694b29dd3d3e251084e7c4d393eebd18438b8d2dd609513eb21b039e27a20ca93a08897c4de30ce248867eac0e67fc54595a2559df10d8fb49fd7e1";

    aes_op_e op = AES_DEC;
    aes_mode_e mode = AES_ECB;
    aes_key_len_e key_len = AES_256;
    aes_key_t aes_key;
    aes_key_o_t aes_key_o;
    aes_flow_t aes_input;

    uint32_t plaintext[32]; //arbitrary length here
    uint32_t plaintext_length;
    uint32_t ciphertext[32]; //arbitrary length here
    uint32_t ciphertext_length;

    hex_to_uint32_array(ciphertext_str, ciphertext, &ciphertext_length);
    hex_to_uint32_array(plaintext_str, plaintext, &plaintext_length);
    VPRINTF(LOW, "PLAINTEXT Length: 0x%x\n", plaintext_length);

    //Key from KV
    aes_key.kv_intf = FALSE;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = 0x0;
        aes_key.key_share1[i] = 0x00000000;
    } 
    
    // Key to KV
    aes_key_o.kv_intf = TRUE;
    aes_key_o.kv_id = 23; //KV slot 23
    aes_key_o.dest_valid = (dest_valid_t){0}; // Clear all destinations
    aes_key_o.dest_valid.dma_data = 1; // Only allow DMA access


    aes_input.key = aes_key;
    aes_input.iv = 0;
    aes_input.aad = 0;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.key_o = aes_key_o;

    //Run ENC
    aes_flow(op, mode, key_len, aes_input);




}

void populate_kv_slot_hmac512(uint8_t tag_kv_id, uint32_t expected_tag[16]) {
    VPRINTF(LOW, "FW: Generating HMAC512 into KV slot: 0x%x\n", tag_kv_id);

    uint32_t block[32] =   {0x48692054,
                            0x68657265,
                            0x80000000,
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
                            0x00000440};


    uint32_t hmac512_lfsr_seed_data[12] =  {0xC8F518D4,
                                    0xF3AA1BD4,
                                    0x6ED56C1C,
                                    0x3C9E16FB,
                                    0x800AF504,
                                    0xC8F518D4,
                                    0xF3AA1BD4,
                                    0x6ED56C1C,
                                    0x3C9E16FB,
                                    0x800AF504,
                                    0xC8F518D4,
                                    0xF3AA1BD4}; 

    uint32_t hmac512_expected_tag[16] =   {0x637edc6e,
                                    0x01dce7e6,
                                    0x742a9945,
                                    0x1aae82df,
                                    0x23da3e92,
                                    0x439e590e,
                                    0x43e761b3,
                                    0x3e910fb8,
                                    0xac2878eb,
                                    0xd5803f6f,
                                    0x0b61dbce,
                                    0x5e251ff8,
                                    0x789a4722,
                                    0xc1be65ae,
                                    0xa45fd464,
                                    0xe89f8f5b}; 
    for (int i = 0; i < 16; i++) {
        expected_tag[i] = hmac512_expected_tag[i];
    }

    uint8_t hmacblock_kv_id     = 0x1;

    hmac_io hmac512_key;
    hmac_io hmac512_block;
    hmac_io hmac512_lfsr_seed;
    hmac_io hmac512_tag;

    hmac512_key.kv_intf = TRUE;
    hmac512_key.kv_id = 4;

    hmac512_block.kv_intf = FALSE;
    hmac512_block.kv_id = hmacblock_kv_id;
    hmac512_block.data_size = 32; 
    for (int i = 0; i < hmac512_block.data_size; i++)
        hmac512_block.data[i] = block[i];

    hmac512_lfsr_seed.kv_intf = FALSE;
    hmac512_lfsr_seed.data_size = 12; 
    for (int i = 0; i < hmac512_lfsr_seed.data_size; i++)
        hmac512_lfsr_seed.data[i] = hmac512_lfsr_seed_data[i];

    hmac512_tag.kv_intf = TRUE;
    hmac512_tag.kv_id = tag_kv_id;
    hmac512_tag.data_size = 16; 
    for (int i = 0; i < hmac512_tag.data_size; i++)
        hmac512_tag.data[i] = hmac512_expected_tag[i];


    //inject hmac512_key to kv key reg (in RTL)
    uint8_t key512_inject_cmd = 0xa8 + (hmac512_key.kv_id & 0x7);
    printf("%c", key512_inject_cmd);

    hmac512_flow(hmac512_key, hmac512_block, hmac512_lfsr_seed, hmac512_tag, TRUE);
    hmac_zeroize();

    VPRINTF(LOW, "FW: FINISHED HMAC512 key generation\n");


}


void main(void) {
        int argc=0;
        char *argv[1];
        uint32_t reg;
        uint32_t send_payload[16] = {
            0xabadface,
            0xba5eba11,
            0xcafebabe,
            0xdeadbeef,
            0xebbf1000,
            0xfadefee1,
            0x12344321,
            0xa5a5a5a5,
            0x14351375,
            0x8afdbe82,
            0xafb832ba,
            0x8843151a,
            0xbad831b1,
            0xf831ba83,
            0xad813451,
            0x67120ad3
        };
        uint32_t mbox_send_payload[16] = {
            0x0991c03c,
            0x7bc14838,
            0xb05f2c82,
            0x7b233274,
            0x01b7ba27,
            0x3f24db45,
            0xd945c472,
            0xabac3989,
            0x64af1d5e,
            0xda068da4,
            0xeb9102ab,
            0xf796de3e,
            0x88fc6af8,
            0x1a169287,
            0xc9a6e724,
            0x667f9dd5
        };
        uint32_t fixed_send_payload[17] = {
            0x00000000,
            0x11111111,
            0x22222222,
            0x33333333,
            0x44444444,
            0x55555555,
            0x66666666,
            0x77777777,
            0x88888888,
            0x99999999,
            0xaaaaaaaa,
            0xbbbbbbbb,
            0xcccccccc,
            0xdddddddd,
            0xeeeeeeee,
            0xffffffff,
            0x234562ab
        };
        uint32_t post_rst_send_payload[16] = {
            0xC8F518D4,
            0xF3AA1BD4,
            0x6ED56C1C,
            0x3C9E16FB,
            0x5112DBBD,
            0x0AAE67FE,
            0xF26B465B,
            0xE935B48E,
            0x800AF504,
            0xDB988435,
            0x48C5F623,
            0xEE115F73,
            0xD4C62ABC,
            0x06D303B5,
            0xD90D9A17,
            0x5087290D
        };
        uint32_t read_payload[16];
        uint32_t mbox_read_payload[17];
        uint32_t fixed_read_payload[17];
        
        /* Intializes random number generator */  //TODO    
        srand(time);


        VPRINTF(LOW, "----------------------------------\nSmoke Test AXI DMA  !!\n----------------------------------\n");
        rst_count++;

        //set NMI vector
        lsu_write_32((uintptr_t) (CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR), (uint32_t) (nmi_handler));

        // Setup the interrupt CSR configuration
        init_interrupts();
        reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
        lsu_write_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, reg & ~(AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_EMPTY_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_EMPTY_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_FULL_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_FULL_EN_MASK));

        if(!(lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK)) {
            // If OCP LOCK mode is not enable we need to check if OCP_LOCK_IN_PROGRESS can be set
            lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK);
            VPRINTF(LOW, "OCP_LOCK_IN_PROGRESS: 0x%x\n", lsu_read_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL));
            if((lsu_read_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL) & SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK) != 0) {
                VPRINTF(FATAL, "OCP_LOCK_IN_PROGRESS set when OCP_LOCK_MODE_EN not set!\n");
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }

        // Test each malformed command check
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_route_combo))          { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_src_addr   ))          { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_dst_addr   ))          { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_byte_count ))          { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_block_size ))          { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_rd_fixed   ))          { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_wr_fixed   ))          { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_mbox_lock  ))          { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_wr_route_invld_range)) { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_wr_route_kv))          { fail = 1; }
        if((lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK)) {
            lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK);
            if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_route_combo_kv))   { fail = 1; } // Can only be tested after IN PROGRESS has been set
            if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_dst_addr_kv))      { fail = 1; } // Can only be tested after IN PROGRESS has been set
            if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_byte_count_kv))    { fail = 1; } // Can only be tested after IN PROGRESS has been set
            if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_wr_fixed_kv))      { fail = 1; } // Can only be tested after IN PROGRESS has been set
        }

        // ===========================================================================
        // If reset was executed, try to run another simple DMA test to check for life
        // ===========================================================================
        if (rst_count == 2) {
            VPRINTF(LOW, "Observed reset! Running some short DMA tests for life\n");

            // ===========================================================================
            // Send data through AHB interface to AXI_DMA, target the AXI SRAM
            // ===========================================================================
            VPRINTF(LOW, "Sending payload via AHB i/f\n");
            soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR, 0, post_rst_send_payload, 16*4, 0);


            // ===========================================================================
            // Move data from one address to another in AXI SRAM
            // ===========================================================================
            VPRINTF(LOW, "Moving payload at SRAM via axi-to-axi xfer\n");
            soc_ifc_axi_dma_send_axi_to_axi(AXI_SRAM_BASE_ADDR, 0, AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, (16)*4, 0, 0, 0);

            // ===========================================================================
            // Read data back from AXI SRAM and confirm it matches
            // ===========================================================================
            VPRINTF(LOW, "Reading payload via AHB i/f\n");
            soc_ifc_axi_dma_read_ahb_payload(AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, read_payload, 16*4, 0);
            for (uint8_t ii = 0; ii < 16; ii++) {
                if (read_payload[ii] != post_rst_send_payload[ii]) {
                    VPRINTF(ERROR, "read_payload[%d] (0x%x) does not match post_rst_send_payload[%d] (0x%x)\n", ii, read_payload[ii], ii, post_rst_send_payload[ii]);
                    fail = 1;
                }
            }

        } else if (rst_count == 1) {

            if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_RESET_REASON) == SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK) {
                VPRINTF(FATAL, "rst_count is still 1 after warm reset!\n");
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }

            SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);

            // ===========================================================================
            // Send data through AHB interface to AXI_DMA, target the AXI SRAM
            // ===========================================================================
            VPRINTF(LOW, "Sending payload via AHB i/f\n");
            soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR, 0, send_payload, 16*4, 0);


            // ===========================================================================
            // Send data through Mailbox to AXI_DMA, target the AXI SRAM
            // ===========================================================================
            VPRINTF(LOW, "Writing payload to Mailbox via Direct Mode\n");
            // Acquire the mailbox lock
            if (soc_ifc_mbox_acquire_lock(1)) {
                VPRINTF(ERROR, "Acquire mailbox lock failed\n");
                fail = 1;
            }
            // Write data into mailbox using direct-mode
            for (uint32_t dw = 0; dw < 16; dw++) {
                lsu_write_32(CLP_MBOX_SRAM_BASE_ADDR + 0x4400 + (dw << 2), mbox_send_payload[dw]);
            }
            lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
            VPRINTF(LOW, "Sending payload from Mailbox\n");
            if (soc_ifc_axi_dma_send_mbox_payload(0x4400, AXI_SRAM_BASE_ADDR + 16*4, 0, 16*4, 0)) {
                fail = 1;
            }


            // ===========================================================================
            // Send data through AHB interface to AXI_DMA, target the AXI SRAM
            // ===========================================================================
            // Use a FIXED transfer (only the final beat should be present at the target address)
            VPRINTF(LOW, "Sending fixed payload via AHB i/f\n");
            soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR + 2*16*4, 1, fixed_send_payload, 17*4, 0);


            // ===========================================================================
            // Move data from one address to another in AXI SRAM
            // ===========================================================================
            VPRINTF(LOW, "Moving payload at SRAM via axi-to-axi xfer\n");
            soc_ifc_axi_dma_send_axi_to_axi(AXI_SRAM_BASE_ADDR, 0, AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, (2*16+1)*4, 0, 0, 0);


            // ===========================================================================
            // Read data back from AXI SRAM and confirm it matches
            // ===========================================================================
            VPRINTF(LOW, "Reading payload via AHB i/f\n");
            soc_ifc_axi_dma_read_ahb_payload(AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, read_payload, 16*4, 0);
            for (uint8_t ii = 0; ii < 16; ii++) {
                if (read_payload[ii] != send_payload[ii]) {
                    VPRINTF(ERROR, "read_payload[%d] (0x%x) does not match send_payload[%d] (0x%x)\n", ii, read_payload[ii], ii, send_payload[ii]);
                    fail = 1;
                }
            }


            // ===========================================================================
            // Read data back through mailbox using direct-mode
            // ===========================================================================
            VPRINTF(LOW, "Reading payload to Mailbox\n");
            if (soc_ifc_axi_dma_read_mbox_payload(AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2 + 16*4, 0x8800, 0, 17*4, 0)) {
                fail = 1;
            }
            VPRINTF(LOW, "Reading payload from Mailbox via Direct Mode\n");
            // Acquire the mailbox lock
            if (soc_ifc_mbox_acquire_lock(1)) {
                VPRINTF(ERROR, "Acquire mailbox lock failed\n");
                fail = 1;
            }
            for (uint32_t dw = 0; dw < 16; dw++) {
                mbox_read_payload[dw] = lsu_read_32(CLP_MBOX_SRAM_BASE_ADDR + 0x8800 + (dw << 2));
                if (mbox_read_payload[dw] != mbox_send_payload[dw]) {
                    VPRINTF(ERROR, "mbox_read_payload[%d] (0x%x) does not match mbox_send_payload[%d] (0x%x)\n", dw, mbox_read_payload[dw], dw, mbox_send_payload[dw]);
                    fail = 1;
                }
            }
            mbox_read_payload[16] = lsu_read_32(CLP_MBOX_SRAM_BASE_ADDR + 0x8800 + (16 << 2));
            if (mbox_read_payload[16] != fixed_send_payload[16]) {
                VPRINTF(ERROR, "mbox_read_payload[%d] (0x%x) does not match fixed_send_payload[%d] (0x%x)\n", 16, mbox_read_payload[16], 16, fixed_send_payload[16]);
                fail = 1;
            }
            lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

            // ===========================================================================
            // FIFO test
            // ===========================================================================
            // Send data through AHB interface to AXI_DMA, target the AXI FIFO
            // Use a FIXED transfer
            VPRINTF(LOW, "Sending fixed payload to FIFO via AHB i/f\n");
            soc_ifc_axi_dma_send_ahb_payload(AXI_FIFO_BASE_ADDR, 1, fixed_send_payload, 17*4, 0);

            // Read data back from AXI FIFO and confirm it matches
            VPRINTF(LOW, "Reading fixed payload from FIFO via AHB i/f\n");
            soc_ifc_axi_dma_read_ahb_payload(AXI_FIFO_BASE_ADDR, 1, fixed_read_payload, 17*4, 0);
            for (uint8_t ii = 0; ii < 17; ii++) {
                if (fixed_read_payload[ii] != fixed_send_payload[ii]) {
                    VPRINTF(ERROR, "fixed_read_payload[%d] (0x%x) does not match fixed_send_payload[%d] (0x%x)\n", ii, fixed_read_payload[ii], ii, fixed_send_payload[ii]);
                    fail = 1;
                }
            }

            SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);


            // ===========================================================================
            // Read rand FIFO data into mailbox
            // ===========================================================================
            // Set auto-write
            VPRINTF(LOW, "Enable FIFO to auto-write\n");
            SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

            VPRINTF(LOW, "Reading rand payload to Mailbox\n");
            if (soc_ifc_axi_dma_read_mbox_payload(AXI_FIFO_BASE_ADDR, 0x0, 1, MAX_FIFO_SIZE*2, 0)) {
                fail = 1;
            }

            // Clear auto-write
            VPRINTF(LOW, "Disable FIFO to auto-write\n");
            SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
            SEND_STDOUT_CTRL(FIFO_CLEAR);


            // ===========================================================================
            // Send rand data through Mailbox to AXI_DMA, target the AXI FIFO
            // ===========================================================================

            // Set auto-read
            VPRINTF(LOW, "Set FIFO to auto-read\n");
            SEND_STDOUT_CTRL(FIFO_AUTO_READ_ON);

            VPRINTF(LOW, "Sending payload from Mailbox\n");
            if (soc_ifc_axi_dma_send_mbox_payload(0, AXI_FIFO_BASE_ADDR, 1, MAX_FIFO_SIZE*2, 0)) {
                fail = 1;
            }

            // Clear auto-read
            VPRINTF(LOW, "Disable FIFO to auto-read\n");
            SEND_STDOUT_CTRL(FIFO_AUTO_READ_OFF);
            SEND_STDOUT_CTRL(FIFO_CLEAR);


            // ===========================================================================
            // Auto FIFO test
            // ===========================================================================

            // Set auto-read
            VPRINTF(LOW, "Set FIFO to auto-read\n");
            SEND_STDOUT_CTRL(FIFO_AUTO_READ_ON);

            // Generate rand data
            srand(17);
            for (uint32_t ii = 0; ii < (MAX_FIFO_SIZE/2); ii++) {
                rand_payload[ii] = rand();
                if ((ii & 0x7f) == 0x40) putchar('.');
            }
            putchar('\n');

            // Send data through AHB interface to AXI_DMA, target the AXI FIFO
            // Use a FIXED transfer
            // Use total byte-count that is 2x FIFO depth
            VPRINTF(LOW, "Sending large rand payload to FIFO via AHB i/f\n");
            soc_ifc_axi_dma_send_ahb_payload(AXI_FIFO_BASE_ADDR, 1, rand_payload, MAX_FIFO_SIZE*2, 0);

            // Clear auto-read
            VPRINTF(LOW, "Disable FIFO to auto-read\n");
            SEND_STDOUT_CTRL(FIFO_AUTO_READ_OFF);
            SEND_STDOUT_CTRL(FIFO_CLEAR);
            // Set auto-write
            VPRINTF(LOW, "Enable FIFO to auto-write\n");
            SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

            // Read data from AXI FIFO
            VPRINTF(LOW, "Reading large payload from FIFO via AHB i/f\n");
            soc_ifc_axi_dma_read_ahb_payload(AXI_FIFO_BASE_ADDR, 1, rand_payload, MAX_FIFO_SIZE*2, 0);

            // Clear auto-write
            VPRINTF(LOW, "Disable FIFO to auto-write\n");
            SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
            SEND_STDOUT_CTRL(FIFO_CLEAR);


            // ===========================================================================
            // Block Size test - AXItoMBOX Read
            // ===========================================================================
            VPRINTF(LOW, "Reading FIFO payload to Mailbox with block_size feature\n");
            if (soc_ifc_axi_dma_read_mbox_payload_no_wait(AXI_FIFO_BASE_ADDR, 0x0, 1, 0x415C, 256)) {
                fail = 1;
            }

            // Set auto-write
            VPRINTF(LOW, "Enable FIFO to auto-write and enable recovery-mode emulation\n");
            SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
            SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

            soc_ifc_axi_dma_wait_idle (1);

            VPRINTF(LOW, "Disable FIFO to auto-write\n");
            SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
            SEND_STDOUT_CTRL(FIFO_CLEAR);
            SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);

            // Set auto-write and enable recovery emulation _before_ arming DMA
            VPRINTF(LOW, "Enable FIFO to auto-write and enable recovery-mode emulation\n");
            VPRINTF(LOW, "Reading FIFO payload to Mailbox with block_size feature\n");
            SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
            SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

            if (soc_ifc_axi_dma_read_mbox_payload_no_wait(AXI_FIFO_BASE_ADDR, 0x0, 1, 0x415C, 256)) {
                fail = 1;
            }

            soc_ifc_axi_dma_wait_idle (1);

            VPRINTF(LOW, "Disable FIFO to auto-write\n");
            SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
            SEND_STDOUT_CTRL(FIFO_CLEAR);
            SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);


            // ===========================================================================
            // Move data in AXI SRAM using same src/dst addr, rand delays
            // ===========================================================================
            SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);

            VPRINTF(LOW, "Moving payload within SRAM via axi-to-axi xfer\n");
            soc_ifc_axi_dma_send_axi_to_axi(AXI_SRAM_BASE_ADDR, 0, AXI_SRAM_BASE_ADDR, 0, (2*16+1)*4, 0, 0, 0);

            SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);


            // ===========================================================================
            // Move data in AXI SRAM using dst_addr == src_addr + 256B, rand delays
            // ===========================================================================
            SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);

            VPRINTF(LOW, "Moving payload at SRAM via axi-to-axi xfer; R/W non-determinism is expected!\n");
            soc_ifc_axi_dma_send_axi_to_axi(AXI_SRAM_BASE_ADDR, 0, AXI_SRAM_BASE_ADDR + 256, 0, (137)*4, 0, 0, 0); // arbitrary number > 512, i.e. more than 2 AXI transactions

            SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);
        
            // ===========================================================================
            // Send KV Key to AXI SRAM                                 
            // ===========================================================================
            if((lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK)) {
                VPRINTF(LOW, "OCP_LOCK_MODE_EN is set, RUNNING KV key test\n");
                uint32_t kv_expected_key[16];
                uint32_t kv_actual_key[16];
                populate_kv_slot_hmac512(23, kv_expected_key);

            //for(int i = 0; i < 16; i++) {
            //    VPRINTF(LOW, "Expected KV[%x]: 0x%x\n", i, kv_expected_key[i]);
            //}

                uint32_t kv_key_size = lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_SIZE) & SOC_IFC_REG_SS_KEY_RELEASE_SIZE_SIZE_MASK;
                uint64_t kv_key_dest = lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_H);
                kv_key_dest = (kv_key_dest << 32) | 
                              lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_L);

                soc_ifc_axi_dma_send_kv_to_axi(kv_key_dest, kv_key_size);

                soc_ifc_axi_dma_read_ahb_payload(kv_key_dest, 0, kv_actual_key, kv_key_size, 0);
        

                for(int i = 0; i < 16; i++) {
                    if(kv_expected_key[i] != kv_actual_key[i]) {
                        VPRINTF(ERROR, "ERROR: KV expected doesn't match actual. Expected 0x%x Actual: 0x%x\n", kv_expected_key[i], kv_actual_key[i]);
                        fail = 1;
                    }
                    else {
                        VPRINTF(LOW, "KV Expected 0x%x Actual: 0x%x\n", kv_expected_key[i], kv_actual_key[i]);
                    }

                }
                //populate_kv_slot_aes_ecb();
            }
            else {
                VPRINTF(LOW, "OCP_LOCK_MODE_EN is not set, SKIPPING KV key test\n");
            }





            // ===========================================================================
            // Auto FIFO test with very large transfer and random RESET
            // ===========================================================================

            // Set auto-write
            VPRINTF(LOW, "Enable FIFO to auto-write\n");
            SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

            // Read data from AXI FIFO
            VPRINTF(LOW, "Request random reset and read large payload from FIFO to Mailbox\n");
            SEND_STDOUT_CTRL(0xee);
            soc_ifc_axi_dma_read_mbox_payload(AXI_FIFO_BASE_ADDR, 0x0, 1, MAX_FIFO_SIZE*32, 0);

            // Clear auto-write
            // This shouldn't execute - the reset will clear the FIFO and auto-write flag
            VPRINTF(LOW, "Disable FIFO to auto-write\n");
            SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
            SEND_STDOUT_CTRL(FIFO_CLEAR);

        }


        // ===========================================================================
        // Ending Status
        // ===========================================================================
        if (fail) {
            VPRINTF(FATAL, "smoke_test_dma failed!\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
}
