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

void nmi_handler() {
    VPRINTF(FATAL, "NMI");
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
    aes_flow_new(op, mode, key_len, aes_input);




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

        VPRINTF(LOW, "----------------------------------\nSmoke Test AES->KV->AXI DMA !!\n----------------------------------\n");
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

        // Set OCP LOCK in PROGRESS
        reg = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
        if (reg & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK) {
            VPRINTF(LOW, "OCP LOCK En, setting OCP LOCK in progress\n");
        } else {
            VPRINTF(LOW, "OCP LOCK En not set\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK);
        
        // ===========================================================================
        // Send KV Key to AXI SRAM                                 
        // ===========================================================================
        uint32_t kv_expected_key[16];
        uint32_t kv_actual_key[16];
        populate_kv_slot_hmac512(23, kv_expected_key);

        for(int i = 0; i < 16; i++) {
            VPRINTF(LOW, "Expected KV[%x]: 0x%x\n", i, kv_expected_key[i]);
        }

        uint32_t kv_key_size = lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_SIZE) & SOC_IFC_REG_SS_KEY_RELEASE_SIZE_SIZE_MASK;
        uint64_t kv_key_dest = lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_H);
        
        lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK);
                
        kv_key_dest = (kv_key_dest << 32) | 
                      lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_L);

        VPRINTF(LOW, "KV size: 0x%x\n", kv_key_size);
        soc_ifc_axi_dma_send_kv_to_axi(kv_key_dest, kv_key_size);

        soc_ifc_axi_dma_read_ahb_payload(kv_key_dest, 0, kv_actual_key, kv_key_size, 0);
        
        populate_kv_slot_aes_ecb();

        for(int i = 0; i < 16; i++) {
            if(kv_expected_key[i] != kv_actual_key[i]) {
                VPRINTF(ERROR, "ERROR: KV expected doesn't match actual. Expected 0x%x Actual: 0x%x\n", kv_expected_key[i], kv_actual_key[i]);
            }
            else {
                VPRINTF(LOW, "KV Expected 0x%x Actual: 0x%x\n", kv_expected_key[i], kv_actual_key[i]);
            }
            
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
