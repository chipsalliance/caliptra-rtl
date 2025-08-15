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
#include "caliptra_rtl_lib.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "soc_ifc.h"
#include "aes.h"
#include "keyvault.h"



enum tb_fifo_mode {
    LOAD_ALL_KV_KEYS_AES  = 0xcb  // Sets KV 16 and 23 to a zero key.
};



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

void nmi_handler() {
    VPRINTF(FATAL, "NMI");
}

void main(void) {
    int argc=0;
    char *argv[1];
    uint32_t reg;
    uint32_t kv_expected_key[16];
    aes_key_o_t aes_key_o;
    aes_key_t aes_key;
    uint32_t random_text_length;
    uint8_t rand_aes_encrypt;
    aes_mode_e rand_aes_mode;


    VPRINTF(LOW, "----------------------------------\nSmoke Test AES KV RAND  !!\n----------------------------------\n");
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


    // FIXME if (xorshift32() % 2) {
    // FIXME     VPRINTF(LOW, "Writing OCP lock control register\n");
    // FIXME     lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK);
    // FIXME } else {
    // FIXME     VPRINTF(LOW, "Skipping OCP lock control register write\n");
    // FIXME }
    lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK);
    
    uint32_t lock_status = lsu_read_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL);
    uint32_t lock_in_progress = (lock_status & SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK) != 0;

    VPRINTF(LOW, "OCP Lock Status: 0x%x, Lock In Progress: %d\n", lock_status, lock_in_progress);
            

    for(int i = 0; i < 20; i++) {
        VPRINTF(LOW, "START TEST %d\n", i);
        aes_key_o.kv_intf = TRUE;
        aes_key_o.kv_expect_err = FALSE;
        aes_key_o.kv_id = xorshift32() % 24; //KV slot 0-23
        aes_key_o.dest_valid = (dest_valid_t){0}; // Clear all destinations
        aes_key_o.dest_valid.dma_data = 1; // Only allow DMA access
            
        
        aes_key.kv_intf = (xorshift32() % 2) ? TRUE : FALSE;
        if (aes_key.kv_intf == TRUE) {
            aes_key.kv_id = xorshift32() % 24;
        }

        if(aes_key.kv_id == 23 && lock_in_progress && aes_key.kv_intf == TRUE) {
            aes_key.kv_expect_err = TRUE;
        }
        else {
            aes_key.kv_expect_err = FALSE;
        }


        rand_aes_encrypt = xorshift32() % 2;


        // Keep generating until we get a non-GCM mode
        // TODO add AES_GCM support
        do {
            rand_aes_mode = (aes_mode_e)(1 << (xorshift32() % 6));  // 0-5 gives us all 6 modes
        } while (rand_aes_mode == AES_GCM);

        if (lock_in_progress  && (aes_key.kv_id == 16) && (aes_key_o.kv_id == 23) && !rand_aes_encrypt && aes_key.kv_intf == TRUE && rand_aes_mode == AES_ECB) {
            aes_key_o.kv_expect_err = FALSE;
        } else {
            aes_key_o.kv_expect_err = TRUE;
        }



        VPRINTF(LOW, "KV ID: %d, KV Intf: %d\n", aes_key.kv_id, aes_key.kv_intf);
        VPRINTF(LOW, "KV_O ID: %d, KV_O Intf: %d, Expect_O Err: %d\n", aes_key_o.kv_id, aes_key_o.kv_intf, aes_key_o.kv_expect_err);
        VPRINTF(LOW, "AES MODE: %s AES ENCRYPT: %d\n", 
                (rand_aes_mode == AES_ECB) ? "AES_ECB" :
                (rand_aes_mode == AES_CBC) ? "AES_CBC" :
                (rand_aes_mode == AES_CFB) ? "AES_CFB" :
                (rand_aes_mode == AES_OFB) ? "AES_OFB" :
                (rand_aes_mode == AES_CTR) ? "AES_CTR" :
                (rand_aes_mode == AES_GCM) ? "AES_GCM" : "UNKNOWN",
                rand_aes_encrypt);
        
        SEND_STDOUT_CTRL(LOAD_ALL_KV_KEYS_AES);
        populate_kv_slot_aes(aes_key_o, aes_key, 0, kv_expected_key, rand_aes_encrypt, rand_aes_mode);

    }



    // ===========================================================================
    // Ending Status
    // ===========================================================================
    if (fail) {
        VPRINTF(FATAL, "smoke_test_dma_aes_kv failed!\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
    SEND_STDOUT_CTRL(0xff);
}
