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

#ifdef MY_RANDOM_SEED
    unsigned rand_seed = (unsigned) MY_RANDOM_SEED;
#else
    unsigned rand_seed = 0;
#endif



enum tb_fifo_mode {
    RCVY_EMU_TOGGLE     = 0x88,
    FIFO_AUTO_READ_ON   = 0x8a, // Should be set while the fifo is empty.
                                // When pushing data to the fifo, it will automatically empty itself (with random speed).
                                // If set, this must be cleared using the off flag below before changing the auto_write flag.
                                // If set, should be cleared before FIFO_CLEAR.
    FIFO_AUTO_WRITE_ON  = 0x8b, // FIFO_CLEAR should be used before setting AUTO_WRITE_ON
                                // If set, this must be cleared with "OFF" before using the FIFO_CLEAR
    FIFO_AUTO_READ_OFF  = 0x8c, // Clear the fifo auto-read feature. Do this after every test that sets it.
    FIFO_AUTO_WRITE_OFF = 0x8d, // Clear the auto-write feature. Should be done after every test that sets it.
                                // MUST be followed by a FIFO_CLEAR (i.e. , disable auto-write then fifo_clear)
    FIFO_CLEAR          = 0x8e, // Generates a pulse and auto-clears itself. Write once to generate the fifo_clear pulse.
    RAND_DELAY_TOGGLE   = 0x8f, // Toggle random delays on the axi_sub. Applies to both.
    ZERO_KV16_KEY  = 0xc8,  // Sets KV 16 and 23 to a zero key.
    SMALL_KV23_KEY  = 0xc9,  // Sets KV 16 and 23 to a zero key.
    LARGE_KV23_KEY  = 0xca,  // Sets KV 16 and 23 to a zero key.
    KV16_KEY  = 0xcc         // Sets KV 16 to a known AES key
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
    uint32_t kv_actual_key[16];
    uint32_t send_payload[16];
    aes_key_o_t aes_key_o;
    aes_key_t aes_key;
    uint32_t random_text_length;
    
    uint32_t kv_key_size = lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_SIZE) & SOC_IFC_REG_SS_KEY_RELEASE_SIZE_SIZE_MASK;
    uint64_t kv_key_dest = lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_H);
    kv_key_dest = (kv_key_dest << 32) |
                  lsu_read_32(CLP_SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_L);
    
    
    /* Intializes random number generator */
    srand(rand_seed);



    VPRINTF(LOW, "----------------------------------\nSmoke Test AXI DMA AES KV  !!\n----------------------------------\n");
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
            
    VPRINTF(LOW, "MEK KEY SIZE: 0x%x\n", kv_key_size);
    VPRINTF(LOW, "MEK KEY DEST: 0x%x\n", kv_key_dest);


    if ( kv_key_size <= 0x40) {
        VPRINTF(LOW, "KV KEY SIZE is less than 0x40 and is valid.\n" );


        // Test each malformed command check
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_wr_route_kv))          { fail = 1; }
        if((lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK)) {
            lsu_write_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL, SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK);
            if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_route_combo_kv))   { fail = 1; } // Can only be tested after IN PROGRESS has been set
            if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_dst_addr_kv))      { fail = 1; } // Can only be tested after IN PROGRESS has been set
            if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_byte_count_kv))    { fail = 1; } // Can only be tested after IN PROGRESS has been set
            if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_wr_fixed_kv))      { fail = 1; } // Can only be tested after IN PROGRESS has been set
        }

        VPRINTF(FATAL, "Enable random delays in AXI\n");
        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);

        // ===========================================================================
        // Send KV Key to AXI SRAM                                 
        // ===========================================================================
        if((lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG) & SOC_IFC_REG_CPTRA_HW_CONFIG_OCP_LOCK_MODE_EN_MASK)) {
            VPRINTF(LOW, "OCP_LOCK_MODE_EN is set, RUNNING KV key test\n");



            ///////////////////////////////////
            // TEST 1: BASIC TEST AES KV 23 to DMA
            ///////////////////////////////////

            VPRINTF(LOW, "START TEST 1: BASIC TEST AES KV 23 to DMA\n");
            // Key to KV
            aes_key_o.kv_intf = TRUE;
            aes_key_o.kv_expect_err = FALSE;
            aes_key_o.kv_id = 23; //KV slot 23
            aes_key_o.dest_valid = (dest_valid_t){0}; // Clear all destinations
            aes_key_o.dest_valid.dma_data = 1; // Only allow DMA access

            //Key from KV
            aes_key.kv_intf = TRUE;
            aes_key.kv_id = 16;
            aes_key.kv_reuse_key = FALSE;
            aes_key.kv_expect_err = FALSE;
            
            // Preload KV16 with a zero key
            SEND_STDOUT_CTRL(KV16_KEY);

            // Loading the KV23 slot with a key from AES
            populate_kv_slot_aes(aes_key_o, aes_key, 0, kv_expected_key, 0, AES_ECB);

            // We should only be sending data to SRAM up to the size of kv_key_size
            // Meaning the other SRAM locations should be zeroed out
            for(int i = kv_key_size >> 2; i < 16; i++) {
                kv_expected_key[i] = 0x0; // Zero out the rest of the key
            }

            // Transfering KV to SRAM
            soc_ifc_axi_dma_send_kv_to_axi(kv_key_dest, kv_key_size);

            // Checking data was sent to SRAM correctly
            soc_ifc_axi_dma_read_ahb_payload(kv_key_dest, 0, kv_actual_key, kv_key_size, 0);


            VPRINTF(LOW, "TEST 1: Checking if key stores in AXI SRAM matches expected\n");
            for(int i = 0; i < 16; i++) {
                if(kv_expected_key[i] != kv_actual_key[i]) {
                    VPRINTF(ERROR, "ERROR: KV expected doesn't match actual. Expected 0x%x Actual: 0x%x\n", kv_expected_key[i], kv_actual_key[i]);
                    fail = 1;
                }
            }
            ///////////////////////////////////
            // TEST 2: TEST AES KV 23 to DMA REUSE KV16
            ///////////////////////////////////

            VPRINTF(LOW, "START TEST 2: TEST AES KV 23 to DMA REUSE KV16\n");
            
            // Initialize structs to ensure clean state

            // Key to KV
            //((volatile aes_key_t*)aes_key)->kv_intf = TRUE;
            aes_key_o.kv_intf = TRUE;
            aes_key_o.kv_expect_err = FALSE;
            aes_key_o.kv_id = 23; //KV slot 23
            aes_key_o.dest_valid = (dest_valid_t){0}; // Clear all destinations
            aes_key_o.dest_valid.dma_data = 1; // Only allow DMA access

            //Key from KV
            ((volatile aes_key_t*)&aes_key)->kv_intf = TRUE;
            aes_key.kv_id = 16;
            aes_key.kv_reuse_key = TRUE;
            aes_key.kv_expect_err = FALSE;
        
            
            // Preload KV16 with zero to prove we are reusing the key alread in AES
            SEND_STDOUT_CTRL(ZERO_KV16_KEY);

            // Loading the KV23 slot with a key from AES
            populate_kv_slot_aes(aes_key_o, aes_key, 0, kv_expected_key, 0, AES_ECB);

            // We should only be sending data to SRAM up to the size of kv_key_size
            // Meaning the other SRAM locations should be zeroed out
            for(int i = kv_key_size >> 2; i < 16; i++) {
                kv_expected_key[i] = 0x0; // Zero out the rest of the key
            }

            // Transfering KV to SRAM
            soc_ifc_axi_dma_send_kv_to_axi(kv_key_dest, kv_key_size);

            // Checking data was sent to SRAM correctly
            soc_ifc_axi_dma_read_ahb_payload(kv_key_dest, 0, kv_actual_key, kv_key_size, 0);


            VPRINTF(LOW, "TEST 2: Checking if key stores in AXI SRAM matches expected\n");
            for(int i = 0; i < 16; i++) {
                if(kv_expected_key[i] != kv_actual_key[i]) {
                    VPRINTF(ERROR, "ERROR: KV expected doesn't match actual. Expected 0x%x Actual: 0x%x\n", kv_expected_key[i], kv_actual_key[i]);
                    fail = 1;
                }
            }

            ///////////////////////////////////
            // TEST 3: ERR DMA NO ACCESS KV23
            ///////////////////////////////////

            VPRINTF(LOW, "START TEST 3: ERR TEST DMA NO ACCESS KV23\n");
            
            // Clearing KV23 so we can load a new key into it. 
            lsu_write_32(CLP_KV_REG_KEY_CTRL_23, KV_REG_KEY_CTRL_23_CLEAR_MASK);

            // Zeroize send_payload since we were having issues with it being non-zero
            memset(send_payload, 0, sizeof(send_payload));
            // Clearing SRAM where key was stored from TEST 1
            soc_ifc_axi_dma_send_ahb_payload(kv_key_dest, 0, send_payload, kv_key_size, 0);

            // Key to KV
            aes_key_o.kv_intf = TRUE;
            aes_key_o.kv_expect_err = FALSE;
            aes_key_o.kv_id = 23; //KV slot 23
            aes_key_o.dest_valid = (dest_valid_t){0}; // Clear all destinations

            //Key from KV
            aes_key.kv_intf = TRUE;
            aes_key.kv_id = 16;
            aes_key.kv_reuse_key = FALSE;

            // Loading the KV23 slot with a key from AES
            populate_kv_slot_aes(aes_key_o, aes_key, 0, kv_expected_key, 0, AES_ECB);

            // Since no access for KV23 was granted we should get a DMA ERROR
            soc_ifc_axi_dma_send_kv_to_axi_error(kv_key_dest, kv_key_size);

            // Checking data was sent to SRAM correctly
            soc_ifc_axi_dma_read_ahb_payload(kv_key_dest, 0, kv_actual_key, kv_key_size, 0);
            
            // No data should have been sent to the SRAM so expected should be 0.
            memset(kv_expected_key, 0, sizeof(kv_expected_key));

            VPRINTF(LOW, "TEST 3: Checking if key stores in AXI SRAM matches expected\n");
            for(int i = 0; i < 16; i++) {
                if(kv_expected_key[i] != kv_actual_key[i]) {
                    VPRINTF(ERROR, "ERROR: KV expected doesn't match actual. Expected 0x%x Actual: 0x%x\n", kv_expected_key[i], kv_actual_key[i]);
                    fail = 1;
                }
            }


            ///////////////////////////////////
            // TEST 4: ERR KV SLOT KEY SMALLER THAN KEY_RELEASE_SIZE STRAP
            ///////////////////////////////////
            if(kv_key_size > 0x4) {
                // Test when key in KV slot is smaller than the key_release_size
                VPRINTF(LOW, "START TEST 4: SMALL KV23\n");

                lsu_write_32(CLP_KV_REG_KEY_CTRL_23, KV_REG_KEY_CTRL_23_CLEAR_MASK);
            
                // Zeroize the key in SRAM
                memset(send_payload, 0, sizeof(send_payload));
                soc_ifc_axi_dma_send_ahb_payload(kv_key_dest, 0, send_payload, kv_key_size, 0);
            
                SEND_STDOUT_CTRL(SMALL_KV23_KEY);

                soc_ifc_axi_dma_send_kv_to_axi_error(kv_key_dest, kv_key_size);

                soc_ifc_axi_dma_read_ahb_payload(kv_key_dest, 0, kv_actual_key, kv_key_size, 0);

                memset(kv_expected_key, 0, sizeof(kv_expected_key));

                VPRINTF(LOW, " TEST 4: Checking if key stores in AXI SRAM matches expected\n");
                for(int i = 0; i < 16; i++) {
                    if(kv_expected_key[i] != kv_actual_key[i]) {
                        VPRINTF(ERROR, "ERROR: KV expected doesn't match actual. Expected 0x%x Actual: 0x%x\n", kv_expected_key[i], kv_actual_key[i]);
                        fail = 1;
                    }
                }
            }
            else {
                VPRINTF(LOW, "SKIP TEST 4: SMALL KV23\n");
            }

            ///////////////////////////////////
            // TEST 5: ERR KV SLOT KEY LARGER THAN KEY_RELEASE_SIZE STRAP
            ///////////////////////////////////
            if(kv_key_size <= 0x3C) {
                // Test when key in KV slot is larger than the key_release_size
                VPRINTF(LOW, "START TEST 5: LARGE KV23\n");

                lsu_write_32(CLP_KV_REG_KEY_CTRL_23, KV_REG_KEY_CTRL_23_CLEAR_MASK);
            
                // Zeroize the key in SRAM
                memset(send_payload, 0, sizeof(send_payload));
                soc_ifc_axi_dma_send_ahb_payload(kv_key_dest, 0, send_payload, kv_key_size, 0);
            
                SEND_STDOUT_CTRL(LARGE_KV23_KEY);

                soc_ifc_axi_dma_send_kv_to_axi_error(kv_key_dest, kv_key_size);

                soc_ifc_axi_dma_read_ahb_payload(kv_key_dest, 0, kv_actual_key, kv_key_size, 0);

                memset(kv_expected_key, 0, sizeof(kv_expected_key));

                VPRINTF(LOW, " TEST 5: Checking if key stores in AXI SRAM matches expected\n");
                for(int i = 0; i < 16; i++) {
                    if(kv_expected_key[i] != kv_actual_key[i]) {
                        VPRINTF(ERROR, "ERROR: KV expected doesn't match actual. Expected 0x%x Actual: 0x%x\n", kv_expected_key[i], kv_actual_key[i]);
                        fail = 1;
                    }
                }
            }
            else {
                VPRINTF(LOW, "SKIP TEST 5: LARGE KV23\n");
            }
            
            /////////////////////////////////////
            //// TEST 6: ERR ROUTE KV16 to FW with a DECRYPT OPERATION         
            /////////////////////////////////////
            VPRINTF(LOW, "START TEST 6: ROUTE KV16 to FW - ERR\n");

            for(int i = 0; i < 23; i++){
                kv_set_clear(i);
            }
            VPRINTF(LOW, "DONE CLEARING KEYS\n");
            
            // Key to KV
            aes_key_o.kv_intf = FALSE;

            //Key from KV
            aes_key.kv_intf = TRUE;
            aes_key.kv_id = 16;
            aes_key.kv_reuse_key = FALSE;
            
            // Preload KV16 with a zero key
            SEND_STDOUT_CTRL(ZERO_KV16_KEY);

            // Loading the KV23 slot with a key from AES
            populate_kv_slot_aes(aes_key_o, aes_key, 0, kv_expected_key, 0, AES_ECB);
            
            ///////////////////////////////////
            // TEST 7: ERR ROUTE KV16 to KV != KV23
            ///////////////////////////////////

            VPRINTF(LOW, "START TEST 7: ERR ROUTE KV16 to KV != KV23\n");
            
            // Clearing SRAM where we expect the key to be written
            soc_ifc_axi_dma_send_ahb_payload(kv_key_dest, 0, send_payload, kv_key_size, 0);

            // Key to KV
            aes_key_o.kv_intf = TRUE;
            aes_key_o.kv_expect_err = TRUE;
            aes_key_o.kv_id = rand() % 23; // Random KV slot 0-22
            aes_key_o.dest_valid = (dest_valid_t){0}; // Clear all destinations
            aes_key_o.dest_valid.dma_data = 1; // Only allow DMA access

            //Key from KV
            aes_key.kv_intf = TRUE;
            aes_key.kv_id = 16;
            aes_key.kv_reuse_key = FALSE;
            
            // Preload KV16 with a zero key
            SEND_STDOUT_CTRL(ZERO_KV16_KEY);

            // Loading the KV slot with a key from AES
            populate_kv_slot_aes(aes_key_o, aes_key, 0, kv_expected_key, 0, AES_ECB);

        }
        else {
            VPRINTF(LOW, "OCP_LOCK_MODE_EN is not set, SKIPPING KV key test\n");
        }
    }
    else {
        VPRINTF(FATAL, "KV KEY SIZE is not valid: 0x%x testing the byte count too large err\n", kv_key_size);
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_byte_count_kv_large))    { fail = 1; } // Can only be tested after IN PROGRESS has been set

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
