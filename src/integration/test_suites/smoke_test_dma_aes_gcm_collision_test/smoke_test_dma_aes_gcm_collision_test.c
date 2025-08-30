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
#include "aes.h"

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

enum tb_fifo_mode {
    RAND_DELAY_TOGGLE   = 0x8f // Toggle random delays on the axi_sub. Applies to both.
};

void main(void) {
    // AES flow configuration
    aes_flow_t    aes_input     = {0};
    aes_op_e      op            = AES_ENC;
    aes_mode_e    mode          = AES_GCM;
    aes_key_len_e key_len;
    aes_endian_e  endian_mode;  // AES_LITTLE_ENDIAN or AES_BIG_ENDIAN

    // AES-256 test vectors
    static char key_str3[] = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    uint32_t   key[8];
    uint32_t   key_size;

    static char iv_str3[] = "cafebabefacedbaddecaf888";
    uint32_t   iv[4];
    uint32_t   iv_length;

    // uint32_t   plaintext[32];  // arbitrary length here
    uint32_t   plaintext_length;

    // uint32_t   ciphertext[32];  // arbitrary length here
    uint32_t   ciphertext_length;

    static char aad_str3[] = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    uint32_t   aad[32];  // arbitrary length here
    uint32_t   aad_length;

    // String "596142b046c10e029d10b7d96a2d2607"
    static uint32_t tag[4]     = { 0xb0426159, 0x020ec146, 0xd9b7109d, 0x07262d6a };
    uint32_t   tag_length;

    // d9313225d9313225d9313225d9313225
    static uint32_t plaintext[4] = { 0x253231d9, 0x253231d9, 0x253231d9, 0x253231d9};
    static uint32_t ciphertext[4] = { 0xf0c12d52, 0xc749e3b8, 0x430c1788, 0xc256405c };

    aes_key_t  aes_key = {0};

    uint32_t  reg;
    uint8_t fail = 0;

    // Set endianness mode
    endian_mode = AES_LITTLE_ENDIAN;

    VPRINTF(LOW, "----------------------------------\nSmoke Test AXI DMA AES  !!\n----------------------------------\n");

    SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);

    // read csr_read_mcause to check if we came from an interrupt
    // if so terminate the test
    uint32_t mcause = csr_read_mcause();
    if (mcause != 0) {
        
        fail = 0;
        VPRINTF(LOW, "NMI Detected: Came from interrupt! mcause=0x%08X\n", mcause);
        // Checking for DMA Error
        for(int i = 0; i < 15; i++) {
            reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
            if(reg & AXI_DMA_REG_STATUS0_ERROR_MASK) {
                VPRINTF(LOW, "DMA Detected: AXI DMA Err Status=0x%08X\n", reg & AXI_DMA_REG_STATUS0_ERROR_MASK);
                break;
            } else {
                // wait a bit
                for(int j = 0; j < 400; j++) {
                    asm volatile("nop");
                }
            }
            if (i == 14) {
                VPRINTF(ERROR, "ERROR: NMI Detected but no AXI DMA Error Status=0x%08X\n", reg);
                fail = 1;
            }
        }

        // Checking CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R -- CIF bit is set
        reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R);
        if (reg & AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AES_CIF_STS_MASK) {
            VPRINTF(LOW, "NMI Detected: AXI DMA CIF Err Status=0x%08X matches expected value\n", reg);
        } else {
            VPRINTF(ERROR, "ERROR: NMI Detected but AXI DMA CIF Error Status=0x%08X\n", reg);
            VPRINTF(ERROR, "ERROR: AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_AES_CIF_EN_MASK not set!\n");
            fail = 1;
        }

        // write 1 to clear the interrupt
        lsu_write_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R,
                      AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AES_CIF_STS_MASK);

        // check if cleared
        reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R);
        if (!(reg & AXI_DMA_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_AES_CIF_STS_MASK)) {
            VPRINTF(LOW, "CIF Err Interrupt cleared\n");
        } else {
            VPRINTF(ERROR, "ERROR: CIF Error Interrupt not cleared!\n");
            fail = 1;
        }

        if (fail) {
            VPRINTF(ERROR, "Test Failed!\n");
            SEND_STDOUT_CTRL(0x01);
        } else {
            VPRINTF(LOW, "Test Passed!\n");
            SEND_STDOUT_CTRL(0xFF);
        }
        while(1);
    }

    // Convert hex strings to uint32 arrays
    hex_to_uint32_array(key_str3, key, &key_size);
    key_len = key_size == 32 ? AES_256 :
              key_size == 16 ? AES_128 : AES_192;
    hex_to_uint32_array(iv_str3, iv, &iv_length);
    // hex_to_uint32_array(plaintext_str3, plaintext, &plaintext_length);
    // hex_to_uint32_array(ciphertext_str3, ciphertext, &ciphertext_length);
    hex_to_uint32_array(aad_str3, aad, &aad_length);
    // hex_to_uint32_array(tag_str3, tag, &tag_length);
    // hex_to_uint32_array(tag_long_str, tag_long, &tag_long_length);

    VPRINTF(LOW, "Tag address: 0x%08X\n", (uint32_t)tag);
    VPRINTF(LOW, "Tag: ");
    for (int i = 0; i < tag_length/4; i++) {
        VPRINTF(LOW, "%08X", tag[i]);
    }
    VPRINTF(LOW, "\n");

    // Setup AES key structure
    aes_key.kv_intf = FALSE;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    plaintext_length = 16;

    // Configure AES input structure
    aes_input.key                        = aes_key;
    aes_input.text_len                   = plaintext_length;
    aes_input.plaintext                  = plaintext;
    aes_input.ciphertext                 = ciphertext;
    aes_input.aad_len                    = aad_length;
    aes_input.aad                        = aad;
    aes_input.tag                        = tag;
    aes_input.iv                         = iv;
    aes_input.data_src_mode              = AES_DATA_DMA;
    aes_input.dma_transfer_data.src_addr = AXI_SRAM_BASE_ADDR;
    aes_input.dma_transfer_data.dst_addr = AXI_SRAM_BASE_ADDR + (AXI_SRAM_SIZE_BYTES/2);

    // ===========================================================================
    // Sending image over to AXI SRAM for usage during DMA AES calculation
    // ===========================================================================
    // Use a FIXED transfer (only the final beat should be present at the target address)
    VPRINTF(LOW, "Sending image payload via AHB i/f to AXI SRAM\n");
    soc_ifc_axi_dma_send_ahb_payload(aes_input.dma_transfer_data.src_addr, 0, 
                                      aes_input.plaintext, aes_input.text_len, 0);

    // Execute AES flow
    aes_flow(op, mode, key_len, aes_input, endian_mode);
    
    // // ===========================================================================
    // // Now inject error and expect to catch it
    // // ===========================================================================

    aes_input.aes_collision_err = TRUE;
    aes_input.aes_expect_err = TRUE;
    VPRINTF(LOW, "AES collision err injection enabled\n");
   
    // Execute AES flow
    VPRINTF(LOW, "Executing AES flow with collision err injection enabled\n");
    aes_flow(op, mode, key_len, aes_input, endian_mode);

    // Reached here means test failed
    VPRINTF(ERROR, "Collision error not detected test progressed unexpectedly\n");
    // Signal completion and wait
    SEND_STDOUT_CTRL(0x01);
    while(1);
}
