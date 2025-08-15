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

// Test configuration structure
typedef struct {
    aes_op_e operation;      // AES_ENC or AES_DEC
    aes_mode_e mode;         // AES_GCM, AES_ECB, AES_CBC, etc.
    aes_key_len_e key_len;   // AES_128, AES_192, AES_256
    aes_endian_e endian_mode; // AES_LITTLE_ENDIAN or AES_BIG_ENDIAN
    const char* test_name;   // Test description
    uint8_t use_src_as_dst;
} test_config_t;

// hex_to_uint32_array_with_endianess
void hex_to_uint32_array_with_endianess(const char *hex_str, uint32_t *array, uint32_t *array_size, aes_endian_e endian_mode) {
    int len = strlen(hex_str);
    int num_dwords;
    int num_chars;

    VPRINTF(HIGH, "String length is %d.\n", len);
    const uint32_t index[] = {1, 0, 3, 2, 5, 4, 7, 6};
    if (len % 2 != 0) {
        VPRINTF(HIGH, "Error: Hex string length must be a multiple of 2.\n");
        return;
    }
    num_dwords = (len / 8);
    *array_size = (len / 2);
    for (int i = 0; i <= num_dwords; i++) {
        uint32_t value = 0x00000000;
        num_chars = (i == num_dwords) ? len % 8 : 8;
        for (int j = 0; j < num_chars; j++) {
            char c = hex_str[i * 8 + j];
            uint32_t digit;

            if (c >= '0' && c <= '9') {
                digit = c - '0';
            } else if (c >= 'a' && c <= 'f') {
                digit = c - 'a' + 10;
            } else if (c >= 'A' && c <= 'F') {
                digit = c - 'A' + 10;
            } else {
                VPRINTF(HIGH, "Error: Invalid hex character: %c\n", c);
                return;
            }
            value |= digit << (4 * index[j]);
        }
        if (num_chars != 0) {
            array[i] = value;
        }
    }

    // Apply endianness if needed
    if (endian_mode == AES_BIG_ENDIAN) {
        for (int i = 0; i < *array_size; i++) {
            array[i] =  (((array[i] & 0xFF000000) >> 24) |
                        ((array[i] & 0x00FF0000) >> 8)  |
                        ((array[i] & 0x0000FF00) << 8)  |
                        ((array[i] & 0x000000FF) << 24));
        }
    }
}

void run_aes_test(test_config_t test_config) {
    aes_flow_t aes_input;
    aes_op_e op = test_config.operation;
    aes_mode_e mode = test_config.mode;
    aes_key_len_e key_len;

    VPRINTF(LOW, "\n----------------------------------\n%s\n----------------------------------\n", test_config.test_name);

    const char key_str3[] = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    const char ecb_key_str[] = "b6a8d5636f5c6a7224f9977dcf7ee6c7fb6d0c48cbdee9737a959796489bddbc";
    uint32_t key[8];
    uint32_t key_size;
                    
    const char iv_str3[] = "cafebabefacedbaddecaf888";
    uint32_t iv[4]; 
    uint32_t iv_length;

    
    const char plaintext_str3[] = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    uint32_t plaintext[32]; //arbitrary length here
    uint32_t plaintext_length;

    const char ciphertext_str3[] = "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662";
    uint32_t ciphertext[32]; //arbitrary length here
    uint32_t ciphertext_length;

    const char aad_str3[] = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    uint32_t aad[32]; //arbitrary length here
    uint32_t aad_length;
                    
    const char tag_str3[] = "76fc6ece0f4e1768cddf8853bb2d551b";
    uint32_t tag[4]; 
    uint32_t tag_length;

    // ECB test vectors for non-GCM tests
    const char ecb_plaintext_str[] = "fc23e07b4018460279f8392e86423ecfe465b25b60382f58995ef5fa1f9ca235e4bf87112554aa0e72836831d7b5f39125df11518b8aeb1809d804419beb05ae013482213012e4ce980ddd1c58e11608";
    const char ecb_ciphertext_str[] = "294645de9db599fc87c89addcc4d2b2c3cbb855d32efd4ba0e885b0bd69218497822dc61260e767e0220911263b5ece06ee7d06dc4618cb014791390780931b39ac63768b28fe148c937f3fee63afa1fb2244382980b01da1d5c6b6657aa4250";
    const char ecb_aad_str[]="b3a1db2d467780480f166859e0e7aab212738b85e88237c2782496c9c503347de02f3dad6bfc671fda71a04ff1e4661767c11303daa0c36d944346d39e3e29ec63d695cdcd83b2b57181582c5ac692b13e4299ab5e86c59d09c2dc6194ebe9";
    const char ecb_tag_str[] = "a6722f6434c72c8dbd598360d804af39";
    const char iv_str128[] = "1234567891a824c5e023283959858062";

    uint32_t ecb_plaintext[32];
    uint32_t ecb_ciphertext[32];
    uint32_t ecb_plaintext_length, ecb_ciphertext_length;

    aes_key_t aes_key;

    // Parse test vectors based on mode
    if (mode == AES_GCM) {
        VPRINTF(LOW, "Configuring AES for GCM mode\n");
        hex_to_uint32_array(key_str3, key, &key_size);
        key_len = key_size == 32 ? AES_256 :
                  key_size == 16 ? AES_128 : AES_192;
        hex_to_uint32_array(iv_str3, iv, &iv_length);
        hex_to_uint32_array_with_endianess(plaintext_str3, plaintext, &plaintext_length, test_config.endian_mode);
        hex_to_uint32_array_with_endianess(ciphertext_str3, ciphertext, &ciphertext_length, test_config.endian_mode);
        hex_to_uint32_array(aad_str3, aad, &aad_length);
        hex_to_uint32_array(tag_str3, tag, &tag_length);

        aes_input.aad_len = aad_length;
        aes_input.aad = aad;
        aes_input.tag = tag;
        aes_input.iv = iv;
        aes_input.plaintext = plaintext;
        aes_input.ciphertext = ciphertext;
        aes_input.text_len = plaintext_length;
    } else {
        VPRINTF(LOW, "Configuring AES for non-GCM mode\n");
        // Non-GCM modes (ECB)
        
        hex_to_uint32_array(ecb_key_str, key, &key_size);
        key_len = key_size == 32 ? AES_256 :
                  key_size == 16 ? AES_128 : AES_192;
        hex_to_uint32_array(ecb_plaintext_str, ecb_plaintext, &ecb_plaintext_length);
        hex_to_uint32_array(ecb_ciphertext_str, ecb_ciphertext, &ecb_ciphertext_length);
        hex_to_uint32_array(ecb_aad_str, aad, &aad_length);
        hex_to_uint32_array(ecb_tag_str, tag, &tag_length);
        hex_to_uint32_array(iv_str128, iv, &iv_length);


        // Set dummy IV for non-GCM modes
        for (int i = 0; i < 4; i++) {
            iv[i] = 0x00000000;
        }
       
        // Set dummy values for GCM-specific fields
        aes_input.aad_len = aad_length;
        aes_input.aad = aad;
        aes_input.tag = tag;
        aes_input.iv = iv;
        aes_input.plaintext = ecb_plaintext;  // This is the input data for DMA
        aes_input.ciphertext = ecb_ciphertext;  // This is the expected output for validation
        aes_input.text_len = ecb_plaintext_length;  // Use plaintext length

    }    
    
    aes_key.kv_intf = FALSE;
    
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    aes_input.key = aes_key;
    
    aes_input.data_src_mode  = AES_DATA_DMA;

    if(test_config.use_src_as_dst == 1){
        VPRINTF(LOW, "Using.. source address as destination address\n");
        aes_input.dma_transfer_data.src_addr = (uint64_t)AXI_SRAM_BASE_ADDR;
        aes_input.dma_transfer_data.dst_addr = (uint64_t)AXI_SRAM_BASE_ADDR;
    } else {
        aes_input.dma_transfer_data.src_addr = (uint64_t)AXI_SRAM_BASE_ADDR;
        aes_input.dma_transfer_data.dst_addr = (uint64_t)(AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2);
    }

    // ===========================================================================
    // Sending image over to AXI SRAM for usage during DMA AES calculation
    // ===========================================================================
    // Use a FIXED transfer (only the final beat should be present at the target address)
    VPRINTF(LOW, "Sending image payload via AHB i/f to AXI SRAM AES GCM\n");
    if(op==AES_ENC){
        soc_ifc_axi_dma_send_ahb_payload(aes_input.dma_transfer_data.src_addr, 0, aes_input.plaintext, aes_input.text_len, 0);
    } else {
        soc_ifc_axi_dma_send_ahb_payload(aes_input.dma_transfer_data.src_addr, 0, aes_input.ciphertext, aes_input.text_len, 0);
    }

    aes_flow(op, mode, key_len, aes_input, test_config.endian_mode);
}

void main(void) {

    VPRINTF(LOW, "----------------------------------\nSmoke Test AXI DMA AES - Multiple Test Cases\n----------------------------------\n");

    // Define all test cases
    test_config_t test_cases[] = {

        // using source as destination
        // GCM Tests
        {AES_ENC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Encrypt GCM image via AXI DMA (Little Endian)", 1},
        {AES_DEC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Decrypt GCM image via AXI DMA (Little Endian)", 1},
        {AES_ENC, AES_GCM, AES_256, AES_BIG_ENDIAN, "AES DMA Encrypt GCM image big endian via AXI DMA", 1},
        {AES_DEC, AES_GCM, AES_256, AES_BIG_ENDIAN, "AES DMA Decrypt GCM image big endian via AXI DMA", 1},

        // GCM Tests
        {AES_ENC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Encrypt GCM image via AXI DMA (Little Endian)", 0},
        {AES_DEC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Decrypt GCM image via AXI DMA (Little Endian)", 0},
        {AES_ENC, AES_GCM, AES_256, AES_BIG_ENDIAN, "AES DMA Encrypt GCM image big endian via AXI DMA", 0},
        {AES_DEC, AES_GCM, AES_256, AES_BIG_ENDIAN, "AES DMA Decrypt GCM image big endian via AXI DMA", 0},
        
        // Non-GCM Tests (ECB mode)
        {AES_ENC, AES_ECB, AES_256, AES_LITTLE_ENDIAN, "AES DMA Encrypt non-GCM image via AXI DMA (Little Endian)", 0},
        {AES_DEC, AES_ECB, AES_256, AES_LITTLE_ENDIAN, "AES DMA Decrypt non-GCM image via AXI DMA (Little Endian)", 0},


    };

    int num_tests = sizeof(test_cases) / sizeof(test_config_t);
    
    for (int i = 0; i < num_tests; i++) {
        VPRINTF(LOW, "\n========================================\nRunning Test %d of %d\n========================================\n", i+1, num_tests);
        run_aes_test(test_cases[i]);
        VPRINTF(LOW, "Test %d PASSED\n", i+1);
    }

    VPRINTF(LOW, "\n========================================\nALL TESTS COMPLETED SUCCESSFULLY!\n========================================\n");

    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
