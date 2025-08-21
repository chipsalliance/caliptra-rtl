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
    uint32_t random_dword_len; // Random length in dwords (1-7)
} test_config_t;

typedef struct {
    const char* plaintext;
    const char* ciphertext; 
    const char* tag;
    const char* aad;
    const char* iv;
    const char* key;
    uint32_t length_dwords;
} aes_gcm_vectors_t;

static const aes_gcm_vectors_t gcm_test_vectors[] = {
    // AES-256 key: feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308
    // IV (96-bit): cafebabefacedbaddecaf888
    // AAD: feedfacedeadbeeffeedfacedeadbeefabaddad2

    

    { // 1 DWORD (4 bytes)
        .plaintext = "d9313225",
        .ciphertext = "522dc1f0",
        .tag = "43aa82ef9cebd0dc5b2f4808c58175b0",
        .aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2",
        .iv = "cafebabefacedbaddecaf888",
        .key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
        .length_dwords = 1
    },
    { // 2 DWORDS (8 bytes)
        .plaintext = "d9313225f88406e5",
        .ciphertext = "522dc1f099567d07",
        .tag = "414ec2648b29e3dbc203cd1adce7da60",
        .aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2",
        .iv = "cafebabefacedbaddecaf888",
        .key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
        .length_dwords = 2
    },
    { // 3 DWORDS (12 bytes)
        .plaintext = "d9313225f88406e5a55909c5",
        .ciphertext = "522dc1f099567d07f47f37a3",
        .tag = "8fbaf6b15ba13f32fde8b82ff6427714",
        .aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2",
        .iv = "cafebabefacedbaddecaf888",
        .key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
        .length_dwords = 3
    },
    { // 4 DWORDS (16 bytes)
        .plaintext = "d9313225f88406e5a55909c5aff5269a",
        .ciphertext = "522dc1f099567d07f47f37a32a84427d",
        .tag = "5b1cf91b45c59ca2e025e6bec8b6a6ea",
        .aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2",
        .iv = "cafebabefacedbaddecaf888",
        .key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
        .length_dwords = 4
    },
    { // 5 DWORDS (20 bytes)
        .plaintext = "d9313225f88406e5a55909c5aff5269a86a7a953",
        .ciphertext = "522dc1f099567d07f47f37a32a84427d643a8cdc",
        .tag = "10501bc85651ae8f4176d6c5a5ea9f3f",
        .aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2",
        .iv = "cafebabefacedbaddecaf888",
        .key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
        .length_dwords = 5
    },
    { // 6 DWORDS (24 bytes)
        .plaintext = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da",
        .ciphertext = "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c9",
        .tag = "1dcc2e8303bec917f99e1b00c24a2dd5",
        .aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2",
        .iv = "cafebabefacedbaddecaf888",
        .key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
        .length_dwords = 6
    },
    { // 7 DWORDS (28 bytes)
        .plaintext = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d",
        .ciphertext = "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd",
        .tag = "eb6c818e5672c8aa6a37889be741d2ca",
        .aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2",
        .iv = "cafebabefacedbaddecaf888",
        .key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
        .length_dwords = 7
    },
    { // 8 DWORDS (32 bytes)
        .plaintext =  "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a72",
        .ciphertext = "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa",
        .tag = "cf9bffa9bd334d8240c868342b36b506",
        .aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2",
        .iv = "cafebabefacedbaddecaf888",
        .key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
        .length_dwords = 8
    }
};

// Helper function to get test vector index based on dword length
int get_vector_index(uint32_t dword_len) {
    return (dword_len >= 1 && dword_len <= 8) ? (dword_len - 1) : 0; // Default to first vector if out of range
}


// Generate random dword length between 1 and 7
uint32_t get_random_dword_length() {
    return (xorshift32() % 7) + 1; // 1 to 7 dwords
}

// Count = 8
// Key = dd5c48988a6e9f9f60be801ba5c090f224a1b53d6601ec5858eab7b7784a8d5e
// IV = 43562d48cd4110a66d9ca64e
// PT = 2cda2761fd0be2b03f9714fce8d0e303
// AAD = 55e568309fc6cb0fb0e0e7d2511d4116
// CT = f2cfb6f5446e7aa172adfcd66b92a98d
// Tag = e099c64d2966e780ce7d2eaae97f47d8

void run_aes_test(test_config_t test_config) {
    aes_flow_t aes_input = {0};
    aes_op_e op = test_config.operation;
    aes_mode_e mode = test_config.mode;
    aes_key_len_e key_len;
    aes_key_t aes_key = {0};

    VPRINTF(LOW, "\n----------------------------------\n%s\n----------------------------------\n", test_config.test_name);
    
    VPRINTF(LOW, "Configuring AES for GCM mode\n");
    
    // Get the appropriate test vector for the random dword length
    int vector_idx = get_vector_index(test_config.random_dword_len);
    uint32_t random_len_bytes = test_config.random_dword_len * 4;
    
    VPRINTF(LOW, "Using test vector %d for %d dwords (%d bytes)\n", 
            vector_idx, test_config.random_dword_len, random_len_bytes);
    
    // Declare arrays for parsed data
    uint32_t key[8];
    uint32_t key_size;
    uint32_t iv[4]; 
    uint32_t iv_length;
    uint32_t aad[32];
    uint32_t aad_length;
    uint32_t plaintext[32];
    uint32_t plaintext_length;
    uint32_t ciphertext[32];
    uint32_t ciphertext_length; 
    uint32_t tag[4];
    uint32_t tag_length;
    
    // Parse test vector components
    hex_to_uint32_array(gcm_test_vectors[vector_idx].key, key, &key_size);
    key_len = key_size == 32 ? AES_256 : key_size == 16 ? AES_128 : AES_192;
    hex_to_uint32_array(gcm_test_vectors[vector_idx].iv, iv, &iv_length);
    hex_to_uint32_array_with_endianess(gcm_test_vectors[vector_idx].plaintext, plaintext, &plaintext_length, test_config.endian_mode);
    hex_to_uint32_array_with_endianess(gcm_test_vectors[vector_idx].ciphertext, ciphertext, &ciphertext_length, test_config.endian_mode);
    hex_to_uint32_array(gcm_test_vectors[vector_idx].aad, aad, &aad_length);
    hex_to_uint32_array(gcm_test_vectors[vector_idx].tag, tag, &tag_length);

    VPRINTF(LOW, "Plaintext: %s\n", gcm_test_vectors[vector_idx].plaintext);
    VPRINTF(LOW, "Ciphertext: %s\n", gcm_test_vectors[vector_idx].ciphertext);
    VPRINTF(LOW, "Tag: %s\n", gcm_test_vectors[vector_idx].tag);

    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.text_len = random_len_bytes; // Use randomized length
    
    aes_key.kv_intf = FALSE;
    
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    aes_input.key = aes_key;
    
    aes_input.data_src_mode  = AES_DATA_DMA;
    aes_input.dma_transfer_data.src_addr = AXI_SRAM_BASE_ADDR;
    aes_input.dma_transfer_data.dst_addr = AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2;
   
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

    VPRINTF(LOW, "----------------------------------\nSmoke Test AXI DMA AES - Variable Length Test Cases\n----------------------------------\n");

    // Define all test cases with randomized dword lengths
    test_config_t test_cases[] = {
        // GCM Tests
        {AES_ENC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Encrypt GCM image via AXI DMA (Little Endian)", 8},
        {AES_ENC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Encrypt GCM image via AXI DMA (Little Endian)", get_random_dword_length()},
        {AES_DEC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Decrypt GCM image via AXI DMA (Little Endian)", get_random_dword_length()}

        // TODO - FIX THIS>
        // {AES_ENC, AES_GCM, AES_256, AES_BIG_ENDIAN, "AES DMA Encrypt GCM image big endian via AXI DMA", get_random_dword_length()},
        // {AES_DEC, AES_GCM, AES_256, AES_BIG_ENDIAN, "AES DMA Decrypt GCM image big endian via AXI DMA", get_random_dword_length()}
    };

    int num_tests = sizeof(test_cases) / sizeof(test_config_t);
    
    for (int i = 0; i < num_tests; i++) {
        VPRINTF(LOW, "\n========================================\nRunning Test %d of %d\n========================================\n", i+1, num_tests);
        VPRINTF(LOW, "Test: %s\n", test_cases[i].test_name);
        VPRINTF(LOW, "Random length: %d dwords (%d bytes)\n", test_cases[i].random_dword_len, test_cases[i].random_dword_len * 4);
        run_aes_test(test_cases[i]);
        VPRINTF(LOW, "Test %d PASSED\n", i+1);
    }

    VPRINTF(LOW, "\n========================================\nALL TESTS COMPLETED SUCCESSFULLY!\n========================================\n");

    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
