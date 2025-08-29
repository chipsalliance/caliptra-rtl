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
    const uint32_t* plaintext;
    const uint32_t* ciphertext; 
    const uint32_t* tag;
    const uint32_t* aad;
    const uint32_t* iv;
    const uint32_t* key;
    uint32_t length_dwords;  // Length of both plaintext and ciphertext in dwords
    uint32_t key_dwords;     // Length of key in dwords
    uint32_t aad_dwords;     // Length of AAD in dwords
} aes_gcm_vectors_t;

static const aes_gcm_vectors_t gcm_test_vectors[] = {
    // AES-256 key: feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308
    // IV (96-bit): cafebabefacedbaddecaf888
    // AAD: feedfacedeadbeeffeedfacedeadbeefabaddad2

    { // 1 DWORD (4 bytes)
        .plaintext = (uint32_t[]){0x253231d9},
        .ciphertext = (uint32_t[]){0xf0c12d52},
        .tag = (uint32_t[]){0xef82aa43, 0xdcd0eb9c, 0x08482f5b, 0xb07581c5},
        .aad = (uint32_t[]){0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab},
        .iv = (uint32_t[]){0xbebafeca, 0xaddbcefa, 0x88f8cade, 0x00000000},
        .key = (uint32_t[]){0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067, 0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067},
        .length_dwords = 1,
        .key_dwords = 8,    // Key length in dwords
        .aad_dwords = 5     // AAD length in dwords
    },
    { // 2 DWORDS (8 bytes)
        .plaintext = (uint32_t[]){0x253231d9, 0xe50684f8},
        .ciphertext = (uint32_t[]){0xf0c12d52, 0x077d5699},
        .tag = (uint32_t[]){0x64c24e41, 0xdbe3298b, 0x1acd03c2, 0x60dae7dc},
        .aad = (uint32_t[]){0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab},
        .iv = (uint32_t[]){0xbebafeca, 0xaddbcefa, 0x88f8cade, 0x00000000},
        .key = (uint32_t[]){0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067, 0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067},
        .length_dwords = 2,
        .key_dwords = 8,    // Key length in dwords
        .aad_dwords = 5     // AAD length in dwords
    },
    { // 3 DWORDS (12 bytes)
        .plaintext = (uint32_t[]){0x253231d9, 0xe50684f8, 0xc50959a5},
        .ciphertext = (uint32_t[]){0xf0c12d52, 0x077d5699, 0xa3377ff4},
        .tag = (uint32_t[]){0xb1f6ba8f, 0x323fa15b, 0x2fb8e8fd, 0x147742f6},
        .aad = (uint32_t[]){0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab},
        .iv = (uint32_t[]){0xbebafeca, 0xaddbcefa, 0x88f8cade, 0x00000000},
        .key = (uint32_t[]){0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067, 0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067},
        .length_dwords = 3,
        .key_dwords = 8,    // Key length in dwords
        .aad_dwords = 5     // AAD length in dwords
    },
    { // 4 DWORDS (16 bytes)
        .plaintext = (uint32_t[]){0x253231d9, 0xe50684f8, 0xc50959a5, 0x9a26f5af},
        .ciphertext = (uint32_t[]){0xf0c12d52, 0x077d5699, 0xa3377ff4, 0x7d42842a},
        .tag = (uint32_t[]){0x1bf91c5b, 0xa29cc545, 0xbee625e0, 0xeaa6b6c8},
        .aad = (uint32_t[]){0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab},
        .iv = (uint32_t[]){0xbebafeca, 0xaddbcefa, 0x88f8cade, 0x00000000},
        .key = (uint32_t[]){0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067, 0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067},
        .length_dwords = 4,
        .key_dwords = 8,    // Key length in dwords
        .aad_dwords = 5     // AAD length in dwords
    },
    { // 5 DWORDS (20 bytes)
        .plaintext = (uint32_t[]){0x253231d9, 0xe50684f8, 0xc50959a5, 0x9a26f5af, 0x53a9a786},
        .ciphertext = (uint32_t[]){0xf0c12d52, 0x077d5699, 0xa3377ff4, 0x7d42842a, 0xdc8c3a64},
        .tag = (uint32_t[]){0xc81b5010, 0x8fae5156, 0xc5d67641, 0x3f9feaa5},
        .aad = (uint32_t[]){0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab},
        .iv = (uint32_t[]){0xbebafeca, 0xaddbcefa, 0x88f8cade, 0x00000000},
        .key = (uint32_t[]){0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067, 0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067},
        .length_dwords = 5,
        .key_dwords = 8,    // Key length in dwords
        .aad_dwords = 5     // AAD length in dwords
    },
    { // 6 DWORDS (24 bytes)
        .plaintext = (uint32_t[]){0x253231d9, 0xe50684f8, 0xc50959a5, 0x9a26f5af, 0x53a9a786, 0xdaf73415},
        .ciphertext = (uint32_t[]){0xf0c12d52, 0x077d5699, 0xa3377ff4, 0x7d42842a, 0xdc8c3a64, 0xc9c0e5bf},
        .tag = (uint32_t[]){0x832ecc1d, 0x17c9be03, 0x001b9ef9, 0xd52d4ac2},
        .aad = (uint32_t[]){0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab},
        .iv = (uint32_t[]){0xbebafeca, 0xaddbcefa, 0x88f8cade, 0x00000000},
        .key = (uint32_t[]){0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067, 0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067},
        .length_dwords = 6,
        .key_dwords = 8,    // Key length in dwords
        .aad_dwords = 5     // AAD length in dwords
    },
    { // 7 DWORDS (28 bytes)
        .plaintext = (uint32_t[]){0x253231d9, 0xe50684f8, 0xc50959a5, 0x9a26f5af, 0x53a9a786, 0xdaf73415, 0x3d304c2e},
        .ciphertext = (uint32_t[]){0xf0c12d52, 0x077d5699, 0xa3377ff4, 0x7d42842a, 0xdc8c3a64, 0xc9c0e5bf, 0xbda29875},
        .tag = (uint32_t[]){0x8e816ceb, 0xaac87256, 0x9b88376a, 0xcad241e7},
        .aad = (uint32_t[]){0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab},
        .iv = (uint32_t[]){0xbebafeca, 0xaddbcefa, 0x88f8cade, 0x00000000},
        .key = (uint32_t[]){0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067, 0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067},
        .length_dwords = 7,
        .key_dwords = 8,    // Key length in dwords
        .aad_dwords = 5     // AAD length in dwords
    },
    { // 8 DWORDS (32 bytes)
        .plaintext = (uint32_t[]){0x253231d9, 0xe50684f8, 0xc50959a5, 0x9a26f5af, 0x53a9a786, 0xdaf73415, 0x3d304c2e, 0x728a318a},
        .ciphertext = (uint32_t[]){0xf0c12d52, 0x077d5699, 0xa3377ff4, 0x7d42842a, 0xdc8c3a64, 0xc9c0e5bf, 0xbda29875, 0xaad15525},
        .tag = (uint32_t[]){0xa9ff9bcf, 0x824d33bd, 0x3468c840, 0x06b5362b},
        .aad = (uint32_t[]){0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab},
        .iv = (uint32_t[]){0xbebafeca, 0xaddbcefa, 0x88f8cade, 0x00000000},
        .key = (uint32_t[]){0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067, 0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067},
        .length_dwords = 8,
        .key_dwords = 8,    // Key length in dwords
        .aad_dwords = 5     // AAD length in dwords
    },
    { // 9 DWORDS (36 bytes)
        .plaintext = (uint32_t[]){0x253231d9, 0xe50684f8, 0xc50959a5, 0x9a26f5af, 0x53a9a786, 0xdaf73415, 0x3d304c2e, 0x728a318a, 0xe55351d9},
        .ciphertext = (uint32_t[]){0xf0c12d52, 0x077d5699, 0xa3377ff4, 0x7d42842a, 0xdc8c3a64, 0xc9c0e5bf, 0xbda29875, 0xaad15525, 0x38d1dd49},
        .tag = (uint32_t[]){0x389e069d, 0x0629e3c0, 0x8213ad67, 0xa1f235bd},
        .aad = (uint32_t[]){0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab},
        .iv = (uint32_t[]){0xbebafeca, 0xaddbcefa, 0x88f8cade, 0x00000000},
        .key = (uint32_t[]){0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067, 0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067},
        .length_dwords = 9,
        .key_dwords = 8,    // Key length in dwords
        .aad_dwords = 5     // AAD length in dwords
    },
    { // 10 DWORDS (40 bytes)
        .plaintext = (uint32_t[]){0x253231d9, 0xe50684f8, 0xc50959a5, 0x9a26f5af, 0x53a9a786, 0xdaf73415, 0x3d304c2e, 0x728a318a, 0xe55351d9, 0xc8fe9523},
        .ciphertext = (uint32_t[]){0xf0c12d52, 0x077d5699, 0xa3377ff4, 0x7d42842a, 0xdc8c3a64, 0xc9c0e5bf, 0xbda29875, 0xaad15525, 0x38d1dd49, 0xa64cf0ef},
        .tag = (uint32_t[]){0x5f89fdfc, 0x1846fa3c, 0x3926b4d6, 0x34262e18},
        .aad = (uint32_t[]){0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab},
        .iv = (uint32_t[]){0xbebafeca, 0xaddbcefa, 0x88f8cade, 0x00000000},
        .key = (uint32_t[]){0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067, 0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067},
        .length_dwords = 10,
        .key_dwords = 8,    // Key length in dwords
        .aad_dwords = 5     // AAD length in dwords
    },
    { // 11 DWORDS (44 bytes)
        .plaintext = (uint32_t[]){0x253231d9, 0xe50684f8, 0xc50959a5, 0x9a26f5af, 0x53a9a786, 0xdaf73415, 0x3d304c2e, 0x728a318a, 0xe55351d9, 0xc8fe9523, 0xef3d5490},
        .ciphertext = (uint32_t[]){0xf0c12d52, 0x077d5699, 0xa3377ff4, 0x7d42842a, 0xdc8c3a64, 0xc9c0e5bf, 0xbda29875, 0xaad15525, 0x38d1dd49, 0xa64cf0ef, 0xdbb82b18},
        .tag = (uint32_t[]){0x30cc6fd1, 0x42a72802, 0xff9b69e4, 0xab223af4},
        .aad = (uint32_t[]){0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab},
        .iv = (uint32_t[]){0xbebafeca, 0xaddbcefa, 0x88f8cade, 0x00000000},
        .key = (uint32_t[]){0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067, 0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067},
        .length_dwords = 11,
        .key_dwords = 8,    // Key length in dwords
        .aad_dwords = 5     // AAD length in dwords
    },
    { // 12 DWORDS (48 bytes)
        .plaintext = (uint32_t[]){0x253231d9, 0xe50684f8, 0xc50959a5, 0x9a26f5af, 0x53a9a786, 0xdaf73415, 0x3d304c2e, 0x728a318a, 0xe55351d9, 0xc8fe9523, 0xef3d5490, 0x625748a3},
        .ciphertext = (uint32_t[]){0xf0c12d52, 0x077d5699, 0xa3377ff4, 0x7d42842a, 0xdc8c3a64, 0xc9c0e5bf, 0xbda29875, 0xaad15525, 0x38d1dd49, 0xa64cf0ef, 0xdbb82b18, 0x7f6a6cbc},
        .tag = (uint32_t[]){0x8f217b0f, 0x7def525d, 0x56aa9749, 0x16ed7daf},
        .aad = (uint32_t[]){0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab},
        .iv = (uint32_t[]){0xbebafeca, 0xaddbcefa, 0x88f8cade, 0x00000000},  // Padded to 4 dwords
        .key = (uint32_t[]){0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067, 0x92e9fffe, 0x1c736586, 0x948f6a6d, 0x08833067},
        .length_dwords = 12,
        .key_dwords = 8,    // Key length in dwords
        .aad_dwords = 5     // AAD length in dwords
    }
};

// Helper function to get test vector index based on dword length
int get_vector_index(uint32_t dword_len) {
    return (dword_len >= 1 && dword_len <= 12) ? (dword_len - 1) : 0; // Default to first vector if out of range
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
    
    // Get references to pre-converted arrays from test vector
    const aes_gcm_vectors_t *vector = &gcm_test_vectors[vector_idx];
    
    // Create local working arrays with endianness handling
    uint32_t plaintext[vector->length_dwords];
    uint32_t ciphertext[vector->length_dwords];
    
    // Copy data with endianness conversion if needed
    copy_data_with_endianness(vector->plaintext, plaintext, vector->length_dwords, test_config.endian_mode);
    copy_data_with_endianness(vector->ciphertext, ciphertext, vector->length_dwords, test_config.endian_mode);
    
    // Use length fields from the vector structure
    uint32_t key_bytes = vector->key_dwords * 4;
    uint32_t aad_bytes = vector->aad_dwords * 4;
    
    // Determine key length
    key_len = key_bytes == 32 ? AES_256 : key_bytes == 16 ? AES_128 : AES_192;

    VPRINTF(LOW, "Plaintext length: %d dwords (%d bytes)\n", vector->length_dwords, vector->length_dwords * 4);
    VPRINTF(LOW, "Ciphertext length: %d dwords (%d bytes)\n", vector->length_dwords, vector->length_dwords * 4);
    VPRINTF(LOW, "Key bytes: %d: \n", key_bytes);
    VPRINTF(LOW, "Key DWORD: %d: \n", vector->key_dwords);
    VPRINTF(LOW, "Key LEN: %d: \n", key_len);
    VPRINTF(LOW, "AAD bytes: %d: \n", aad_bytes);
    VPRINTF(LOW, "AAD DWORD: %d: \n", vector->aad_dwords);

    // Setup AES input structure - use vector data directly
    aes_input.aad_len = aad_bytes; // Dynamic AAD length in bytes
    aes_input.aad = (uint32_t*)vector->aad;
    aes_input.tag = (uint32_t*)vector->tag;
    aes_input.iv = (uint32_t*)vector->iv;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.text_len = random_len_bytes; // Use randomized length
    
    aes_key.kv_intf = FALSE;
    
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = (i < vector->key_dwords) ? vector->key[i] : 0;
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
        {AES_ENC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Encrypt GCM image via AXI DMA (Little Endian)", 1},
        {AES_ENC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Encrypt GCM image via AXI DMA (Little Endian)", 2},
        {AES_DEC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Decrypt GCM image via AXI DMA (Little Endian)", 3},
        {AES_ENC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Encrypt GCM image via AXI DMA (Little Endian)", 4},
        {AES_ENC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Encrypt GCM image via AXI DMA (Little Endian)", 5},
        {AES_DEC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Decrypt GCM image via AXI DMA (Little Endian)", 6},
        {AES_DEC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Decrypt GCM image via AXI DMA (Little Endian)", 7},
        {AES_DEC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Decrypt GCM image via AXI DMA (Little Endian)", 8},
        {AES_ENC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Encrypt GCM image via AXI DMA (Little Endian)", 9},
        {AES_ENC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Encrypt GCM image via AXI DMA (Little Endian)", 10},
        {AES_DEC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Decrypt GCM image via AXI DMA (Little Endian)", 11},
        {AES_DEC, AES_GCM, AES_256, AES_LITTLE_ENDIAN, "AXI DMA Decrypt GCM image via AXI DMA (Little Endian)", 12},

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
