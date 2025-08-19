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

void main(void) {
    aes_flow_t aes_input;
    aes_op_e op = AES_ENC;
    aes_mode_e mode = AES_GCM;
    aes_key_len_e key_len;
    aes_endian_e endian_mode; // AES_LITTLE_ENDIAN or AES_BIG_ENDIAN
    uint32_t reg;


    const char key_str3[] = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
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

    aes_key_t aes_key;

    endian_mode = AES_LITTLE_ENDIAN;

    VPRINTF(LOW, "----------------------------------\nSmoke Test AXI DMA AES  !!\n----------------------------------\n");

    hex_to_uint32_array(key_str3, key, &key_size);
    key_len = key_size == 32 ? AES_256 :
              key_size == 16 ? AES_128 : AES_192;
    hex_to_uint32_array(iv_str3, iv, &iv_length);
    hex_to_uint32_array(plaintext_str3, plaintext, &plaintext_length);
    hex_to_uint32_array(ciphertext_str3, ciphertext, &ciphertext_length);
    hex_to_uint32_array(aad_str3, aad, &aad_length);
    hex_to_uint32_array(tag_str3, tag, &tag_length);

    aes_key.kv_intf = FALSE;
    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }

    aes_input.key = aes_key;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.aad_len = aad_length;
    aes_input.aad = aad;
    aes_input.tag = tag;
    aes_input.iv = iv;
    
    aes_input.data_src_mode  = AES_DATA_DMA;
    aes_input.dma_transfer_data.src_addr = AXI_SRAM_BASE_ADDR;
    aes_input.dma_transfer_data.dst_addr = AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2;
    
    // ===========================================================================
    // Sending image overto AXI SRAM for usage during DMA AES calculation
    // ===========================================================================
    // Use a FIXED transfer (only the final beat should be present at the target address)
    SEND_STDOUT_CTRL( 0xb6); // assertoff
    
    SEND_STDOUT_CTRL( 0xb8); //  AXI Error Injection Disabled
    VPRINTF(LOW, "Sending image payload via AHB i/f to AXI SRAM\n");
    soc_ifc_axi_dma_send_ahb_payload(aes_input.dma_transfer_data.src_addr, 0, aes_input.plaintext, aes_input.text_len, 0);

    SEND_STDOUT_CTRL( 0xb7); // AXI Error Injection Enabled
    VPRINTF(LOW, "Trying the AES GCM Operation.. Err Inj ON\n");
    aes_input.aes_expect_err = TRUE;
    aes_flow(op, mode, key_len, aes_input, endian_mode);
    SEND_STDOUT_CTRL( 0xb8); //  AXI Error Injection Disabled   
    SEND_STDOUT_CTRL( 0xb5); // asserton

    VPRINTF(LOW, "Trying Again the AES GCM Operation.. Err Inj OFF\n");
    aes_input.aes_expect_err = FALSE;
    aes_flow(op, mode, key_len, aes_input, endian_mode);

    SEND_STDOUT_CTRL( 0xff);
    while(1);

}
