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
#include "soc_ifc.h"
#include "printf.h"
#include "aes.h"
#include <stdint.h>
#include <string.h>

// Function wrapper for lsu_write_32 with endianness support
void aes_lsu_write_32(uint32_t addr, uint32_t data, aes_endian_e endian_mode) {
    uint32_t write_data = data;
    
    if (endian_mode == AES_BIG_ENDIAN) {
        // Swap bytes for big endian: ABCD -> DCBA
        write_data = ((data & 0xFF000000) >> 24) |
                     ((data & 0x00FF0000) >> 8)  |
                     ((data & 0x0000FF00) << 8)  |
                     ((data & 0x000000FF) << 24);
    }
    
    lsu_write_32(addr, write_data);
}

void hex_to_uint32_array(const char *hex_str, uint32_t *array, uint32_t *array_size) {
    int len = strlen(hex_str);
    int num_dwords;
    int num_chars;
      VPRINTF(HIGH, "String length is %d.\n",len);
    const uint32_t index[] = {1,0,3,2,5,4,7,6};
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
}

void aes_wait_idle(){
  while((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_IDLE_MASK) == 0);
}


void aes_flow(aes_op_e op, aes_mode_e mode, aes_key_len_e key_len, aes_flow_t aes_input, aes_endian_e endian_mode){
  uint8_t fail_cmd = 0x1;
  uint32_t ciphertext[4];
  uint32_t tag[4];
  uint32_t partial_text_len = aes_input.text_len%16;
  uint32_t partial_aad_len = aes_input.aad_len%16;
  uint32_t num_blocks_text = (partial_text_len == 0) ? aes_input.text_len/16 : aes_input.text_len/16 +1;
  uint32_t num_blocks_aad = (partial_aad_len == 0) ? aes_input.aad_len/16 : aes_input.aad_len/16 + 1;
  uint32_t length;
  uint32_t num_bytes;
  uint32_t masked = 0;
  uint32_t read_payload[100];
  uint8_t  gcm_mode = mode == AES_GCM;

  // wait for AES to be idle
  aes_wait_idle();
  
  // Configure endianness if needed
  if (endian_mode == AES_BIG_ENDIAN) {
      VPRINTF(LOW, "Configuring AES for big endian mode\n");
      // Set ENDIAN_SWAP bit to convert big endian to little endian
      lsu_write_32(CLP_AES_CLP_REG_CTRL0, AES_CLP_REG_CTRL0_ENDIAN_SWAP_MASK);        
  } else {
      VPRINTF(LOW, "Configuring AES for little endian mode\n");
      // Clear ENDIAN_SWAP bit for native little endian
      lsu_write_32(CLP_AES_CLP_REG_CTRL0, 0);
  }
  
  // wait for AES to be idle
  aes_wait_idle();

  //Load key from keyvault if expected
  if (aes_input.key.kv_intf){
      // Wait for KV read logic to be idle
      while((lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS) & AES_CLP_REG_AES_KV_RD_KEY_STATUS_READY_MASK) == 0);

      // Program KEY Read
      lsu_write_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL, AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                      ((aes_input.key.kv_id << AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

      // Check that AES key is loaded
      while((lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS) & AES_CLP_REG_AES_KV_RD_KEY_STATUS_VALID_MASK) == 0);
  }

  uint32_t aes_ctrl =
    ((op << AES_REG_CTRL_SHADOWED_OPERATION_LOW) & AES_REG_CTRL_SHADOWED_OPERATION_MASK) |
    ((mode << AES_REG_CTRL_SHADOWED_MODE_LOW) & AES_REG_CTRL_SHADOWED_MODE_MASK) |
    ((key_len << AES_REG_CTRL_SHADOWED_KEY_LEN_LOW) & AES_REG_CTRL_SHADOWED_KEY_LEN_MASK) |
    (0x0 << AES_REG_CTRL_SHADOWED_MANUAL_OPERATION_LOW) |
    (aes_input.key.kv_intf << AES_REG_CTRL_SHADOWED_SIDELOAD_LOW);

  VPRINTF(LOW, "Write AES CTRL with value 0x%x\n", aes_ctrl);
  
  //write shadowed ctrl twice
  lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, aes_ctrl);
  lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, aes_ctrl);


  if (mode == AES_GCM) {
    aes_wait_idle();

    //If GCM set CTRL_GCM to GCM_INIT
    lsu_write_32(CLP_AES_REG_CTRL_GCM_SHADOWED, (GCM_INIT << AES_REG_CTRL_GCM_SHADOWED_PHASE_LOW) |
                                                (16 << AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_LOW));
    lsu_write_32(CLP_AES_REG_CTRL_GCM_SHADOWED, (GCM_INIT << AES_REG_CTRL_GCM_SHADOWED_PHASE_LOW) |
                                                (16 << AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_LOW));
  }

  aes_wait_idle();

  //Write the key
  if (!aes_input.key.kv_intf) {
      // Load key from hw_data and write to AES
      VPRINTF(LOW, "Load Key data to AES\n");
      for (int j = 0; j < 8; j++) {
        lsu_write_32(CLP_AES_REG_KEY_SHARE0_0 + j * 4, aes_input.key.key_share0[j]);
        lsu_write_32(CLP_AES_REG_KEY_SHARE1_0 + j * 4, aes_input.key.key_share1[j]);
      }
  }

  aes_wait_idle();

  // Write IV
  VPRINTF(LOW, "Write AES IV\n");
  for (int j = 0; j < 4; j++) {
    lsu_write_32((CLP_AES_REG_IV_0 + j * 4), aes_input.iv[j]);
  }

  //If GCM set CTRL_GCM to GCM_AAD
  if ((mode == AES_GCM) && (aes_input.aad_len > 0)) {

    // Write AAD to REG_DATA_IN
    // Check INPUT_READY between blocks
    for (int i = 0; i < num_blocks_aad; i++) {
      if ((i==0) || ((i==(num_blocks_aad-1)) && (partial_aad_len > 0))) {
        num_bytes = ((i==(num_blocks_aad-1)) && (partial_aad_len > 0)) ? partial_aad_len : 16;

        aes_wait_idle();

        VPRINTF(LOW, "Write GCM_AAD Phase, NUM_BYTES 0x%x\n", num_bytes);
        lsu_write_32(CLP_AES_REG_CTRL_GCM_SHADOWED, (GCM_AAD << AES_REG_CTRL_GCM_SHADOWED_PHASE_LOW) |
                                                    (num_bytes << AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_LOW));
        lsu_write_32(CLP_AES_REG_CTRL_GCM_SHADOWED, (GCM_AAD << AES_REG_CTRL_GCM_SHADOWED_PHASE_LOW) |
                                                    (num_bytes << AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_LOW));
      }

      VPRINTF(LOW, "Wait for INPUT_READY\n");
      // Wait for INPUT_READY
      while((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_INPUT_READY_MASK) == 0);

      VPRINTF(LOW, "Write AES AAD Block %d\n", i);
      for (int j = 0; j < 4; j++) {
        VPRINTF(HIGH, "Write In Data: 0x%x\n", aes_input.aad[j+i*4]);
        aes_lsu_write_32((CLP_AES_REG_DATA_IN_0 + j * 4), aes_input.aad[j+i*4], endian_mode);
      }
    }
  }

  // Wait for IDLE
  //aes_wait_idle();
  if (aes_input.text_len > 0) { 
    if (aes_input.data_src_mode == AES_DATA_DMA){

        VPRINTF(LOW, "SRC: { 0x%0x_%0x } to DST: { 0x%0x_%0x }\n", 
          (uint32_t)((aes_input.dma_transfer_data.src_addr >> 32) & 0xFFFFFFFF), 
          (uint32_t)(aes_input.dma_transfer_data.src_addr & 0xFFFFFFFF),
          (uint32_t)((aes_input.dma_transfer_data.dst_addr >> 32) & 0xFFFFFFFF),
          (uint32_t)(aes_input.dma_transfer_data.dst_addr & 0xFFFFFFFF));

        soc_ifc_axi_dma_send_axi_to_axi(aes_input.dma_transfer_data.src_addr, 0, aes_input.dma_transfer_data.dst_addr, 0,  aes_input.text_len, 0, 1, gcm_mode);

        soc_ifc_axi_dma_read_ahb_payload(aes_input.dma_transfer_data.dst_addr, 0, read_payload, aes_input.text_len, 0);

        // Compare to cypher text
        for (int j = 0; j < aes_input.text_len/4; j++) {

          // No masking in AXI mode
          uint32_t mask =  0xffffffff ;
          
          if (op == AES_ENC) {
            if ((read_payload[j] & mask) != (aes_input.ciphertext[j] & mask)) {
              VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
              VPRINTF(LOW, "Actual   data: 0x%x\n", read_payload[j] & mask);
              VPRINTF(LOW, "Expected data: 0x%x\n", aes_input.ciphertext[j] & mask);
              VPRINTF(LOW,"%c", fail_cmd);
              while(1);
            }
          } else if (op == AES_DEC) {
            if ((read_payload[j] & mask) != (aes_input.plaintext[j] & mask)) {
              VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
              VPRINTF(LOW, "Actual   data: 0x%x\n", read_payload[j] & mask);
              VPRINTF(LOW, "Expected data: 0x%x\n", aes_input.plaintext[j] & mask);
              VPRINTF(LOW,"%c", fail_cmd);
              while(1);
            }
          }
        }
      
    }
    else {
      // For Data Block I=0,...,N-1
      for (int i = 0; i < num_blocks_text; i++) {
        
        //Check if first block or a partial last block
        if ((mode == AES_GCM) && ((i == 0) || ((i == num_blocks_text-1) && (partial_text_len > 0)))) {
          //Set num bytes for the last block (could be first also)
          num_bytes = ((i == num_blocks_text-1) && (partial_text_len > 0)) ?  partial_text_len : 16;

          // Wait for IDLE
          aes_wait_idle();

          //set CTRL_GCM to GCM_TEXT
          lsu_write_32(CLP_AES_REG_CTRL_GCM_SHADOWED, (GCM_TEXT << AES_REG_CTRL_GCM_SHADOWED_PHASE_LOW) |
                                                      (num_bytes << AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_LOW));
          lsu_write_32(CLP_AES_REG_CTRL_GCM_SHADOWED, (GCM_TEXT << AES_REG_CTRL_GCM_SHADOWED_PHASE_LOW) |
                                                      (num_bytes << AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_LOW));
        }

        // Wait for INPUT_READY
        while((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_INPUT_READY_MASK) == 0);

        // Write Input Data Block.
        VPRINTF(LOW, "Write AES Input Data Block %d\n", i);
        for (int j = 0; j < 4; j++) {
          if (op == AES_ENC) {
            VPRINTF(HIGH, "Write In Data: 0x%x\n", aes_input.plaintext[j+i*4]);
            aes_lsu_write_32((CLP_AES_REG_DATA_IN_0 + j * 4), aes_input.plaintext[j+i*4], endian_mode);
          } else if (op == AES_DEC) {
            VPRINTF(HIGH, "Write In Data: 0x%x\n", aes_input.ciphertext[j+i*4]);
            aes_lsu_write_32((CLP_AES_REG_DATA_IN_0 + j * 4), aes_input.ciphertext[j+i*4], endian_mode);
          }
        }                      

        // Wait for OUTPUT_VALID bit
        while((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_OUTPUT_VALID_MASK) == 0);

        // Read Output Data Block I
        for (int j = 0; j < 4; j++) {
          ciphertext[j] = lsu_read_32(CLP_AES_REG_DATA_OUT_0 + j * 4);

          //byte mask
          uint32_t mask = (masked == 0) ? 0xffffffff : 0x00000000;
          //this is the last block, and the partial is inside this dword
          if ((i == num_blocks_text-1) && (partial_text_len > 0) && (partial_text_len >= j*4) && (partial_text_len < (j+1)*4)) {
            mask = (1 << (partial_text_len%4)*8) - 1;
            masked = 0x1;
          }
          
          if (op == AES_ENC) {
            if ((ciphertext[j] & mask) != (aes_input.ciphertext[j+i*4] & mask)) {
              VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
              VPRINTF(LOW, "Actual   data: 0x%x\n", ciphertext[j] & mask);
              VPRINTF(LOW, "Expected data: 0x%x\n", aes_input.ciphertext[j+i*4] & mask);
              VPRINTF(LOW,"%c", fail_cmd);
              while(1);
            }
          } else if (op == AES_DEC) {
            if ((ciphertext[j] & mask) != (aes_input.plaintext[j+i*4] & mask)) {
              VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
              VPRINTF(LOW, "Actual   data: 0x%x\n", ciphertext[j] & mask);
              VPRINTF(LOW, "Expected data: 0x%x\n", aes_input.plaintext[j+i*4] & mask);
              VPRINTF(LOW,"%c", fail_cmd);
              while(1);
            }
          }
          
        }
      }
    }
  }

  // Wait for IDLE
  aes_wait_idle();

  if (mode == AES_GCM) {
    // If GCM set CTRL_GCM to GCM_TAG
    lsu_write_32(CLP_AES_REG_CTRL_GCM_SHADOWED, (GCM_TAG << AES_REG_CTRL_GCM_SHADOWED_PHASE_LOW) |
                                                (16 << AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_LOW));
    lsu_write_32(CLP_AES_REG_CTRL_GCM_SHADOWED, (GCM_TAG << AES_REG_CTRL_GCM_SHADOWED_PHASE_LOW) |
                                                (16 << AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_LOW));

    //Write Input Data Block containing length of AAD and length of ciphertext
    //compute length of AAD
    length = aes_input.aad_len << 3; //convert length from bytes to bits
    length = ((length<<24) & 0xff000000) | //swap the bytes
             ((length<< 8) & 0x00ff0000) |
             ((length>> 8) & 0x0000ff00) |
             ((length>>24) & 0x000000ff);

    VPRINTF(HIGH, "Write AAD Length: 0x%x\n", length);
    aes_lsu_write_32(CLP_AES_REG_DATA_IN_0, 0, endian_mode);
    aes_lsu_write_32(CLP_AES_REG_DATA_IN_1, length, endian_mode);

    //compute length of text
    length = aes_input.text_len << 3; //convert length from bytes to bits
    length = ((length<<24) & 0xff000000) | //swap the bytes
             ((length<< 8) & 0x00ff0000) |
             ((length>> 8) & 0x0000ff00) |
             ((length>>24) & 0x000000ff);

    VPRINTF(HIGH, "Write Text Length: 0x%x\n", length);
    aes_lsu_write_32(CLP_AES_REG_DATA_IN_2, 0, endian_mode);
    aes_lsu_write_32(CLP_AES_REG_DATA_IN_3, length, endian_mode);

    // Wait for OUTPUT_VALID bit
    while ((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_OUTPUT_VALID_MASK) == 0);

    // Prepare expected tag values with endianness consideration
    uint32_t expected_tag[4];
    for (int j = 0; j < 4; j++) {
        if (endian_mode == AES_BIG_ENDIAN) {
            // Apply byte swapping for big endian comparison
            expected_tag[j] = ((aes_input.tag[j] & 0xFF000000) >> 24) |
                             ((aes_input.tag[j] & 0x00FF0000) >> 8)  |
                             ((aes_input.tag[j] & 0x0000FF00) << 8)  |
                             ((aes_input.tag[j] & 0x000000FF) << 24);
        } else {
            expected_tag[j] = aes_input.tag[j];
        }
    }
    
    //compare output data to expected tag
    // Read Output Data Block I
    for (int j = 0; j < 4; j++) {
      tag[j] = lsu_read_32(CLP_AES_REG_DATA_OUT_0 + j * 4);
      VPRINTF(MEDIUM, "TAG: 0x%x\n", tag[j]);
      if (tag[j] != expected_tag[j]) {
        VPRINTF(FATAL,"At offset [%d], tag data mismatch!\n", j);
        VPRINTF(LOW,"Actual   data: 0x%x\n", tag[j]);
        VPRINTF(LOW,"Expected data: 0x%x\n", expected_tag[j]);
        VPRINTF(LOW,"%c", fail_cmd);
        while(1);
      }
    }
  }

  // Disable autostart. Note the control register is shadowed and thus needs to be written twice.
  aes_ctrl = 0x1 << AES_REG_CTRL_SHADOWED_MANUAL_OPERATION_LOW;
  lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, aes_ctrl);
  lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, aes_ctrl);

  // Clear all key, IV, Input Data and Output Data registers.
  lsu_write_32(CLP_AES_REG_TRIGGER, (0x1 << AES_REG_TRIGGER_KEY_IV_DATA_IN_CLEAR_LOW) |
                                     (0x1 << AES_REG_TRIGGER_DATA_OUT_CLEAR_LOW));

}
