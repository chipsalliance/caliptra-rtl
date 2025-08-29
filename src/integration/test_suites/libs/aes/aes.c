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
#include "keyvault.h"
#include "caliptra_rtl_lib.h"
#include <stdint.h>
#include <string.h>
#include "caliptra_rtl_lib.h"

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

// hex_to_uint32_array_with_endianess
void hex_to_uint32_array_with_endianess(const char *hex_str, uint32_t *array, uint32_t *array_size, aes_endian_e endian_mode) {
    int len = strlen(hex_str);
    int num_dwords;
    int num_chars;

    VPRINTF(LOW, "String length is %d.\n", len);
    const uint32_t index[] = {1, 0, 3, 2, 5, 4, 7, 6};
    if (len % 2 != 0) {
        VPRINTF(ERROR, "Error: Hex string length must be a multiple of 2.\n");
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
                VPRINTF(ERROR, "Error: Invalid hex character: %c\n", c);
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

void copy_data_with_endianness(const uint32_t* src, uint32_t* dst, uint32_t len, aes_endian_e endian_mode) {
    for (uint32_t i = 0; i < len; i++) {
        if (endian_mode == AES_BIG_ENDIAN) {
            // Apply byte swapping for big endian
            dst[i] = ((src[i] & 0xFF000000) >> 24) |
                     ((src[i] & 0x00FF0000) >> 8)  |
                     ((src[i] & 0x0000FF00) << 8)  |
                     ((src[i] & 0x000000FF) << 24);
        } else {
            dst[i] = src[i];
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
  uint32_t read_payload[aes_input.text_len/4];
  uint8_t  gcm_mode = mode == AES_GCM;
  uint8_t  src_fixed = 0;
  uint8_t  dst_fixed = 0;
  uint8_t  block_size = 0;

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
  if (aes_input.key.kv_intf && !aes_input.key.kv_reuse_key) {
      // Wait for KV read logic to be idle
      while((lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS) & AES_CLP_REG_AES_KV_RD_KEY_STATUS_READY_MASK) == 0);

      // Program KEY Read
      lsu_write_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL, AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                      ((aes_input.key.kv_id << AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_MASK));

      // Check that AES key is loaded
      while((lsu_read_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS) & AES_CLP_REG_AES_KV_RD_KEY_STATUS_VALID_MASK) == 0);
  }

  // Load key into kevault if expected
  if (aes_input.key_o.kv_intf) {
    kv_write_ctrl(CLP_AES_CLP_REG_AES_KV_WR_CTRL, 
                  aes_input.key_o.kv_id,
                  aes_input.key_o.dest_valid);
    VPRINTF(LOW, "Set AES KV Write to slot %d\n", aes_input.key_o.kv_id);
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

  if (!aes_input.key.kv_expect_err){
    // Try to program KEY Read during engine operation
    lsu_write_32(CLP_AES_CLP_REG_AES_KV_RD_KEY_CTRL, AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_EN_MASK |
                                                  ((!aes_input.key.kv_id << AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_LOW) & AES_CLP_REG_AES_KV_RD_KEY_CTRL_READ_ENTRY_MASK));
  }

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
        if(((i*4) +j) < (aes_input.aad_len >> 2)) {
            VPRINTF(MEDIUM, "Write In Data: 0x%x aad DWORD: %d\n", aes_input.aad[j+i*4], ((i*4) +j));
            aes_lsu_write_32((CLP_AES_REG_DATA_IN_0 + j * 4), aes_input.aad[j+i*4], endian_mode);
        }
        else {
            VPRINTF(MEDIUM, "Padding AAD with 0s AAD DWORD: %d", ((i*4) +j));
            aes_lsu_write_32((CLP_AES_REG_DATA_IN_0 + j * 4), 0x0, endian_mode);
        }
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
        
        if(aes_input.aes_dma_err == TRUE) {
          VPRINTF(LOW, "Injecting DMA error\n");
          while(src_fixed == 0 && dst_fixed == 0 && block_size == 0) {
            src_fixed = xorshift32()%2;
            dst_fixed = xorshift32()%2;
            block_size = xorshift32()%20;
          }
          aes_input.aes_expect_err = TRUE;
        }

        soc_ifc_axi_dma_send_axi_to_axi_w_error_expected(aes_input.dma_transfer_data.src_addr, src_fixed, aes_input.dma_transfer_data.dst_addr, dst_fixed,  aes_input.text_len, block_size, 1, gcm_mode, (aes_input.aes_expect_err == TRUE));

        soc_ifc_axi_dma_read_ahb_payload(aes_input.dma_transfer_data.dst_addr, 0, read_payload, aes_input.text_len, 0);

        // Compare to cypher text
        for (int j = 0; j < aes_input.text_len/4; j++) {

          // No masking in AXI mode
          uint32_t mask =  0xffffffff ;
          
          if (op == AES_ENC) {
            if ((read_payload[j] & mask) != (aes_input.ciphertext[j] & mask)) {
              if(aes_input.aes_expect_err == FALSE){
                VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
                VPRINTF(FATAL, "Actual   data: 0x%x\n", read_payload[j] & mask);
                VPRINTF(FATAL, "Expected data: 0x%x\n", aes_input.ciphertext[j] & mask);
                VPRINTF(FATAL,"%c", fail_cmd);
                while(1);
              }
            }
          } else if (op == AES_DEC) {
            if ((read_payload[j] & mask) != (aes_input.plaintext[j] & mask)) {
              if(aes_input.aes_expect_err == FALSE){
              VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
              VPRINTF(FATAL, "Actual   data: 0x%x\n", read_payload[j] & mask);
              VPRINTF(FATAL, "Expected data: 0x%x\n", aes_input.plaintext[j] & mask);
              SEND_STDOUT_CTRL(fail_cmd);
              while(1);
              }
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

        if (aes_input.aes_err_inj.sideload_corrupt) {
          aes_ctrl =  lsu_read_32(CLP_AES_REG_CTRL_SHADOWED);
          aes_ctrl ^= AES_REG_CTRL_SHADOWED_SIDELOAD_MASK; // Flip the SIDELOAD bit
        }


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
        
        if (aes_input.aes_err_inj.sideload_corrupt) {
          lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, aes_ctrl);
          lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, aes_ctrl);
          VPRINTF(LOW, "ATTEMPT TO FLIP SIDELOAD BIT\n")
        }

        if( !aes_input.key_o.kv_intf ) {
            uint8_t ocp_lock_block_output;
            // Wait for OUTPUT_VALID bit
            while((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_OUTPUT_VALID_MASK) == 0);
            
            ocp_lock_block_output = (lsu_read_32(CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL) & SOC_IFC_REG_SS_OCP_LOCK_CTRL_LOCK_IN_PROGRESS_MASK) &&
                                    (aes_input.key.kv_intf == TRUE) && (aes_input.key.kv_id == 16) &&
                                    (mode == AES_ECB);



            // Checking OUTPUT_LOST is the correct value. If OCP LOCK logic is engaged
            // trying to route key to FW should result in OUTPUT_LOST being set
            if(ocp_lock_block_output) {
              if((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_OUTPUT_LOST_MASK) == 0) {
                if(aes_input.aes_expect_err == FALSE){
                  VPRINTF(FATAL, "EXPECTED OUTPUT_LOST to be non-zero since OCP LOCK protections are blocking the output to FW\n");
                  VPRINTF(FATAL,"%c", fail_cmd);
                  while(1);
                }
              }
            
            } else if((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_OUTPUT_LOST_MASK) != 0) {
                if(aes_input.aes_expect_err == FALSE){
                  VPRINTF(FATAL, "EXPECTED OUTPUT_LOST to be 0x0 - Actual: 0x%x", (lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_OUTPUT_LOST_MASK));
                  VPRINTF(FATAL,"%c", fail_cmd);
                  while(1);
                }
            }

            // Read Output Data Block I
            for (int j = 0; j < 4; j++) {
              ciphertext[j] = lsu_read_32(CLP_AES_REG_DATA_OUT_0 + j * 4);
              VPRINTF(MEDIUM, "CIPHERTEXT: 0x%x\n", ciphertext[j]);

              //byte mask
              uint32_t mask = (masked == 0) ? 0xffffffff : 0x00000000;
              //this is the last block, and the partial is inside this dword
              if ((i == num_blocks_text-1) && (partial_text_len > 0) && (partial_text_len >= j*4) && (partial_text_len < (j+1)*4)) {
                mask = (1 << (partial_text_len%4)*8) - 1;
                masked = 0x1;
              }
              
              if(ocp_lock_block_output) {
                if(aes_input.aes_expect_err == FALSE){
                if ((ciphertext[j] & mask) != 0) {
                  VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
                  VPRINTF(FATAL, "Actual   data: 0x%x\n", ciphertext[j] & mask);
                  VPRINTF(FATAL, "Expected data: 0x0\n");
                  SEND_STDOUT_CTRL(fail_cmd);
                  while(1);
                  }
                }
              }
              else if (op == AES_ENC) {
                if(aes_input.aes_expect_err == FALSE){
                if ((ciphertext[j] & mask) != (aes_input.ciphertext[j+i*4] & mask)) {
                  VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
                  VPRINTF(FATAL, "Actual   data: 0x%x\n", ciphertext[j] & mask);
                  VPRINTF(FATAL, "Expected data: 0x%x\n", aes_input.ciphertext[j+i*4] & mask);
                  SEND_STDOUT_CTRL(fail_cmd);
                  while(1);
                }
                }
              } else if (op == AES_DEC) {
                if(aes_input.aes_expect_err == FALSE){
                if ((ciphertext[j] & mask) != (aes_input.plaintext[j+i*4] & mask)) {
                  VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
                  VPRINTF(FATAL, "Actual   data: 0x%x\n", ciphertext[j] & mask);
                  VPRINTF(FATAL, "Expected data: 0x%x\n", aes_input.plaintext[j+i*4] & mask);
                  SEND_STDOUT_CTRL(fail_cmd);
                  while(1);
                }
      }
              }
            }
        } else if(i == 0 && aes_input.key.kv_intf) {
          VPRINTF(LOW, "WAITING FOR KV READ TO FINISH\n");
          kv_poll_valid(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS);
          if(aes_input.key.kv_expect_err == TRUE) {
              VPRINTF(LOW, "EXPECTING KV RD ERR\n");
              kv_expect_error_check(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS);
              break; // If we expect an error, we break out of the loop
          }
          else {
              VPRINTF(LOW, "EXPECTING NO KV RD ERR\n");
              kv_error_check(CLP_AES_CLP_REG_AES_KV_RD_KEY_STATUS);
          }
        }
      }
      if (aes_input.key_o.kv_intf && aes_input.key.kv_expect_err == FALSE) {
        VPRINTF(LOW, "WAITING FOR KV WRITE TO FINISH\n");
        kv_poll_valid(CLP_AES_CLP_REG_AES_KV_WR_STATUS);
        VPRINTF(LOW, "CHECKING FOR KV WRITE ERR\n");
        if(aes_input.key_o.kv_expect_err == TRUE) {
            VPRINTF(LOW, "EXPECTING KV ERR\n");
            kv_expect_error_check(CLP_AES_CLP_REG_AES_KV_WR_STATUS);
        }
        else {
            VPRINTF(LOW, "EXPECTING NO KV ERR\n");
            kv_error_check(CLP_AES_CLP_REG_AES_KV_WR_STATUS);
        }
      }
    }
  }

  // Wait for IDLE
  aes_wait_idle();

  if (mode == AES_GCM && aes_input.key.kv_expect_err == FALSE) {
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

    VPRINTF(LOW, "Read and Compare GCM TAG\n");
    //compare output data to expected tag
    // Read Output Data Block I
    for (int j = 0; j < 4; j++) {
      tag[j] = lsu_read_32(CLP_AES_REG_DATA_OUT_0 + j * 4);
      VPRINTF(MEDIUM, "TAG: 0x%x\n", tag[j]);
      if(aes_input.aes_expect_err == FALSE){
        if (tag[j] != expected_tag[j]) {
          VPRINTF(FATAL,"At offset [%d], tag data mismatch!\n", j);
          VPRINTF(FATAL,"Actual   data: 0x%x\n", tag[j]);
          VPRINTF(FATAL,"Expected data: 0x%x\n", aes_input.tag[j]);
          SEND_STDOUT_CTRL(fail_cmd);
          while(1);
        }
      }
    }
  }
  VPRINTF(LOW, "AES Operation Complete\n");

  // Disable autostart. Note the control register is shadowed and thus needs to be written twice.
  aes_ctrl = 0x1 << AES_REG_CTRL_SHADOWED_MANUAL_OPERATION_LOW;
  lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, aes_ctrl);
  lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, aes_ctrl);

  // Clear all key, IV, Input Data and Output Data registers.
  lsu_write_32(CLP_AES_REG_TRIGGER, (0x1 << AES_REG_TRIGGER_KEY_IV_DATA_IN_CLEAR_LOW) |
                                     (0x1 << AES_REG_TRIGGER_DATA_OUT_CLEAR_LOW));

}

void populate_kv_slot_aes(aes_key_o_t aes_key_o, aes_key_t aes_key, uint32_t override_text_length, uint32_t expected_key[16], uint8_t encrypt, aes_mode_e mode) {
    //CASE1
    VPRINTF(LOW, "Loading KV via AES\n");

    // Check that override_text_length is not larger than 512 bits (16 dwords)
    if (override_text_length > 16) {
        VPRINTF(ERROR, "ERROR: override_text_length (%d) exceeds maximum allowed size of 16 dwords (512 bits)\n", override_text_length);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }   

    // Pre-converted uint32_t arrays (no more hex string conversion needed)
    // Original: "062c4cc774e213bec03b66688e3378e9e2caae3afa446ee67def9a89121ca261736e6ebb609d35b8e667b7230f33bcc90cea0c0c3916597336b9b4d32ca553"
    uint32_t plaintext_data[] = {0xc74c2c06, 0xbe13e274, 0xc03b6668, 0x7e7833e9, 0x3aaecae2, 0xe63e44fa, 0x89aaef7d, 0x61a21c12, 0xbb6e6e73, 0x359d60b8, 0x23b7e668, 0x0f33bcc9, 0xca0ea00c, 0x72916539, 0x36b973b4, 0xa53cd32d}; // 16 dwords
    // Original: "123dead5230958269cde2a5ba7041835"
    uint32_t iv_data[] = {0xd5ea3d12, 0x26580923, 0x95e2cdab, 0x5b418370}; // 4 dwords
    // Original: "123dead526580923"
    uint32_t iv_ctr_data[] = {0xd5ea3d12, 0x26580923, 0x00000000, 0x00000000}; // 2 dwords + 2 dwords padding
    // Original: "bc623095823dafe190993814fedbac4258395063234564534423ad23fcef9ad423"
    uint32_t key_data[] = {0x953062bc, 0xe1af3d82, 0x14839990, 0x42acdbfe, 0x63503958, 0x53644523, 0xfcad2321, 0x4423daef}; // 8 dwords
    // Original: "7f4363949e2ffeea53c83dcc03052b3b3"
    uint32_t tag_data[] = {0x9463437f, 0xfe2f26e9, 0x33dcc853, 0xb3220503}; // 4 dwords
    // Original: "77f2817a9e46515255532b89fc59c5d70ed554f747f32b8ed461b8e152cd30acac36e16bd9b327f6091684313aa6c683464cc93a6ff43d5c579a8cc63ac5b"
    uint32_t ciphertext_GCM[] = {0x7a81f277, 0x5251469e, 0x2b335525, 0x99c5fc89, 0xfd54d70e, 0xf747f32b, 0xb8e1d46f, 0x30accd52, 0x6bc1be36, 0xd27b34f9, 0x09021f68, 0xa6b8313a, 0x934cc683, 0xd543ffa6, 0x8a9cc57d, 0xac5b63ab}; // 16 dwords
    // Original: "f0a5eb3c5d1f06225d1e2b7b6e4bd9b4dd345ba3535c16a9eb0d31cb2f6d8dbed8dc28c92656293c39b43982a8b8c25b882e5253dc7c13ec2d228f95ad5a5a7"
    uint32_t ciphertext_ECB[] = {0x3ceba5f0, 0x22061f5d, 0xb72ce1d3, 0xb4d94b6e, 0xa35b34dd, 0xa9165c53, 0xcb310deb, 0xbe8d6d2f, 0x92ca28dc, 0x293c5611, 0x8239b439, 0x5b2c8b8a, 0x3d25882e, 0x3ec11dc7, 0x9df228d2, 0x7a5ad5a5}; // 16 dwords
    // Original: "caa1e4240ac31d5cd30aaca63cebc5f342d7c377a68a47a6ed077e39c635622d29286ea8eb9b9eeeb0eff321c2470c842408ef9852aa5dc8226c653c6bccc1169"
    uint32_t ciphertext_CBC[] = {0x24e4a1ca, 0x5cd21dc3, 0xa83aac0a, 0xf3c5eb6c, 0x77c3d742, 0xaf478aa6, 0x397e07ed, 0x2d6235c6, 0xa86e2829, 0xee60eeb9, 0x2f21faf3, 0x90c84702, 0xf98ee038, 0x8dc5aa52, 0xc2653c22, 0x6911c6bc}; // 16 dwords
    // Original: "2386abd46d5c7342d4aabf1a6f0b04b8a5a1e4c271f70ee176b1cdf8a2d55f6518906cc377041d26934194a79bd4bd164bb6a171b92e37360376637aae0f135e8"
    uint32_t ciphertext_CFB[] = {0xd4ab8623, 0x42735c6d, 0x1abfaad4, 0xb8040b6f, 0xc2e4a1a5, 0xe10ef771, 0xf8cdb176, 0x565fd52a, 0x73cc9018, 0x2d610477, 0x79a14934, 0xbe16d4bd, 0xa71ab6b4, 0x6073e92b, 0x66ac6737, 0xe835e0f1}; // 16 dwords
    // Original: "23a42c6343e01582637c05325eb01c1848c7091f8bec3c8aadea25cef2c4ebb30dea0fd3a661d08083f38e8bf07739192843a622d238503607dd3a0d36a1baf6c"
    uint32_t ciphertext_OFB[] = {0x632ca423, 0x8215e043, 0x32057c63, 0x181cb05e, 0x1f09c748, 0x8a3cec8b, 0xce25eaad, 0xb3ebc4f2, 0xd30fea0d, 0x880d61a6, 0x8ebaf323, 0x8b19f077, 0x22a6843f, 0x365038d2, 0xd3a07dd3, 0x6caf1b6a}; // 16 dwords
    // Original: "e1c460f06fa47a18ea69cdc3e022b5bc8a3bfab67870189c8e173b0ce6fb904e7e36769776b237ff87f4a6e1c22b6c4e186b3af9cd070a14850405fd0ec5a13da"
    uint32_t ciphertext_CTR[] = {0xf060c4e1, 0x187aa46f, 0xc3cd69ea, 0xbcb522e0, 0xb6fa3b8a, 0x9c187078, 0x0c3b178e, 0x4e90fbe6, 0x9776367e, 0x8737ff2b, 0xe1a6a3f4, 0x4e6c2bc2, 0xf93a6b18, 0x0a14cd07, 0xe7fd0485, 0xda3a15c5}; // 16 dwords
    
    uint32_t *iv;
    uint32_t iv_length;

    uint32_t *key;
    uint32_t key_size;
    
    uint32_t *tag; 
    uint32_t tag_length;

    aes_op_e op = AES_DEC;
    aes_key_len_e key_len = AES_256;
    aes_flow_t aes_input = {0};

    uint32_t *plaintext; // Changed to pointer for direct assignment
    uint32_t plaintext_length = 16 * 4; // 16 dwords from plaintext_data
    uint32_t *ciphertext; // Changed to pointer for direct assignment
    uint32_t ciphertext_length = 16 * 4; // 16 dwords for all cipher modes
       
    if (encrypt) {
        op = AES_ENC;
    }   

    // Direct pointer assignments (no more memcpy calls)
    if (mode == AES_CTR) {
        iv = iv_ctr_data;
        iv_length = 2; // 2 dwords for CTR mode
    } else if (mode != AES_ECB) {
        iv = iv_data;
        iv_length = 4; // 4 dwords for other modes
    }

    plaintext = plaintext_data;

    // Direct pointer assignment instead of memcpy for ciphertext
    if(mode == AES_GCM) {
        ciphertext = ciphertext_GCM;
        tag = tag_data;
        tag_length = 4; // 4 dwords for GCM tag
    } else if (mode == AES_ECB) {
        ciphertext = ciphertext_ECB;
    } else if (mode == AES_CBC) {
        ciphertext = ciphertext_CBC;
    } else if (mode == AES_CFB) {
        ciphertext = ciphertext_CFB;
    } else if (mode == AES_OFB) {
        ciphertext = ciphertext_OFB;
    } else if (mode == AES_CTR) {
        ciphertext = ciphertext_CTR;
    }

    key = key_data;
    key_len =AES_256 ; 

    for (int i = 0; i < 8; i++) {
        aes_key.key_share0[i] = key[i];
        aes_key.key_share1[i] = 0x00000000;
    }


    if(override_text_length > 0) {
        plaintext_length = override_text_length;
        ciphertext_length = override_text_length;
    }   
    VPRINTF(LOW, "Populate KV with key length: %d\n", ciphertext_length);
       
    if (encrypt) {
      for (int i = 0; i < ciphertext_length; i++) {
          expected_key[i] = ciphertext[i];
      }
    } else {
      for (int i = 0; i < plaintext_length; i++) {
          expected_key[i] = plaintext[i];
      }   
    }

       
    aes_input.tag = tag;
    aes_input.key = aes_key;
    aes_input.iv = iv;
    aes_input.aad = 0;
    aes_input.text_len = plaintext_length;
    aes_input.plaintext = plaintext;
    aes_input.ciphertext = ciphertext;
    aes_input.key_o = aes_key_o;
    aes_input.aes_err_inj.sideload_corrupt = TRUE;


    //Run ENC
    aes_flow(op, mode, key_len, aes_input, AES_LITTLE_ENDIAN);

}


