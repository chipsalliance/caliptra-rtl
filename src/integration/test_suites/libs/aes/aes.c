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
#include <stdint.h>
#include <string.h>

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


void aes_flow(aes_op_e op, aes_mode_e mode, aes_key_len_e key_len, aes_flow_t aes_input){
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

      // Wait for INPUT_READY
      while((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_INPUT_READY_MASK) == 0);

      VPRINTF(LOW, "Write AES AAD Block %d\n", i);
      for (int j = 0; j < 4; j++) {
        VPRINTF(HIGH, "Write In Data: 0x%x\n", aes_input.aad[j+i*4]);
        lsu_write_32((CLP_AES_REG_DATA_IN_0 + j * 4), aes_input.aad[j+i*4]);
      }
    }
  }

  // Wait for IDLE
  //aes_wait_idle();

  if (aes_input.text_len > 0) { 
    if (aes_input.data_src_mode == AES_DATA_DMA){
        VPRINTF(LOW, "Streaming in text data via DMA: Source: 0x%x Destination: 0x%x\n", aes_input.dma_transfer_data.src_addr, aes_input.dma_transfer_data.dst_addr);

        soc_ifc_axi_dma_send_axi_to_axi(aes_input.dma_transfer_data.src_addr, 0, aes_input.dma_transfer_data.dst_addr, 0,  aes_input.text_len, 0, 1, gcm_mode);

        soc_ifc_axi_dma_read_ahb_payload(aes_input.dma_transfer_data.dst_addr, 0, read_payload, aes_input.text_len, 0);

        // Compare to cypher text
        for (int j = 0; j < aes_input.text_len/4; j++) {
          VPRINTF(MEDIUM, "CIPHERTEXT: 0x%x\n", read_payload[j]);

          // No masking in AXI mode
          uint32_t mask =  0xffffffff ;
          
          if (op == AES_ENC) {
            if ((read_payload[j] & mask) != (aes_input.ciphertext[j] & mask)) {
              VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
              VPRINTF(FATAL, "Actual   data: 0x%x\n", read_payload[j] & mask);
              VPRINTF(FATAL, "Expected data: 0x%x\n", aes_input.ciphertext[j] & mask);
              VPRINTF(FATAL,"%c", fail_cmd);
              while(1);
            }
          } else if (op == AES_DEC) {
            if ((read_payload[j] & mask) != (aes_input.plaintext[j] & mask)) {
              VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
              VPRINTF(FATAL, "Actual   data: 0x%x\n", read_payload[j] & mask);
              VPRINTF(FATAL, "Expected data: 0x%x\n", aes_input.plaintext[j] & mask);
              VPRINTF(FATAL,"%c", fail_cmd);
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

        if (aes_input.aes_err_inj.sideload_corrupt) {
          aes_ctrl =  lsu_read_32(CLP_AES_REG_CTRL_SHADOWED);
          aes_ctrl ^= AES_REG_CTRL_SHADOWED_SIDELOAD_MASK; // Flip the SIDELOAD bit
        }


        // Write Input Data Block.
        VPRINTF(LOW, "Write AES Input Data Block %d\n", i);
        for (int j = 0; j < 4; j++) {
          if (op == AES_ENC) {
            VPRINTF(HIGH, "Write In Data: 0x%x\n", aes_input.plaintext[j+i*4]);
            lsu_write_32((CLP_AES_REG_DATA_IN_0 + j * 4), aes_input.plaintext[j+i*4]);
          } else if (op == AES_DEC) {
            VPRINTF(HIGH, "Write In Data: 0x%x\n", aes_input.ciphertext[j+i*4]);
            lsu_write_32((CLP_AES_REG_DATA_IN_0 + j * 4), aes_input.ciphertext[j+i*4]);
          }
        }                      
        
        if (aes_input.aes_err_inj.sideload_corrupt) {
          lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, aes_ctrl);
          lsu_write_32(CLP_AES_REG_CTRL_SHADOWED, aes_ctrl);
          VPRINTF(LOW, "ATTEMPT TO FLIP SIDELOAD BIT")
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
                    VPRINTF(FATAL, "EXPECTED OUTPUT_LOST to be non-zero since OCP LOCK protections are blocking the output to FW\n");
                    VPRINTF(FATAL,"%c", fail_cmd);
                    while(1);
                }
            
            } else if((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_OUTPUT_LOST_MASK) != 0) {
                VPRINTF(FATAL, "EXPECTED OUTPUT_LOST to be 0x0 - Actual: 0x%x", (lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_OUTPUT_LOST_MASK));
                VPRINTF(FATAL,"%c", fail_cmd);
                while(1);
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
                if ((ciphertext[j] & mask) != 0) {
                  VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
                  VPRINTF(FATAL, "Actual   data: 0x%x\n", ciphertext[j] & mask);
                  VPRINTF(FATAL, "Expected data: 0x0\n");
                  VPRINTF(FATAL,"%c", fail_cmd);
                  while(1);
                }

              }
              else if (op == AES_ENC) {
                if ((ciphertext[j] & mask) != (aes_input.ciphertext[j+i*4] & mask)) {
                  VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
                  VPRINTF(FATAL, "Actual   data: 0x%x\n", ciphertext[j] & mask);
                  VPRINTF(FATAL, "Expected data: 0x%x\n", aes_input.ciphertext[j+i*4] & mask);
                  VPRINTF(FATAL,"%c", fail_cmd);
                  while(1);
                }
              } else if (op == AES_DEC) {
                if ((ciphertext[j] & mask) != (aes_input.plaintext[j+i*4] & mask)) {
                  VPRINTF(FATAL, "At offset [%d], output data mismatch!\n", j);
                  VPRINTF(FATAL, "Actual   data: 0x%x\n", ciphertext[j] & mask);
                  VPRINTF(FATAL, "Expected data: 0x%x\n", aes_input.plaintext[j+i*4] & mask);
                  VPRINTF(FATAL,"%c", fail_cmd);
                  while(1);
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
    lsu_write_32(CLP_AES_REG_DATA_IN_0, 0);
    lsu_write_32(CLP_AES_REG_DATA_IN_1, length);

    //compute length of text
    length = aes_input.text_len << 3; //convert length from bytes to bits
    length = ((length<<24) & 0xff000000) | //swap the bytes
             ((length<< 8) & 0x00ff0000) |
             ((length>> 8) & 0x0000ff00) |
             ((length>>24) & 0x000000ff);

    VPRINTF(HIGH, "Write Text Length: 0x%x\n", length);
    lsu_write_32(CLP_AES_REG_DATA_IN_2, 0);
    lsu_write_32(CLP_AES_REG_DATA_IN_3, length);

    // Wait for OUTPUT_VALID bit
    while ((lsu_read_32(CLP_AES_REG_STATUS) & AES_REG_STATUS_OUTPUT_VALID_MASK) == 0);

    //compare output data to expected tag
    // Read Output Data Block I
    for (int j = 0; j < 4; j++) {
      tag[j] = lsu_read_32(CLP_AES_REG_DATA_OUT_0 + j * 4);
      VPRINTF(MEDIUM, "TAG: 0x%x\n", tag[j]);
      if (tag[j] != aes_input.tag[j]) {
        VPRINTF(FATAL,"At offset [%d], tag data mismatch!\n", j);
        VPRINTF(FATAL,"Actual   data: 0x%x\n", tag[j]);
        VPRINTF(FATAL,"Expected data: 0x%x\n", aes_input.tag[j]);
        VPRINTF(FATAL,"%c", fail_cmd);
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

void populate_kv_slot_aes(aes_key_o_t aes_key_o, aes_key_t aes_key, uint32_t override_text_length, uint32_t expected_key[16], uint8_t encrypt, aes_mode_e mode) {
    //CASE1
    VPRINTF(LOW, "Loading KV via AES\n");

    // Check that override_text_length is not larger than 512 bits (16 dwords)
    if (override_text_length > 16) {
        VPRINTF(ERROR, "ERROR: override_text_length (%d) exceeds maximum allowed size of 16 dwords (512 bits)\n", override_text_length);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }   
    const char plaintext_str[]   = "062c4cc774e213be68663bc0e933787ee2caae3afa443ee67defaa89121ca261736e6ebbb8609d3568e6b723c9bc330f0ca00eca39659172b473b9362dd33ca5";
    const char iv_str[] = "123dead523095826abcde2957083415b"; // 16 bytes IV for AES
    const char iv_ctr_str[] = "123dead523095826"; // 8 bytes IV for AES CTR
    uint32_t iv[4];
    uint32_t iv_length;

    const char key_str[] = "bc623095823dafe190998314fedbac4258395063234564532123adfcefda2344";
    uint32_t key[8];
    uint32_t key_size;
    
    const char tag_str[] = "7F436394E9262FFE53C8DC33030522B3";
    uint32_t tag[4]; 
    uint32_t tag_length;


    
    
    
    const char ciphertext_str_GCM[]  = "77F2817A9E4651522555332B89FCC5990ED754FD2BF347F76FD4E1B852CDAC3036BEC16BF9347BD2681F02093A31B8A683C64C93A6FF43D57DC59C8AAB635BAC";
    const char ciphertext_str_ECB[]  = "F0A5EB3C5D1F0622D3E12CB76E4BD9B4DD345BA3535C16A9EB0D31CB2F6D8DBEDC28CA9211563C2939B439828A8B2C5B2E88253DC71DC13ED228F29DA5D55A7A";
    const char ciphertext_str_CBC[]  = "CAA1E424C31DD25C0AAC3AA86CEBC5F342D7C377A68A47AFED077E39C635622D29286EA8B9EE60EEF3FA212F0247C89038E08EF952AAC58D223C65C2BCC61169";
    const char ciphertext_str_CFB[]  = "2386ABD46D5C7342D4AABF1A6F0B04B8A5A1E4C271F70EE176B1CDF82AD55F561890CC737704612D3449A179BDD416BEB4B61AA72BE973603767AC66F1E035E8";
    const char ciphertext_str_OFB[]  = "23A42C6343E01582637C05325EB01C1848C7091F8BEC3C8AADEA25CEF2C4EBB30DEA0FD3A6610D8823F3BA8E77F0198B3F84A622D2385036D37DA0D36A1BAF6C";
    const char ciphertext_str_CTR[]  = "E1C460F06FA47A18EA69CDC3E022B5BC8A3BFAB67870189C8E173B0CE6FB904E7E3676972BFF3787F4A3A6E1C22B6C4E186B3AF907CD140A8504FDE7C5153ADA";

    aes_op_e op = AES_DEC;
    aes_key_len_e key_len = AES_256;
    aes_flow_t aes_input;

    uint32_t plaintext[32]; //arbitrary length here
    uint32_t plaintext_length;
    uint32_t ciphertext[32]; //arbitrary length here
    uint32_t ciphertext_length;
       
    if (encrypt) {
        op = AES_ENC;
    }   

    if (mode == AES_CTR) {
        hex_to_uint32_array(iv_ctr_str, iv, &iv_length);
    } else if (mode != AES_ECB) {
        hex_to_uint32_array(iv_str, iv, &iv_length);
    }

    hex_to_uint32_array(plaintext_str, plaintext, &plaintext_length);

    if(mode == AES_GCM) {
        hex_to_uint32_array(ciphertext_str_GCM, ciphertext, &ciphertext_length);
        hex_to_uint32_array(tag_str, tag, &tag_length);
    } else if (mode == AES_ECB) {
        hex_to_uint32_array(ciphertext_str_ECB, ciphertext, &ciphertext_length);
    } else if (mode == AES_CBC) {
        hex_to_uint32_array(ciphertext_str_CBC, ciphertext, &ciphertext_length);
    } else if (mode == AES_CFB) {
        hex_to_uint32_array(ciphertext_str_CFB, ciphertext, &ciphertext_length);
    } else if (mode == AES_OFB) {
        hex_to_uint32_array(ciphertext_str_OFB, ciphertext, &ciphertext_length);
    } else if (mode == AES_CTR) {
        hex_to_uint32_array(ciphertext_str_CTR, ciphertext, &ciphertext_length);
    }



    hex_to_uint32_array(key_str, key, &key_size);
    key_len = key_size == 32 ? AES_256 :
              key_size == 16 ? AES_128 : AES_192;  

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
    aes_flow(op, mode, key_len, aes_input);

}


