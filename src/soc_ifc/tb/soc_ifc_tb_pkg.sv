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
//======================================================================

`ifndef SOC_IFC_TB_PKG
`define SOC_IFC_TB_PKG

`define CALIPTRA_MODE_SUBSYSTEM


package soc_ifc_tb_pkg;

  `include "caliptra_reg_defines.svh" // This is from integration/rtl level 
  `include "caliptra_reg_field_defines.svh"

  localparam SOCIFC_BASE = `CLP_SOC_IFC_REG_BASE_ADDR;
  localparam SHAACC_BASE = `CLP_SHA512_ACC_CSR_BASE_ADDR;
  localparam ADDR_WIDTH = 32; // SHould be 18; will let APB & AHB bus widths truncate as needed
  localparam AXI_USER_WIDTH = 32;

  logic [63:0] strap_ss_caliptra_base_addr_tb;
  logic [63:0] strap_ss_mci_base_addr_tb;
  logic [63:0] strap_ss_recovery_ifc_base_addr_tb;
  logic [63:0] strap_ss_external_staging_area_base_addr_tb;
  logic [63:0] strap_ss_otp_fc_base_addr_tb;
  logic [63:0] strap_ss_uds_seed_base_addr_tb;
  logic [31:0] strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_tb;
  logic [31:0] strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_tb;
  logic [31:0] strap_ss_strap_generic_0_tb;
  logic [31:0] strap_ss_strap_generic_1_tb;
  logic [31:0] strap_ss_strap_generic_2_tb;
  logic [31:0] strap_ss_strap_generic_3_tb;
  logic [31:0] strap_ss_caliptra_dma_axi_user_tb;
  logic        ss_debug_intent_tb;
  logic        subsystem_mode_tb;

  // ================================================================================ 
  // Type declarations 
  // ================================================================================ 

  typedef logic [ADDR_WIDTH-1:0] word_addr_t; 
  typedef logic [31:0] dword_t;

  typedef struct {
    word_addr_t addr;
    int         dwordlen;    
  } addrlen_pair_t; 

  // TODO. Somewhat superfluous declaration to help avoid object references 
  typedef struct {
    word_addr_t addr;
    dword_t     data;
    int         tid;    
  } transaction_t;

  // Useful struct to qualify an int "d" with a valid "v" status
  typedef struct {
    int d;   
    int v;   
  } intpair_t; 

  typedef transaction_t transq_t [$];  

  typedef string strq_t [$];  
  typedef dword_t dwordq_t [$];  
  typedef enum {
    COLD_RESET, WARM_RESET,
    SET_AXI, SET_AHB, SET_DIRECT,
    GET_AXI, GET_AHB, GET_DIRECT
  } access_t; 

  typedef struct {
    word_addr_t addr_min;
    word_addr_t addr_max;
  } extent_t;

  typedef word_addr_t word_addrq_t [$];  

  // ================================================================================ 
  // Constants & Global Data Structures (Private)
  // ================================================================================ 

  // TODO. These are crutches; should be static var inside a class
  int _fuses_locked = 0; 
  // realtime _exp_update_time = 0; 
  int _clk_period = 0;

  // typedef enum logic [2:0] { 
  logic [2:0] _security_state_dict [string] = {
    "DEBUG_UNLOCKED_UNPROVISIONED" : 3'b000, // {DEBUG_UNLOCKED, UNPROVISIONED},     
    "DEBUG_LOCKED_UNPROVISIONED"   : 3'b100, // {DEBUG_LOCKED, UNPROVISIONED},       
    "DEBUG_UNLOCKED_MANUFACTURING" : 3'b001, // {DEBUG_UNLOCKED, MANUFACTURING},     
    "DEBUG_LOCKED_MANUFACTURING"   : 3'b101, // {DEBUG_LOCKED, MANUFACTURING},       
    "DEBUG_UNLOCKED_PRODUCTION"    : 3'b011, // {DEBUG_UNLOCKED, DEVICE_PRODUCTION}, 
    "DEBUG_LOCKED_PRODUCTION"      : 3'b111, // {DEBUG_LOCKED, DEVICE_PRODUCTION},   
    "UNDEFINED2"                   : 3'b010, 
    "UNDEFINED6"                   : 3'b110 
  }; //  security_state_code_t;


  // The whole thing could probably be done slickly using enums but dictionaries 
  // are easier to use and lookup stuff. To be updated if overhead is too high. 

  word_addr_t _wide_register_dict [string] = {
    "CPTRA_FW_EXTENDED_ERROR_INFO"          : 8, 
    "CPTRA_MBOX_VALID_AXI_USER"             : 5,  
    "CPTRA_MBOX_AXI_USER_LOCK"              : 5,  
    "CPTRA_TRNG_DATA"                       : 12,
    "CPTRA_GENERIC_INPUT_WIRES"             : 2,  
    "CPTRA_GENERIC_OUTPUT_WIRES"            : 2,  
    "CPTRA_FW_REV_ID"                       : 2,
    "CPTRA_WDT_TIMER1_TIMEOUT_PERIOD"       : 2, 
    "CPTRA_WDT_TIMER2_TIMEOUT_PERIOD"       : 2, 
    "CPTRA_WDT_CFG"                         : 2, 
    "CPTRA_RSVD_REG"                        : 2, 
    "CPTRA_OWNER_PK_HASH"                   : 12,
    "FUSE_UDS_SEED"                         : 12,
    "FUSE_FIELD_ENTROPY"                    : 8,
    "FUSE_VENDOR_PK_HASH"                   : 12,
    //"FUSE_KEY_MANIFEST_PK_HASH_MASK"        : 8,
    "FUSE_MANUF_DBG_UNLOCK_TOKEN"           : 16,
    "FUSE_RUNTIME_SVN"                      : 4,  
    "FUSE_IDEVID_CERT_ATTR"                 : 24, 
    "FUSE_IDEVID_MANUF_HSM_ID"              : 4, 
    "FUSE_SOC_MANIFEST_SVN"                 : 4,
    "INTERNAL_OBF_KEY"                      : 8,
    "SS_STRAP_GENERIC"                      : 4 ,
    "SS_SOC_DBG_UNLOCK_LEVEL"               : 2, 
    "SS_GENERIC_FW_EXEC_CTRL"               : 4
  };


  // ** NOTE. INTR_BRF (== INTR_BLOCK_RF) registers are NOT explictly tested. Only provided to check for undefined ranges, and for future **
  //  
  // Identifier                                       Base Addr      Offset                                                            // Offset   Description
  word_addr_t _soc_register_dict [string] = {
    "CPTRA_HW_ERROR_FATAL"                          : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_ERROR_FATAL,                                 // 0x000      Hardware Error Fatal 
    "CPTRA_HW_ERROR_NON_FATAL"                      : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL,                             // 0x004      Hardware Error Non-Fatal 
    "CPTRA_FW_ERROR_FATAL"                          : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_ERROR_FATAL,                                 // 0x008      Firmware Error Fatal 
    "CPTRA_FW_ERROR_NON_FATAL"                      : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_ERROR_NON_FATAL,                             // 0x00c      Firmware Error Non-Fatal 
    "CPTRA_HW_ERROR_ENC"                            : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_ERROR_ENC,                                   // 0x010      Hardware Error Encoding 
    "CPTRA_FW_ERROR_ENC"                            : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_ERROR_ENC,                                   // 0x014      Firmware Error Encoding 
    "CPTRA_FW_EXTENDED_ERROR_INFO"                  : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0,                       // 0x018 [8]  Firmware Extended Error Information 
    "CPTRA_BOOT_STATUS"                             : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_BOOT_STATUS,                                    // 0x038      Boot Status 
    "CPTRA_FLOW_STATUS"                             : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FLOW_STATUS,                                    // 0x03c      Flow Status 
    "CPTRA_RESET_REASON"                            : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_RESET_REASON,                                   // 0x040      Reset Reason 
    "CPTRA_SECURITY_STATE"                          : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_SECURITY_STATE,                                 // 0x044      Security State 
    "CPTRA_MBOX_VALID_AXI_USER"                     : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0,                          // 0x048 [5]  Valid User Registers 
    "CPTRA_MBOX_AXI_USER_LOCK"                      : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0,                           // 0x05c [5]  Valid User Register Lock 
    "CPTRA_TRNG_VALID_AXI_USER"                     : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_VALID_AXI_USER,                            // 0x070      Valid User for TRNG 
    "CPTRA_TRNG_AXI_USER_LOCK"                      : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK,                             // 0x074      Valid User for TRNG AXI_USER Lock 
    "CPTRA_TRNG_DATA"                               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_DATA_0,                                    // 0x078 [12] TRNG Data 
    "CPTRA_TRNG_CTRL"                               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_CTRL,                                      // 0x0a8      TRNG Ctrl 
    "CPTRA_TRNG_STATUS"                             : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_STATUS,                                    // 0x0ac      TRNG Status 
    "CPTRA_FUSE_WR_DONE"                            : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FUSE_WR_DONE,                                   // 0x0b0      Fuse Write Done 
    "CPTRA_TIMER_CONFIG"                            : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TIMER_CONFIG,                                   // 0x0b4      Timer Config 
    "CPTRA_BOOTFSM_GO"                              : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_BOOTFSM_GO,                                     // 0x0b8      BOOTFSM GO 
    "CPTRA_DBG_MANUF_SERVICE_REG"                   : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_DBG_MANUF_SERVICE_REG,                          // 0x0bc      DEBUG & MANUF SERVICE REG
    "CPTRA_CLK_GATING_EN"                           : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_CLK_GATING_EN,                                  // 0x0c0      Global Caliptra Clk gating enable 
    "CPTRA_GENERIC_INPUT_WIRES"                     : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0,                          // 0x0c8 [2]  Generic Input Wires 
    "CPTRA_GENERIC_OUTPUT_WIRES"                    : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0,                         // 0x0d0 [2]  Generic Output Wires 
    "CPTRA_HW_REV_ID"                               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_REV_ID,                                      // 0x0d4      Caliptra HW RevID 
    "CPTRA_FW_REV_ID"                               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_REV_ID_0,                                    // 0x0d8 [2]  Caliptra FW RevID
    "CPTRA_HW_CONFIG"                               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_CONFIG,                                      // 0x0e0      Caliptra HW Config
    "CPTRA_WDT_TIMER1_EN"                           : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_TIMER1_EN,                                  // 0x0e4      Caliptra WDT Timer1 EN register  
    "CPTRA_WDT_TIMER1_CTRL"                         : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL,                                // 0x0e8      Caliptra WDT Timer1 CTRL register  
    "CPTRA_WDT_TIMER1_TIMEOUT_PERIOD"               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0,                    // 0x0ec [2]  Caliptra WDT Timer1 Timeout Period register  
    "CPTRA_WDT_TIMER2_EN"                           : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_TIMER2_EN,                                  // 0x0f4      Caliptra WDT Timer2 EN register  
    "CPTRA_WDT_TIMER2_CTRL"                         : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL,                                // 0x0f8      Caliptra WDT Timer2 CTRL register  
    "CPTRA_WDT_TIMER2_TIMEOUT_PERIOD"               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0,                    // 0x0fc [2]  Caliptra WDT Timer2 Timeout Period register  
    "CPTRA_WDT_STATUS"                              : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_STATUS,                                     // 0x104      Caliptra WDT STATUS register
    "CPTRA_FUSE_VALID_AXI_USER"                     : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FUSE_VALID_AXI_USER,                            // 0x108      Valid User for FUSE 
    "CPTRA_FUSE_AXI_USER_LOCK"                      : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK,                             // 0x10c      Valid User for FUSE AXI_USER Lock
    "CPTRA_WDT_CFG"                                 : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_CFG_0,                                      // 0x110 [2]  Caliptra WDT1 Config 	
    "CPTRA_ITRNG_ENTROPY_CONFIG_0"	                : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0,                         // 0x118      Caliptra iTRNG Entropy Configuration 0 	                            
    "CPTRA_ITRNG_ENTROPY_CONFIG_1"	                : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1,                         // 0x11c      Caliptra iTRNG Entropy Configuration 1    
    "CPTRA_RSVD_REG"                                : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_RSVD_REG_0,                                     // 0x120 [2]  Caliptra Reserved Registers
    "CPTRA_HW_CAPABILITIES"                         : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_CAPABILITIES,                                // 0x128      Caliptra HW Capabilities
    "CPTRA_FW_CAPABILITIES"                         : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_CAPABILITIES,                                // 0x12c      Caliptra FW Capabilities
    "CPTRA_CAP_LOCK"                                : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_CAP_LOCK,                                       // 0x130      Caliptra Cap Lock
    // 0x134..0x13c
    "CPTRA_OWNER_PK_HASH"                           : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0,                                // 0x140 [12] - 
    "CPTRA_OWNER_PK_HASH_LOCK"                      : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK,                             // 0x170      - 
    // 0x174..0x1fc
    "FUSE_UDS_SEED"                                 : SOCIFC_BASE + `SOC_IFC_REG_FUSE_UDS_SEED_0,                                      // 0x200 [12] Unique Device Secret 
    "FUSE_FIELD_ENTROPY"                            : SOCIFC_BASE + `SOC_IFC_REG_FUSE_FIELD_ENTROPY_0,                                 // 0x240 [8]  Field Entropy 
    "FUSE_VENDOR_PK_HASH"                           : SOCIFC_BASE + `SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0,                                // 0x260 [12] - 
    "FUSE_ECC_REVOCATION"                           : SOCIFC_BASE + `SOC_IFC_REG_FUSE_ECC_REVOCATION,                                  // 0x290      - 
    // 0x294..0x2b0
    "FUSE_FMC_KEY_MANIFEST_SVN"                     : SOCIFC_BASE + `SOC_IFC_REG_FUSE_FMC_KEY_MANIFEST_SVN,                            // 0x2b4      - 
    "FUSE_RUNTIME_SVN"                              : SOCIFC_BASE + `SOC_IFC_REG_FUSE_RUNTIME_SVN_0,                                   // 0x2b8 [4]  - 
    "FUSE_ANTI_ROLLBACK_DISABLE"                    : SOCIFC_BASE + `SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE,                           // 0x2c8      - 
    "FUSE_IDEVID_CERT_ATTR"                         : SOCIFC_BASE + `SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0,                              // 0x2cc [24] - 
    "FUSE_IDEVID_MANUF_HSM_ID"                      : SOCIFC_BASE + `SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_0,                           // 0x32c [4]  - 
    "FUSE_LMS_REVOCATION"                           : SOCIFC_BASE + `SOC_IFC_REG_FUSE_LMS_REVOCATION,                                  // 0x340      -
    "FUSE_MLDSA_REVOCATION"                         : SOCIFC_BASE + `SOC_IFC_REG_FUSE_MLDSA_REVOCATION,                                // 0x344      -
    "FUSE_SOC_STEPPING_ID"                          : SOCIFC_BASE + `SOC_IFC_REG_FUSE_SOC_STEPPING_ID,                                 // 0x348      - 
    "FUSE_MANUF_DBG_UNLOCK_TOKEN"                   : SOCIFC_BASE + `SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0,                        // 0x34c [16]  Manufcturing Debug Unlock Token
    "FUSE_PQC_KEY_TYPE"                             : SOCIFC_BASE + `SOC_IFC_REG_FUSE_PQC_KEY_TYPE,                                    // 0x38c 
    "FUSE_SOC_MANIFEST_SVN"                         : SOCIFC_BASE + `SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_0,                              // 0x390 [4]
    "FUSE_SOC_MANIFEST_MAX_SVN"                     : SOCIFC_BASE + `SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN,                            // 0x3a0
    "SS_CPTRA_BASE_ADDR_L"                    : SOCIFC_BASE + `SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L,                               // 0x500
    "SS_CPTRA_BASE_ADDR_H"                    : SOCIFC_BASE + `SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_H,                               // 0x504
    "SS_MCI_BASE_ADDR_L"                      : SOCIFC_BASE + `SOC_IFC_REG_SS_MCI_BASE_ADDR_L,                                    // 0x508
    "SS_MCI_BASE_ADDR_H"                      : SOCIFC_BASE + `SOC_IFC_REG_SS_MCI_BASE_ADDR_H,                                    // 0x50c
    "SS_RECOVERY_IFC_BASE_ADDR_L"             : SOCIFC_BASE + `SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L,                           // 0x510
    "SS_RECOVERY_IFC_BASE_ADDR_H"             : SOCIFC_BASE + `SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_H,                           // 0x514
    "SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L"    : SOCIFC_BASE + `SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L,                           // 0x510
    "SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H"    : SOCIFC_BASE + `SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H,                           // 0x514
    "SS_OTP_FC_BASE_ADDR_L"                   : SOCIFC_BASE + `SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_L,                                 // 0x518
    "SS_OTP_FC_BASE_ADDR_H"                   : SOCIFC_BASE + `SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_H,                                 // 0x51c
    "SS_UDS_SEED_BASE_ADDR_L"                 : SOCIFC_BASE + `SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L,                               // 0x520
    "SS_UDS_BASE_ADDR_H"                      : SOCIFC_BASE + `SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_H,                               // 0x524
    "SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET" : SOCIFC_BASE + `SOC_IFC_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET, // 0x528
    "SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES"        : SOCIFC_BASE + `SOC_IFC_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES,        // 0x52c
    "SS_DEBUG_INTENT"                               : SOCIFC_BASE + `SOC_IFC_REG_SS_DEBUG_INTENT,                                       // 0x530
    "SS_CPTRA_DMA_AXI_USER"                   : SOCIFC_BASE + `SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER,                              // 0x534
    "SS_CPTRA_STAGING_AREA_BASE_ADDR_L"       : SOCIFC_BASE + `SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L,                  // 0x538
    "SS_CPTRA_STAGING_AREA_BASE_ADDR_H"       : SOCIFC_BASE + `SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H,                  // 0x53c
    // 0x540..0x59c
    "SS_STRAP_GENERIC"                              : SOCIFC_BASE + `SOC_IFC_REG_SS_STRAP_GENERIC_0,                                    // 0x5a0 [4]
    // 0x5b0..0x5bc
    "SS_DBG_SERVICE_REG_REQ"                        : SOCIFC_BASE + `SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ,                                 // 0x5c0
    "SS_DBG_SERVICE_REG_RSP"                  : SOCIFC_BASE + `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP,                           // 0x5c4
    "SS_SOC_DBG_UNLOCK_LEVEL"                       : SOCIFC_BASE + `SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_0,                              // 0x5c8 [2]
    "SS_GENERIC_FW_EXEC_CTRL"                       : SOCIFC_BASE + `SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0,                              // 0x5d0 [4]
    // 0x5e0..0x5fc           
    "INTERNAL_OBF_KEY"                              : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_OBF_KEY_0,                                   // 0x600 [8]  De-Obfuscation Key 
    "INTERNAL_ICCM_LOCK"                            : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_ICCM_LOCK,                                   // 0x620      ICCM Lock 
    "INTERNAL_FW_UPDATE_RESET"                      : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET,                             // 0x624      FW Update Reset 
    "INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES"          : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES,                 // 0x628      FW Update Reset Wait Cycles 
    "INTERNAL_NMI_VECTOR"                           : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_NMI_VECTOR,                                  // 0x62c      NMI Vector 
    "INTERNAL_HW_ERROR_FATAL_MASK"                  : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK,                         // 0x630      Hardware Error Fatal Mask   
    "INTERNAL_HW_ERROR_NON_FATAL_MASK"              : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK,                     // 0x634      Hardware Error Non-Fatal Mask   
    "INTERNAL_FW_ERROR_FATAL_MASK"                  : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_FW_ERROR_FATAL_MASK,                         // 0x638      Firmware Error Fatal Mask   
    "INTERNAL_FW_ERROR_NON_FATAL_MASK"              : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK,                     // 0x63C      Firmware Error Non-Fatal Mask 0
    "INTERNAL_RV_MTIME_L"                           : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_RV_MTIME_L,                                  // 0x640      mtime low   
    "INTERNAL_RV_MTIME_H"                           : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_RV_MTIME_H,                                  // 0x644      mtime high  
    "INTERNAL_RV_MTIMECMP_L"                        : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_RV_MTIMECMP_L,                               // 0x648      mtimecmp low  
    "INTERNAL_RV_MTIMECMP_H"                        : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_RV_MTIMECMP_H,                               // 0x64C      mtimecmp high
    // 0x650..0x7fc    
    // SoC IFC Interrupt Block Register 
    "INTR_BRF_GLOBAL_INTR_EN_R"                     : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R,                       // 0x800
    "INTR_BRF_ERROR_INTR_EN_R"                      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R,                        // 0x804
    "INTR_BRF_NOTIF_INTR_EN_R"                      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R,                        // 0x808
    "INTR_BRF_ERROR_GLOBAL_INTR_R"                  : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R,                    // 0x80c
    "INTR_BRF_NOTIF_GLOBAL_INTR_R"                  : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R,                    // 0x810
    "INTR_BRF_ERROR_INTERNAL_INTR_R"                : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R,                  // 0x814
    "INTR_BRF_NOTIF_INTERNAL_INTR_R"                : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R,                  // 0x818
    "INTR_BRF_ERROR_INTR_TRIG_R"                    : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R,                      // 0x81c
    "INTR_BRF_NOTIF_INTR_TRIG_R"                    : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R,                      // 0x820
    // 0x824..0x8fc
    "INTR_BRF_ERROR_INTERNAL_INTR_COUNT_R"          : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R,            // 0x900
    "INTR_BRF_ERROR_INV_DEV_INTR_COUNT_R"           : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R,             // 0x904
    "INTR_BRF_ERROR_CMD_FAIL_INTR_COUNT_R"          : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R,            // 0x908
    "INTR_BRF_ERROR_BAD_FUSE_INTR_COUNT_R"          : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R,            // 0x90c
    "INTR_BRF_ERROR_ICCM_BLOCKED_INTR_COUNT_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R,        // 0x910
    "INTR_BRF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R,        // 0x914
    "INTR_BRF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R": SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R,  // 0x918   
    "INTR_BRF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R": SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R,  // 0x91c   
    // 0x920..0x97c
    "INTR_BRF_NOTIF_CMD_AVAIL_INTR_COUNT_R"         : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R,           // 0x980
    "INTR_BRF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R,        // 0x984
    "INTR_BRF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R,        // 0x988
    "INTR_BRF_NOTIF_SCAN_MODE_INTR_COUNT_R"         : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R,           // 0x98c 
    "INTR_BRF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R,        // 0x990 
    "INTR_BRF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R"     : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R,       // 0x994
    // 0x998..0x9fc 
    "INTR_BRF_ERROR_INTERNAL_INTR_COUNT_INCR_R"     : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R,       // 0xa00
    "INTR_BRF_ERROR_INV_DEV_INTR_COUNT_INCR_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R,        // 0xa04
    "INTR_BRF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R"     : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R,       // 0xa08
    "INTR_BRF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R"     : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R,       // 0xa0c
    "INTR_BRF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R" : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R,   // 0xa10
    "INTR_BRF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R" : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R,   // 0xa14
    "INTR_BRF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R" : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R,  // 0xa18  
    "INTR_BRF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R" : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R,  // 0xa1c  
    "INTR_BRF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R"       : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R,    // 0xa20
    "INTR_BRF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R"    : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R, // 0xa24   
    "INTR_BRF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R"    : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R, // 0xa28 
    "INTR_BRF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R"       : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R,    // 0xa2c
    "INTR_BRF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R"    : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R, // 0xa30
    "INTR_BRF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R"   : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R, // 0xa34

    // SHA Accelerator Interrupt Block Registers
    "SHA_ACC_INTR_BRF_GLOBAL_INTR_EN_R"                : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R,                  // 0x800   Per-Type Intr Enable Reg   
    "SHA_ACC_INTR_BRF_ERROR_INTR_EN_R"                 : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R,                   // 0x804   Per-Event Intr Enable Reg  
    "SHA_ACC_INTR_BRF_NOTIF_INTR_EN_R"                 : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R,                   // 0x808   Per-Event Intr Enable Reg  
    "SHA_ACC_INTR_BRF_ERROR_GLOBAL_INTR_R"             : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R,               // 0x80C   Intr Status Agg Reg type def    
    "SHA_ACC_INTR_BRF_NOTIF_GLOBAL_INTR_R"             : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R,               // 0x810   Intr Status Agg Reg type def    
    "SHA_ACC_INTR_BRF_ERROR_INTERNAL_INTR_R"           : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R,             // 0x814   Intr Status Reg type def    
    "SHA_ACC_INTR_BRF_NOTIF_INTERNAL_INTR_R"           : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R,             // 0x818   Intr Status Reg type def    
    "SHA_ACC_INTR_BRF_ERROR_INTR_TRIG_R"               : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R,                 // 0x81C   Intr Trigger Reg type def   
    "SHA_ACC_INTR_BRF_NOTIF_INTR_TRIG_R"               : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R,                 // 0x820   Intr Trigger Reg type def   
    // 0x824..0x8fc   
    "SHA_ACC_INTR_BRF_ERROR0_INTR_COUNT_R"             : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_R,               // 0x900   Intr Event Counter  
    "SHA_ACC_INTR_BRF_ERROR1_INTR_COUNT_R"             : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_R,               // 0x904   Intr Event Counter  
    "SHA_ACC_INTR_BRF_ERROR2_INTR_COUNT_R"             : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_R,               // 0x908   Intr Event Counter  
    "SHA_ACC_INTR_BRF_ERROR3_INTR_COUNT_R"             : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_R,               // 0x90C   Intr Event Counter  
    // 0x910..0x97c 
    "SHA_ACC_INTR_BRF_NOTIF_CMD_DONE_INTR_COUNT_R"     : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_R,       // 0x980   Intr Event Counter  
    // 0x984..0x9fc
    "SHA_ACC_INTR_BRF_ERROR0_INTR_COUNT_INCR_R"        : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R,          // 0xa00   Intr Event Count Incr
    "SHA_ACC_INTR_BRF_ERROR1_INTR_COUNT_INCR_R"        : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R,          // 0xa04   Intr Event Count Incr
    "SHA_ACC_INTR_BRF_ERROR2_INTR_COUNT_INCR_R"        : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R,          // 0xa08   Intr Event Count Incr
    "SHA_ACC_INTR_BRF_ERROR3_INTR_COUNT_INCR_R"        : SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R,          // 0xa0C   Intr Event Count Incr
    "SHA_ACC_INTR_BRF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R": SHAACC_BASE + `SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R   // 0xa10   Intr Event Count Incr
  };
                                                                                        
  
  // These address ranges (inclusive) in each extent have no definition 
  extent_t _undefined_addr_ranges [$] = {
    '{addr_min: SOCIFC_BASE + 16'h0134, addr_max: SOCIFC_BASE + 16'h013c},
    '{addr_min: SOCIFC_BASE + 16'h0174, addr_max: SOCIFC_BASE + 16'h01fc},
    '{addr_min: SOCIFC_BASE + 16'h0294, addr_max: SOCIFC_BASE + 16'h02b0},
    '{addr_min: SOCIFC_BASE + 16'h03a4, addr_max: SOCIFC_BASE + 16'h04fc},
    '{addr_min: SOCIFC_BASE + 16'h0540, addr_max: SOCIFC_BASE + 16'h059c},
    '{addr_min: SOCIFC_BASE + 16'h05b0, addr_max: SOCIFC_BASE + 16'h05bc},
    '{addr_min: SOCIFC_BASE + 16'h05e0, addr_max: SOCIFC_BASE + 16'h05fc},
    '{addr_min: SOCIFC_BASE + 16'h0650, addr_max: SOCIFC_BASE + 16'h07fc},
    '{addr_min: SOCIFC_BASE + 16'h0824, addr_max: SOCIFC_BASE + 16'h08fc},
    '{addr_min: SOCIFC_BASE + 16'h0920, addr_max: SOCIFC_BASE + 16'h097c},
    '{addr_min: SOCIFC_BASE + 16'h0998, addr_max: SOCIFC_BASE + 16'h09fc}
  };
 

  // Only non-zero power-on values are stored; also populated by SocRegisters instantiation 
  dword_t _soc_register_initval_dict [string] = {
    "CPTRA_MBOX_VALID_AXI_USER"              : 32'hffff_ffff,
    "CPTRA_TRNG_VALID_AXI_USER"              : 32'hffff_ffff,
    "INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES" : 32'h5,
    "CPTRA_HW_REV_ID"                      : 32'h02,
    //"CPTRA_HW_CONFIG"                      : 32'h0000_0010,  // LMS Acc Cap bit is set
    "CPTRA_WDT_TIMER1_TIMEOUT_PERIOD"      : 32'hffff_ffff,
    "CPTRA_WDT_TIMER2_TIMEOUT_PERIOD"      : 32'hffff_ffff,
    "CPTRA_FUSE_VALID_AXI_USER"              : 32'hffff_ffff 
    //"SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES": 32'h8
  };

  dword_t _soc_register_initval_passive_dict [string] = {
    "CPTRA_HW_CONFIG"                      : 32'h0000_0010  // LMS Acc Cap bit is set
  };

  dword_t _soc_register_initval_ss_dict [string] = {
    "CPTRA_HW_CONFIG"                      : 32'h0000_0030  // LMS Acc Cap bit is set
  };


  // Sticky registers preserve values across warm reset -- groups of regs might be populated by code
  // mask of all bits to be protected in case of warm reset
  word_addr_t _sticky_register_prefix_dict [string] = {
    "FUSE_UDS_SEED"                                    : 32'hffff_ffff,
    "FUSE_FIELD_ENTROPY"                               : 32'hffff_ffff,
    "FUSE_VENDOR_PK_HASH"                              : 32'hffff_ffff ,
    "FUSE_ECC_REVOCATION"                              : 32'hf,          // field 3:0
    "FUSE_FMC_KEY_MANIFEST_SVN"                        : 32'hffff_ffff, 
    "FUSE_RUNTIME_SVN"                                 : 32'hffff_ffff, 
    "FUSE_ANTI_ROLLBACK_DISABLE"                       : 32'h1,          // field 0
    "FUSE_IDEVID_CERT_ATTR"                            : 32'hffff_ffff, 
    "FUSE_IDEVID_MANUF_HSM_ID"                         : 32'hffff_ffff, 
    "FUSE_LMS_REVOCATION"                              : 32'hffff_ffff,
    "FUSE_MLDSA_REVOCATION"                            : 32'hf,
    "FUSE_SOC_STEPPING_ID"                             : 32'hffff,       // field 15:0
    "FUSE_MANUF_DBG_UNLOCK_TOKEN"                      : 32'hffff_ffff,
    "FUSE_PQC_KEY_TYPE"                                : 32'h3,          // field 1:0
    "FUSE_SOC_MANIFEST_SVN"                            : 32'hffff_ffff, 
    "FUSE_SOC_MANIFEST_MAX_SVN"                        : 32'hff,         // field 7:0
    "CPTRA_HW_ERROR_"                                  : 32'hffff_ffff,  // FATAL, NON_FATAL, ENC                          
    "CPTRA_FW_ERROR_"                                  : 32'hffff_ffff,  // FATAL, NON_FATAL, ENC                          
    "CPTRA_FW_EXTENDED_ERROR_INFO"                     : 32'hffff_ffff,
    "CPTRA_RESET_REASON"                               : 32'h2,          // field WARM_RESET 
    "CPTRA_FUSE_WR_DONE"                               : 32'h1,          // field 0 
    "CPTRA_HW_REV_ID"                                  : 32'hffff_ffff,  // field SOC_STEPPING_ID, CPTRA_GENERATION
    "CPTRA_HW_CONFIG"                                  : 32'h0000_003F,  // All existing bits are sticky
    "CPTRA_FUSE_VALID_AXI_USER"                        : 32'hffff_ffff,
    "CPTRA_FUSE_AXI_USER_LOCK"                         : 32'h1,
    "CPTRA_TIMER_CONFIG"                               : 32'hffff_ffff,                           
    "CPTRA_WDT_CFG"                                    : 32'hffff_ffff,                           
    "CPTRA_OWNER_PK_HASH"                              : 32'hffff_ffff, 
    "CPTRA_OWNER_PK_HASH_LOCK"                         : 32'h1, 
    "INTERNAL_RV_MTIME"                                : 32'hffff_ffff, // for MTIME_L/H, MTIMECMP_L/H
    "INTR_BRF_ERROR_INTERNAL_INTR_R"                   : 32'hff,        // fields 5:0
    "INTR_BRF_ERROR_INTERNAL_INTR_COUNT_R"             : 32'hffff_ffff,          
    "INTR_BRF_ERROR_INV_DEV_INTR_COUNT_R"              : 32'hffff_ffff,
    "INTR_BRF_ERROR_CMD_FAIL_INTR_COUNT_R"             : 32'hffff_ffff,
    "INTR_BRF_ERROR_BAD_FUSE_INTR_COUNT_R"             : 32'hffff_ffff,
    "INTR_BRF_ERROR_ICCM_BLOCKED_INTR_COUNT_R"         : 32'hffff_ffff,
    "INTR_BRF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R"         : 32'hffff_ffff,
    "INTR_BRF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R"   : 32'hffff_ffff,
    "INTR_BRF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R"   : 32'hffff_ffff,
    "SS_CPTRA_BASE_ADDR_L"                             : 32'hffff_ffff,
    "SS_CPTRA_BASE_ADDR_H"                             : 32'hffff_ffff,
    "SS_MCI_BASE_ADDR_L"                               : 32'hffff_ffff,
    "SS_MCI_BASE_ADDR_H"                               : 32'hffff_ffff,
    "SS_RECOVERY_IFC_BASE_ADDR_L"                      : 32'hffff_ffff,
    "SS_RECOVERY_IFC_BASE_ADDR_H"                      : 32'hffff_ffff,
    "SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L"             : 32'hffff_ffff,
    "SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H"             : 32'hffff_ffff,
    "SS_OTP_FC_BASE_ADDR_L"                            : 32'hffff_ffff,
    "SS_OTP_FC_BASE_ADDR_H"                            : 32'hffff_ffff,
    "SS_UDS_SEED_BASE_ADDR_L"                          : 32'hffff_ffff,
    "SS_UDS_BASE_ADDR_H"                               : 32'hffff_ffff,
    "SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET" : 32'hffff_ffff,
    "SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES"        : 32'hffff_ffff,
    "SS_DEBUG_INTENT"                                  : 32'h1,
    "SS_CPTRA_DMA_AXI_USER"                            : 32'hffff_ffff,
    "SS_STRAP_GENERIC"                                 : 32'hffff_ffff
  };


  // mask bits that reflect which fields can be modified  
  dword_t _soc_register_mask_dict [string] = {
    "CPTRA_HW_CONFIG"                                  : (`SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK    |
                                                          `SOC_IFC_REG_CPTRA_HW_CONFIG_RSVD_EN_MASK     |                                                  
                                                          `SOC_IFC_REG_CPTRA_HW_CONFIG_LMS_ACC_EN_MASK  |
                                                          `SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK  ),
    "CPTRA_FLOW_STATUS"                                : (`SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK             |
                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_IDEVID_CSR_READY_MASK   |
                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK       |
                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK  |
                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_MASK),
    "CPTRA_MBOX_AXI_USER_LOCK"                           : `SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0_LOCK_MASK,   // same for all 5 pausers
    "CPTRA_TRNG_AXI_USER_LOCK"                           : `SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK_LOCK_MASK,
    "CPTRA_TRNG_CTRL"                                  : `SOC_IFC_REG_CPTRA_TRNG_CTRL_CLEAR_MASK,
    "CPTRA_TRNG_STATUS.APB"                            : `SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_MASK, 
    "CPTRA_TRNG_STATUS.AHB"                            : `SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_REQ_MASK,     
    "CPTRA_FUSE_WR_DONE"                               : `SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK,
    "CPTRA_BOOTFSM_GO"                                 : `SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_MASK, 
    "CPTRA_CLK_GATING_EN"                              : `SOC_IFC_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_MASK,
    "CPTRA_HW_REV_ID"                                  : (`SOC_IFC_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_MASK |  
                                                          `SOC_IFC_REG_CPTRA_HW_REV_ID_SOC_STEPPING_ID_MASK), 
    "CPTRA_WDT_TIMER1_EN"                              : `SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK,
    "CPTRA_WDT_TIMER1_CTRL"                            : `SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK,
    "CPTRA_WDT_TIMER2_EN"                              : `SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK,
    "CPTRA_WDT_TIMER2_CTRL"                            : `SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_MASK,
    "CPTRA_WDT_STATUS"                                 : (`SOC_IFC_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_MASK | 
                                                          `SOC_IFC_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_MASK),
    "CPTRA_FUSE_AXI_USER_LOCK"                           : `SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK_LOCK_MASK, 
    "CPTRA_OWNER_PK_HASH_LOCK"                         : `SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK_LOCK_MASK,
    "CPTRA_CAP_LOCK_MASK"                              : `SOC_IFC_REG_CPTRA_CAP_LOCK_LOCK_MASK, 
    "FUSE_ANTI_ROLLBACK_DISABLE"                       : `SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_MASK, 
    "FUSE_ECC_REVOCATION"                              : `SOC_IFC_REG_FUSE_ECC_REVOCATION_ECC_REVOCATION_MASK,
    "FUSE_MLDSA_REVOCATION"                            : `SOC_IFC_REG_FUSE_MLDSA_REVOCATION_MLDSA_REVOCATION_MASK,
    "FUSE_SOC_STEPPING_ID"                             : `SOC_IFC_REG_FUSE_SOC_STEPPING_ID_SOC_STEPPING_ID_MASK,
    "FUSE_PQC_KEY_TYPE"                                : `SOC_IFC_REG_FUSE_PQC_KEY_TYPE_KEY_TYPE_MASK,
    "FUSE_SOC_MANIFEST_MAX_SVN"                        : `SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN_SVN_MASK,
    "SS_DEBUG_INTENT"                                  : `SOC_IFC_REG_SS_DEBUG_INTENT_DEBUG_INTENT_MASK,   
    "SS_DBG_SERVICE_REG_REQ"                           : (`SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_MANUF_DBG_UNLOCK_REQ_MASK | 
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_PROD_DBG_UNLOCK_REQ_MASK  |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ_UDS_PROGRAM_REQ_MASK),
    "SS_DBG_SERVICE_REG_RSP"                     : (`SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK     | 
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK     |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_MASK      |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_MASK         |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_MASK  |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK          |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK             |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK), 
    "SS_DBG_SERVICE_REG_RSP_PROD_UNLOCK"         : (`SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_SUCCESS_MASK      |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_FAIL_MASK         |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_PROD_DBG_UNLOCK_IN_PROGRESS_MASK  |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK          |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK             |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK      |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK), 
    "SS_DBG_SERVICE_REG_RSP_MANUF_UNLOCK"        : (`SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_SUCCESS_MASK     | 
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_FAIL_MASK        |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_MANUF_DBG_UNLOCK_IN_PROGRESS_MASK |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_SUCCESS_MASK          |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_FAIL_MASK             |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_UDS_PROGRAM_IN_PROGRESS_MASK      |
                                                          `SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP_TAP_MAILBOX_AVAILABLE_MASK), 
    "INTERNAL_ICCM_LOCK"                               : `SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK, 
    "INTERNAL_FW_UPDATE_RESET"                         : `SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK,
    "INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES"             : `SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES_WAIT_CYCLES_MASK,
    "INTERNAL_HW_ERROR_FATAL_MASK"                     : (`SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_NMI_PIN_MASK      | 
                                                          `SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_DCCM_ECC_UNC_MASK |
                                                          `SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK_MASK_ICCM_ECC_UNC_MASK), 
    "INTERNAL_HW_ERROR_NON_FATAL_MASK"                 : (`SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_NO_LOCK_MASK | 
                                                          `SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_PROT_OOO_MASK     | 
                                                          `SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK_MASK_MBOX_ECC_UNC_MASK),      
    "INTR_BRF_GLOBAL_INTR_EN_R"                        : (`SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK | 
                                                          `SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK),    
    "INTR_BRF_ERROR_INTR_EN_R"                        :  (`SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_MASK           |
                                                          `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INV_DEV_EN_MASK            |
                                                          `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_CMD_FAIL_EN_MASK           |
                                                          `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_BAD_FUSE_EN_MASK           |
                                                          `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_ICCM_BLOCKED_EN_MASK       |
                                                          `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_MBOX_ECC_UNC_EN_MASK       |
                                                          `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK |
                                                          `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK ),
    "INTR_BRF_NOTIF_INTR_EN_R" :                        (`SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_AVAIL_EN_MASK     |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_MBOX_ECC_COR_EN_MASK  |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_DEBUG_LOCKED_EN_MASK  |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_SCAN_MODE_EN_MASK     |                     
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_SOC_REQ_LOCK_EN_MASK  |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_GEN_IN_TOGGLE_EN_MASK ),
    "INTR_BRF_ERROR_GLOBAL_INTR_R" :                     `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK,
    "INTR_BRF_NOTIF_GLOBAL_INTR_R" :                     `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK, 
    "INTR_BRF_ERROR_INTERNAL_INTR_R":                   (`SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK            |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK             |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK            |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK            |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_MASK        |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK        |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK  |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK  ),
    "INTR_BRF_NOTIF_INTERNAL_INTR_R":                   (`SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK        |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK     |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK     |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK        |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SOC_REQ_LOCK_STS_MASK     |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK    ),
    "INTR_BRF_ERROR_INTR_TRIG_R":                       (`SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INTERNAL_TRIG_MASK            |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_INV_DEV_TRIG_MASK             |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_CMD_FAIL_TRIG_MASK            |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_BAD_FUSE_TRIG_MASK            |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_ICCM_BLOCKED_TRIG_MASK        |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_MBOX_ECC_UNC_TRIG_MASK        |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_WDT_TIMER1_TIMEOUT_TRIG_MASK  |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR_WDT_TIMER2_TIMEOUT_TRIG_MASK  ),
    "INTR_BRF_NOTIF_INTR_TRIG_R":                       (`SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_AVAIL_TRIG_MASK           |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_MBOX_ECC_COR_TRIG_MASK        |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_DEBUG_LOCKED_TRIG_MASK        |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_SCAN_MODE_TRIG_MASK           |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_SOC_REQ_LOCK_TRIG_MASK        |
                                                         `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_GEN_IN_TOGGLE_TRIG_MASK       ),
    "INTR_BRF_ERROR_INTERNAL_INTR_COUNT_INCR_R"        : `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_MASK,   
    "INTR_BRF_ERROR_INV_DEV_INTR_COUNT_INCR_R"         : `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R_PULSE_MASK,
    "INTR_BRF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R"        : `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R_PULSE_MASK,
    "INTR_BRF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R"        : `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R_PULSE_MASK,
    "INTR_BRF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R"    : `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R_PULSE_MASK,
    "INTR_BRF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R"    : `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R_PULSE_MASK,
    "INTR_BRF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R" : `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK,
    "INTR_BRF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R" : `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R_PULSE_MASK,
    "INTR_BRF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R"       : `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_MASK,
    "INTR_BRF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R"    : `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R_PULSE_MASK,
    "INTR_BRF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R"    : `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_PULSE_MASK, 
    "INTR_BRF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R"    : `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R_PULSE_MASK,
    // SHA Accelerator Interrupt Block Registers
    "SHA_ACC_INTR_BRF_GLOBAL_INTR_EN_R"                :(`SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK |    
                                                         `SHA512_ACC_CSR_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_NOTIF_EN_MASK ),
    "SHA_ACC_INTR_BRF_ERROR_INTR_EN_R"                 :(`SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR0_EN_MASK |                
                                                         `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR1_EN_MASK |                
                                                         `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR2_EN_MASK |                
                                                         `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR3_EN_MASK ),               
    "SHA_ACC_INTR_BRF_NOTIF_INTR_EN_R"                 : `SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_CMD_DONE_EN_MASK,
    "SHA_ACC_INTR_BRF_ERROR_GLOBAL_INTR_R"             : `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R_AGG_STS_MASK,         
    "SHA_ACC_INTR_BRF_NOTIF_GLOBAL_INTR_R"             : `SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R_AGG_STS_MASK,               
    "SHA_ACC_INTR_BRF_ERROR_INTERNAL_INTR_R"           :(`SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR0_STS_MASK |         
                                                         `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR1_STS_MASK |         
                                                         `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR2_STS_MASK |         
                                                         `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR3_STS_MASK ),        
    "SHA_ACC_INTR_BRF_NOTIF_INTERNAL_INTR_R"           : `SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK,  
    "SHA_ACC_INTR_BRF_ERROR_INTR_TRIG_R"               :(`SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR0_TRIG_MASK |         
                                                         `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR1_TRIG_MASK |         
                                                         `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR2_TRIG_MASK |         
                                                         `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR_INTR_TRIG_R_ERROR3_TRIG_MASK ),        
    "SHA_ACC_INTR_BRF_NOTIF_INTR_TRIG_R"               : `SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R_NOTIF_CMD_DONE_TRIG_MASK,
    "SHA_ACC_INTR_BRF_ERROR0_INTR_COUNT_INCR_R"        : `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR0_INTR_COUNT_INCR_R_PULSE_MASK,            
    "SHA_ACC_INTR_BRF_ERROR1_INTR_COUNT_INCR_R"        : `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR1_INTR_COUNT_INCR_R_PULSE_MASK,            
    "SHA_ACC_INTR_BRF_ERROR2_INTR_COUNT_INCR_R"        : `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR2_INTR_COUNT_INCR_R_PULSE_MASK,            
    "SHA_ACC_INTR_BRF_ERROR3_INTR_COUNT_INCR_R"        : `SHA512_ACC_CSR_INTR_BLOCK_RF_ERROR3_INTR_COUNT_INCR_R_PULSE_MASK,            
    "SHA_ACC_INTR_BRF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R": `SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_CMD_DONE_INTR_COUNT_INCR_R_PULSE_MASK     
  };  


  // holds addr -> name inverse map of _soc_register_dict - populated by SocRegisters instantiation 
  string _imap_soc_register_dict [word_addr_t]; 

  // Populated by SocRegisters instantiation
  word_addr_t _exp_register_data_dict [string]; 

  // pulsed registers - includes self-clearing bits
  string _pulsed_regnames [] = {
    "INTERNAL_FW_UPDATE_RESET",
    "INTR_BRF_ERROR_INTERNAL_INTR_COUNT_INCR_R"      ,        
    "INTR_BRF_ERROR_INV_DEV_INTR_COUNT_INCR_R"       ,
    "INTR_BRF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R"      ,
    "INTR_BRF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R"      ,
    "INTR_BRF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R"  ,
    "INTR_BRF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R"  ,
    "INTR_BRF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R" ,
    "INTR_BRF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R" , 
    "INTR_BRF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R"     ,
    "INTR_BRF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R"  ,
    "INTR_BRF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R"  , 
    "INTR_BRF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R"        
    // "INTR_BRF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R"    // TODO. Check for saturation!
  }; 


  // ================================================================================ 
  // Functions 
  // ================================================================================ 

  function int get_ss_code(input string ss_name);

    if (_security_state_dict.exists(ss_name)) 
      return int'(_security_state_dict[ss_name]);
    else 
      return -1;

  endfunction // get_ss_code


  function string get_ss_name(input int ss_code);

    logic [2:0] ss_code_3bit; 

    foreach (_security_state_dict[ss_name]) begin
      if (_security_state_dict[ss_name] == ss_code[2:0]) 
        return ss_name; 
    end
    return "";

  endfunction // get_ss_name


  function dword_t get_mask(string addr_name);

    return _soc_register_mask_dict.exists(addr_name) ? _soc_register_mask_dict[addr_name] : 32'hffff_ffff; 

  endfunction // get_mask


  function dword_t get_initval(string addr_name);
    if (str_startswith(addr_name, "SS_") && 
        !str_contains(addr_name, "SS_GENERIC_FW_EXEC_CTRL") && 
        !str_contains(addr_name, "SS_DBG_SERVICE_REG")) begin
      //$display("SS string match");
      case (addr_name)
        "SS_CPTRA_BASE_ADDR_L"                    : return strap_ss_caliptra_base_addr_tb[31:0];
        "SS_CPTRA_BASE_ADDR_H"                    : return strap_ss_caliptra_base_addr_tb[63:32];
        "SS_MCI_BASE_ADDR_L"                      : return strap_ss_mci_base_addr_tb[31:0];
        "SS_MCI_BASE_ADDR_H"                      : return strap_ss_mci_base_addr_tb[63:32];
        "SS_RECOVERY_IFC_BASE_ADDR_L"             : return strap_ss_recovery_ifc_base_addr_tb[31:0];
        "SS_RECOVERY_IFC_BASE_ADDR_H"             : return strap_ss_recovery_ifc_base_addr_tb[63:32];
        "SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L"    : return strap_ss_external_staging_area_base_addr_tb[31:0];
        "SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H"    : return strap_ss_external_staging_area_base_addr_tb[63:32];
        "SS_OTP_FC_BASE_ADDR_L"                   : return strap_ss_otp_fc_base_addr_tb[31:0];
        "SS_OTP_FC_BASE_ADDR_H"                   : return strap_ss_otp_fc_base_addr_tb[63:32];
        "SS_UDS_SEED_BASE_ADDR_L"                 : return strap_ss_uds_seed_base_addr_tb[31:0];
        "SS_UDS_BASE_ADDR_H"                      : return strap_ss_uds_seed_base_addr_tb[63:32];                             
        "SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET" : return strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_tb;
        "SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES"        : return strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_tb;
        "SS_CPTRA_DMA_AXI_USER"                   : return strap_ss_caliptra_dma_axi_user_tb;
        "SS_DEBUG_INTENT"                         : return ss_debug_intent_tb;
        default: return '0;
      endcase
    end
    else if (str_startswith(addr_name, "CPTRA_HW_CONFIG")) begin
      if (subsystem_mode_tb == 1) begin// subsystem mode
        $display("Subsytem mode: 0x%0x", subsystem_mode_tb);
        return _soc_register_initval_ss_dict[addr_name];
      end
      else begin // passive mode
        $display("Passive mode: 0x%0x", subsystem_mode_tb);
        return _soc_register_initval_passive_dict[addr_name];
      end
    end
    else begin
      return _soc_register_initval_dict.exists(addr_name) ? _soc_register_initval_dict[addr_name] : '0; 
    end

  endfunction // get_initval


  function void set_initval(string addr_name, dword_t value); 
    if (_soc_register_initval_dict.exists(addr_name))
      $display("TB INFO. Overwriting register init value for %s with value 0x%08x", addr_name, value);
    else
      $display("TB INFO. Adding new register init value for %s with value 0x%08x", addr_name, value);
    _soc_register_initval_dict[addr_name] = value;
    
  endfunction // set_initval

  // Needs RMW of register without APB or AHB writes 
  function automatic dword_t update_CPTRA_SECURITY_STATE(logic scan_mode, logic debug_state, logic [1:0] lifecycle); 

    begin
      update_exp_regval("CPTRA_SECURITY_STATE", 
        mask_shifted(lifecycle, `SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK) |   
        mask_shifted(debug_state, `SOC_IFC_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_MASK) |   
        mask_shifted(scan_mode, `SOC_IFC_REG_CPTRA_SECURITY_STATE_SCAN_MODE_MASK),
        SET_DIRECT);          

      $display ("TB INFO. Fields for CPTRA_SECURITY_STATE changed to 0x%08x", _exp_register_data_dict["CPTRA_SECURITY_STATE"]); 
      return _exp_register_data_dict["CPTRA_SECURITY_STATE"];
    end 

  endfunction // update_CPTRA_SECURITY_STATE


  // Can update only 1 GENERIC_INPUT_WIRE bus at a time 
  function automatic dword_t update_CPTRA_GENERIC_INPUT_WIRES(logic [31:0] generic_wires, bit upper);

    begin
      if (upper) begin
        update_exp_regval("CPTRA_GENERIC_INPUT_WIRES1", generic_wires, SET_DIRECT);
        $display ("TB INFO. CPTRA_GENERIC_INPUT_WIRES1 changed to 0x%08x", _exp_register_data_dict["CPTRA_GENERIC_INPUT_WIRES1"]); 
        return _exp_register_data_dict["CPTRA_GENERIC_INPUT_WIRES1"];
      end else begin
        update_exp_regval("CPTRA_GENERIC_INPUT_WIRES0", generic_wires, SET_DIRECT);
        $display ("TB INFO. CPTRA_GENERIC_INPUT_WIRES0 changed to 0x%08x", _exp_register_data_dict["CPTRA_GENERIC_INPUT_WIRES0"]); 
        return _exp_register_data_dict["CPTRA_GENERIC_INPUT_WIRES0"];
      end
    end

  endfunction // update_CPTRA_GENERIC_INPUT_WIRES


  // Needs RMW of register without APB or AHB writes 
  function automatic logic [31:0] update_INTR_BRF_NOTIF_INTERNAL_INTR_R(logic gen_input_wire_toggle, logic debug_locked); 

    dword_t tmp_data;

    begin

      tmp_data = _exp_register_data_dict["INTR_BRF_NOTIF_INTERNAL_INTR_R"];
      // tmp_data = tmp_data & (32'hffff_ffff ^ `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK)    
      //                     & (32'hffff_ffff ^ `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK); 
      tmp_data = tmp_data | mask_shifted(debug_locked, `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK)
                          | mask_shifted(gen_input_wire_toggle, `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK);
      update_exp_regval("INTR_BRF_NOTIF_INTERNAL_INTR_R", tmp_data, SET_DIRECT);

      $display( "TB INFO. Updated expected value of INTR_BRF_NOTIF_INTERNAL_INTR_R = 0x%08x", _exp_register_data_dict["INTR_BRF_NOTIF_INTERNAL_INTR_R"]);
      return _exp_register_data_dict["INTR_BRF_NOTIF_INTERNAL_INTR_R"];
    end 

  endfunction // update_INTR_BRF_NOTIF_INTERNAL_INTR_R


  // Needs RMW of register without AXI or AHB writes 
  function automatic dword_t update_CPTRA_FLOW_STATUS(int fuse_ready_val, logic [2:0] boot_fsm_ps);

    dword_t tmp_data;

    begin
      //$display("In update_CPTRA_FLOW_STATUS");
      tmp_data = _exp_register_data_dict["CPTRA_FLOW_STATUS"]; // then preserve read-only bit fields per masks 
      $display("Read back expected CPTRA_FLOW_STATUS: 0x%x", tmp_data);
      tmp_data = tmp_data & (32'hffff_ffff ^ `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK);
      $display(tmp_data);
      tmp_data = tmp_data | mask_shifted(fuse_ready_val, `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK);
      //$display("fuse_ready_val = 0x%x, ready_for_fuses_mask = 0x%x, tmp_data = 0x%x", fuse_ready_val, `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK, tmp_data);
      tmp_data = tmp_data & (32'hffff_ffff ^ `SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK);
      //$display("boot_fsm_ps_mask = 0x%x, tmp_data = 0x%x", `SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK, tmp_data);
      tmp_data = tmp_data | mask_shifted(boot_fsm_ps, `SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK);
      //$display("boot_fsm_ps = 0x%x, boot_fsm_ps_mask = 0x%x, tmp_data = 0x%x", boot_fsm_ps, `SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK, tmp_data);
      // $display( "TB DEBUG. update_CPTRA_FLOW_STATUS(%x, %x) at time %t. new tmp_data = 0x%08x", fuse_ready_val, boot_fsm_ps, $realtime, tmp_data); 

      //$display("Final Temp_data = 0x%x", tmp_data);
      //update_exp_regval("CPTRA_FLOW_STATUS", tmp_data, SET_DIRECT); 
      update_exp_regval("CPTRA_FLOW_STATUS", tmp_data, SET_DIRECT); 

      //$display("Back to update_CPTRA_FLOW_STATUS");

      $display( "TB INFO. Updated expected value of CPTRA_FLOW_STATUS = 0x%08x", _exp_register_data_dict["CPTRA_FLOW_STATUS"]);
      //$display("Done update_CPTRA_FLOW_STATUS");
      return _exp_register_data_dict["CPTRA_FLOW_STATUS"];
    end 

  endfunction // update_CPTRA_FLOW_STATUS


  // Needs RMW of register without APB or AHB writes 
  function automatic dword_t update_CPTRA_RESET_REASON(int wrm_rst, int fw_upd);

    begin
      update_exp_regval("CPTRA_RESET_REASON", 
        mask_shifted(wrm_rst, `SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK) | 
        mask_shifted(fw_upd, `SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK), 
        SET_DIRECT);

      $display ("TB INFO. Fields for CPTRA_RESET_REASON changed to 0x%08x", _exp_register_data_dict["CPTRA_RESET_REASON"]); 
      return _exp_register_data_dict["CPTRA_RESET_REASON"];
    end 

  endfunction // update_CPTRA_RESET_REASON

  function automatic dword_t update_CPTRA_HW_CONFIG();
    
    dword_t exp_cptra_hw_config;

    begin
      exp_cptra_hw_config = get_initval("CPTRA_HW_CONFIG");
      update_exp_regval("CPTRA_HW_CONFIG", exp_cptra_hw_config, SET_DIRECT);
      $display("TB INFO. Updated expected value of CPTRA_HW_CONFIG = 0x%0x", _exp_register_data_dict["CPTRA_HW_CONFIG"]);
    end

  endfunction // update_CPTRA_HW_CONFIG


  function void update_exp_regval(string addr_name, dword_t indata, access_t modify, string pfx="DEFAULT");
    // "expected" model of register. Read-modify-write model 
   
    word_addr_t addr; 
    dword_t curr_data, exp_data;
    dword_t ahb_indata, axi_indata, axi_rodata, ahb_rodata;

    string tmpstr; 
    string axi_user_suffix; 
    string axi_user_lock_regname; 
    int axi_user_locked, owner_pk_hash_locked, fuses_locked, lock_mask, iccm_locked, cap_locked; 
    string mask_name; 

    dword_t sscode;
    dword_t tmp_data;
    dword_t mask;
    dword_t ss_debug_intent;


    begin

      //$display("In update_exp_regval: %s", addr_name);

      addr = _soc_register_dict[addr_name];
      sscode = _soc_register_initval_dict["CPTRA_SECURITY_STATE"];

      if (modify == COLD_RESET) begin
        reset_exp_data();
        return;
      end

      if (modify == WARM_RESET) begin
        warm_reset_exp_data();
        return;
      end

      if (!_imap_soc_register_dict.exists(addr)) begin
        $display ("TB ERROR.  Address 0x%08x not found in inverse address map!", addr);
        return;
      end

      // With direct modification responsibility is on caller to ensure mask fields are respected!!  
      if (modify == SET_DIRECT) begin
        _exp_register_data_dict[addr_name] = indata;
        if ((addr_name == "INTERNAL_FW_UPDATE_RESET") &  (indata[0] == 1'b1)) begin
            // NOTE. The expected value of  INTERNAL_ICCM_LOCK must be updated outside of package, or at least outside of 
            //       a function call since there could be a significant delay 
            // _exp_register_data_dict["INTERNAL_ICCM_LOCK"] = '0;  
            // $display ("TB INFO: Cross modification - Writing '1' to INTERNAL_FW_UPDATE_RESET also reset INTERNAL_ICCM_LOCK"); 

            tmp_data = _exp_register_data_dict["CPTRA_RESET_REASON"]; 
            tmp_data = tmp_data & (32'hffff_ffff ^ `SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK)  |
                        tmp_data & mask_shifted(1'b1, `SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK); 
            $display ("TB INFO: Cross modification - Writing '1' to INTERNAL_FW_UPDATE_RESET also sets CPTRA_RESET_REASON"); 
        end
        return;
      end 


      fuses_locked = _fuses_locked; 

      curr_data = _exp_register_data_dict[addr_name];

      axi_indata = indata & {32{(modify == SET_AXI)}}; // axi_mutable;
      ahb_indata = indata & {32{(modify == SET_AHB)}}; // ahb_mutable;

      axi_rodata = curr_data & {32{(modify == SET_AXI)}}; // axi_readonly;
      ahb_rodata = curr_data & {32{(modify == SET_AHB)}}; // ahb_readonly;

      //$display("axi_indata = 0x%x", axi_indata);
      //$display("ahb_rodata = 0x%x", ahb_rodata);
      //$display("curr_data = 0x%x", curr_data);

      // handle wide registers first, then normal sized ones

      if (str_startswith(addr_name, "CPTRA_TRNG_DATA"))
        exp_data = ahb_rodata | axi_indata;  // ahb-RO

      else if (str_startswith(addr_name, "CPTRA_FW_REV_ID")) begin
        exp_data = ahb_indata | axi_rodata; // apb-RO
        // $display( "TB DEBUG. CPTRA_FW_REV_ID: addr %-30s, exp_data 0x%08x", addr_name, exp_data); 
      
      end else if ((str_startswith(addr_name, "FUSE_UDS_SEED")) || (str_startswith(addr_name, "FUSE_FIELD_ENTROPY")))
        exp_data = '0; // not accessible over APB or AHB 

      else if (addr_name == "FUSE_SOC_STEPPING_ID") begin // Normal fuse register operation + cross modification of register
        exp_data = fuses_locked ? curr_data : (ahb_rodata | axi_indata & get_mask(addr_name)); // ahb-RO 
        $display ("TB INFO: Cross modification - Updating FUSE_SOC_STEPPING_ID also updates CPTRA_HW_REV_ID"); 

        tmp_data = _exp_register_data_dict["CPTRA_HW_REV_ID"] & 
                    mask_shifted(16'hffff, `SOC_IFC_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_MASK); // pick out cptra_generation 
        _exp_register_data_dict["CPTRA_HW_REV_ID"] = 
                    mask_shifted(tmp_data, `SOC_IFC_REG_CPTRA_HW_REV_ID_CPTRA_GENERATION_MASK) |  // add back cptra_generation 
                    mask_shifted(exp_data, `SOC_IFC_REG_CPTRA_HW_REV_ID_SOC_STEPPING_ID_MASK);    // and new stepping_id 

      end else if (str_startswith(addr_name, "FUSE_"))
        exp_data = fuses_locked ? curr_data : (ahb_rodata | axi_indata & get_mask(addr_name)); // ahb-RO 

      else if (str_startswith(addr_name, "CPTRA_MBOX_VALID_AXI_USER")) begin    // find equivalent pauser lock & if set, apb-RO 
        tmpstr = "CPTRA_MBOX_VALID_AXI_USER";
        axi_user_suffix = addr_name.substr(tmpstr.len(), addr_name.len()-1);
        axi_user_lock_regname = {"CPTRA_MBOX_AXI_USER_LOCK", axi_user_suffix};
        axi_user_locked = _exp_register_data_dict[axi_user_lock_regname]; 
        exp_data = axi_user_locked ? curr_data : (ahb_indata | axi_indata); 
        //$display("DEBUG: addr_name: %s\naxi_user_lock_regname: %s\naxi_user_locked: 0x%x\nexp_data: 0x%x", addr_name, axi_user_lock_regname, axi_user_locked, exp_data);

      end else if (str_startswith(addr_name, "CPTRA_MBOX_AXI_USER_LOCK")) begin //  if axi_user locked, axi-RO
        tmpstr = "CPTRA_MBOX_AXI_USER_LOCK";
        axi_user_locked = _exp_register_data_dict[addr_name];
        exp_data = axi_user_locked ? curr_data & get_mask(tmpstr) :  (ahb_indata | axi_indata) & get_mask(tmpstr); 
        //$display("DEBUG: addr_name: %s\naxi_user_locked: 0x%x\nexp_data: 0x%x", addr_name, axi_user_locked, exp_data);

      end else if (str_startswith(addr_name, "CPTRA_GENERIC_INPUT_WIRES")) 
        exp_data = curr_data; // all bits are RO 

      else if (str_startswith(addr_name, "CPTRA_GENERIC_OUTPUT_WIRES"))  
        exp_data = ahb_indata | axi_rodata; // all bits are axi-RO 

      else if (str_startswith(addr_name, "CPTRA_HW_CONFIG"))
        exp_data = curr_data & get_mask("CPTRA_HW_CONFIG"); // all bits are RO 

      else if (str_startswith(addr_name, "CPTRA_WDT_TIMER1_TIMEOUT_PERIOD") ||           
               str_startswith(addr_name, "CPTRA_WDT_TIMER2_TIMEOUT_PERIOD")) 
        exp_data = ahb_indata | axi_rodata; 

      else if (str_startswith(addr_name, "CPTRA_OWNER_PK_HASH") & !str_endswith(addr_name, "LOCK")) begin
        owner_pk_hash_locked = _exp_register_data_dict["CPTRA_OWNER_PK_HASH_LOCK"];
        exp_data = owner_pk_hash_locked ? curr_data : (axi_indata | ahb_rodata); // all bits are ahb-RO
      end

      else if (str_startswith(addr_name, "INTERNAL_OBF_KEY"))            
        exp_data = '0;  // not accessible over AXI or AHB 

      else if (str_startswith(addr_name, "SHA_ACC_INTR_BRF"))
        if (str_endswith(addr_name, "INCR_R"))
          exp_data = ahb_rodata | axi_rodata; 
        else if ((addr_name == "SHA_ACC_INTR_BRF_ERROR_GLOBAL_INTR_R") || (addr_name == "SHA_ACC_INTR_BRF_NOTIF_GLOBAL_INTR_R"))
          exp_data = ahb_rodata | axi_rodata; 
        else
          exp_data = ahb_indata & get_mask(addr_name) | axi_rodata; 

      else if (str_startswith(addr_name, "INTR_BRF_")) begin // Interrupt block has its own sub-cases

        if (is_pulsed_reg(addr_name)) begin
          exp_data = '0;
          
        end else begin
          case (addr_name)

            "INTR_BRF_ERROR_GLOBAL_INTR_R":exp_data = ahb_rodata | axi_rodata; // set by HW  
            "INTR_BRF_NOTIF_GLOBAL_INTR_R":exp_data = ahb_rodata | axi_rodata; // set by HW  
            "INTR_BRF_ERROR_INTR_TRIG_R": exp_data = ((ahb_indata & get_mask(addr_name)) != 0) ? '0: axi_rodata; // TODO. Pulsed reg 
            "INTR_BRF_NOTIF_INTR_TRIG_R": exp_data = ((ahb_indata & get_mask(addr_name)) != 0) ? '0: axi_rodata; // TODO. Pulsed reg 
            "INTR_BRF_ERROR_INTERNAL_INTR_R": exp_data = axi_rodata | (~(ahb_indata & get_mask(addr_name)) & curr_data);
            "INTR_BRF_NOTIF_INTERNAL_INTR_R": exp_data = axi_rodata | (~(ahb_indata & get_mask(addr_name)) & curr_data);

            default: exp_data = ahb_indata & get_mask(addr_name) | axi_rodata;

          endcase

        end

      end  else if (str_startswith(addr_name, "SS_GENERIC_FW_EXEC_CTRL")) begin
        exp_data = axi_rodata | ahb_indata;

      end else if (str_startswith(addr_name, "SS_STRAP_GENERIC")) begin // all bits are AHB-RO
        exp_data = fuses_locked ? curr_data : axi_indata;

      end  else if (str_startswith(addr_name, "SS_SOC_DBG_UNLOCK_LEVEL")) begin
        ss_debug_intent = _exp_register_data_dict["SS_DEBUG_INTENT"];
        exp_data = ss_debug_intent ? (ahb_indata | axi_rodata) : curr_data;

      end else if (str_startswith(addr_name, "SS_DBG_SERVICE_REG_RSP")) begin
        $display("pfx = %s", pfx);
        if (pfx.compare("DEFAULT") != 0)
          mask_name = {addr_name, pfx};
        else
          mask_name = addr_name;
        //$display("name_name = %s", mask_name);
        addr_name = "SS_DBG_SERVICE_REG_RSP";
        ss_debug_intent = _exp_register_data_dict["SS_DEBUG_INTENT"];
        //$display("In update_exp_regval, mask = 0x%08x", get_mask(mask_name));
        exp_data = ss_debug_intent ? ahb_indata & get_mask(mask_name) : curr_data;
        $display("exp_data = 0x%x", exp_data);

      end else begin    
        //$display("COntrol is in this block");
        
        case (addr_name)
    
          "CPTRA_HW_ERROR_FATAL", "CPTRA_HW_ERROR_NON_FATAL": begin
            exp_data = ahb_indata | axi_indata;  
            exp_data = '0; // write-one to clear -- effectively always 0
          end

          "CPTRA_FLOW_STATUS" : begin
            //$display("DEBUG: here");
            if (modify == SET_AXI) //  apb-RO 
              exp_data = axi_rodata;
            else if (modify == SET_AHB) begin // some fields are ro
              mask = get_mask(addr_name);
              exp_data = (mask & ahb_indata) | (~mask & curr_data); 
              // $display ("TB DEBUG: for CPTRA_FLOW_STATUS ahb_indata = 0x%08x, curr_data = 0x%08x, exp_data = 0x%08x", 
              //   ahb_indata, curr_data, exp_data); 
            end
          end

          "CPTRA_RESET_REASON"                       : exp_data = ahb_rodata | axi_rodata; //  bit 1:0 is RO 
          "CPTRA_SECURITY_STATE"                     : exp_data = curr_data & get_mask(addr_name); // & sscode;  //  bit 3:0 is RO 

          "CPTRA_TRNG_VALID_AXI_USER" : begin // find equivalent pauser lock & if set, apb-RO 
            axi_user_locked = _exp_register_data_dict["CPTRA_TRNG_AXI_USER_LOCK"]; 
            exp_data = axi_user_locked ? curr_data : (ahb_indata | axi_indata); 
          end

          "CPTRA_TRNG_AXI_USER_LOCK": begin
            lock_mask = get_mask(addr_name); 
            axi_user_locked = curr_data & get_mask(addr_name); // TODO. TRNG registers may need exclusion 
            exp_data = axi_user_locked ? curr_data & lock_mask :  (ahb_indata | axi_indata) & lock_mask;  
          end

          "CPTRA_TRNG_CTRL"                          : exp_data = axi_rodata; // pulsed w/ahb 

          "CPTRA_TRNG_STATUS": begin                                        //                   WR_DONE        REQ
            dword_t ahb_mask = get_mask("CPTRA_TRNG_STATUS.AHB"); 
            dword_t apb_mask = get_mask("CPTRA_TRNG_STATUS.APB"); 
            exp_data = (ahb_rodata & ~ahb_mask | ahb_indata & ahb_mask) |   // Caliptra Access:       RO         RW 
                       (axi_rodata & ~apb_mask | axi_indata & apb_mask) ;   // SOC Access:            RW         RO
          end

          "CPTRA_HW_REV_ID"                          : exp_data = curr_data;  
          "CPTRA_WDT_TIMER1_EN"                      : exp_data = ahb_indata & get_mask(addr_name) | axi_rodata;
          "CPTRA_WDT_TIMER1_CTRL"                    : exp_data = ((ahb_indata & get_mask(addr_name)) != 0) ? '0: axi_rodata; // TODO. Pulsed reg
          "CPTRA_WDT_TIMER2_EN"                      : exp_data = ahb_indata & get_mask(addr_name) | axi_rodata;
          "CPTRA_WDT_TIMER2_CTRL"                    : exp_data = ((ahb_indata & get_mask(addr_name)) != 0) ? '0: axi_rodata; // TODO. Pulsed reg 
          "CPTRA_WDT_STATUS"                         : exp_data = curr_data; 
          "CPTRA_FUSE_WR_DONE"                       : begin 
            $display("Found CPTRA_FUSE_WR_DONE");
            exp_data = fuses_locked ? curr_data : (ahb_rodata | axi_indata & get_mask(addr_name)); 
          end
          "CPTRA_BOOTFSM_GO"                         : exp_data = ahb_rodata | axi_indata & get_mask(addr_name) ; 
          "CPTRA_DBG_MANUF_SERVICE_REG"              : exp_data = ahb_indata | axi_indata;
          "CPTRA_BOOT_STATUS"                        : exp_data = ahb_indata | axi_rodata; 
          "CPTRA_CLK_GATING_EN"                      : exp_data = ahb_rodata | axi_indata & get_mask(addr_name) ; 

          "CPTRA_FUSE_VALID_AXI_USER" : begin // find equivalent pauser lock & if set, apb-RO 
            axi_user_locked = _exp_register_data_dict["CPTRA_FUSE_AXI_USER_LOCK"]; 
            exp_data = axi_user_locked ? curr_data : (ahb_indata | axi_indata); 
          end

          "CPTRA_FUSE_AXI_USER_LOCK": begin
            lock_mask = get_mask(addr_name); 
            axi_user_locked = curr_data & get_mask(addr_name); 
            exp_data = axi_user_locked ? curr_data & lock_mask :  (ahb_indata | axi_indata) & lock_mask;  
          end 

          "CPTRA_OWNER_PK_HASH_LOCK": begin
            owner_pk_hash_locked = _exp_register_data_dict["CPTRA_OWNER_PK_HASH_LOCK"];
            exp_data = owner_pk_hash_locked ? curr_data : ahb_rodata | (axi_indata & get_mask(addr_name));
            $display("Expected data: 0x%x", exp_data);
          end

          "CPTRA_CAP_LOCK": begin
            exp_data = ahb_indata & get_mask(addr_name) | axi_rodata;
          end

          "CPTRA_HW_CAPABILITIES": begin
            cap_locked = _exp_register_data_dict["CPTRA_CAP_LOCK"];
            $display("CPTRA_CAP_LOCK = 0x%08x", cap_locked);
            exp_data = cap_locked ? curr_data : (ahb_indata | axi_rodata);
          end

          "CPTRA_FW_CAPABILITIES": begin
            cap_locked = _exp_register_data_dict["CPTRA_CAP_LOCK"];
            $display("CPTRA_CAP_LOCK = 0x%08x", cap_locked);
            exp_data = cap_locked ? curr_data : (ahb_indata | axi_rodata);
          end

          "INTERNAL_ICCM_LOCK"                              : begin
            iccm_locked = curr_data & get_mask(addr_name); 
            exp_data = iccm_locked ? curr_data : (ahb_indata & get_mask(addr_name) | axi_rodata); 
          end 

          "INTERNAL_FW_UPDATE_RESET"                        : begin
            exp_data = ahb_indata & get_mask(addr_name) | axi_rodata; 

            // $display ("TB DEBUG: ahb_indata = 0x%x and exp_data for INTERNAL_FW_UPDATE_RESET = 0x%x", ahb_indata, exp_data); 
            if (exp_data[0]) begin  // write-one to clear
            // NOTE. The expected value of  INTERNAL_ICCM_LOCK must be updated outside of package, or at least outside of 
            //       a function call since there could be a significant delay
            //  _exp_register_data_dict["INTERNAL_ICCM_LOCK"] = '0;  
            //  $display ("TB INFO: Cross modification - Writing '1' to INTERNAL_FW_UPDATE_RESET also reset INTERNAL_ICCM_LOCK"); 

              _exp_register_data_dict["CPTRA_RESET_REASON"] = 32'h1;  //TODO. Ignoring warm reset for now 
              $display ("-- CPTRA_RESET_REASON is now %d", _exp_register_data_dict["CPTRA_RESET_REASON"]); 
              $display ("TB INFO: Cross modification - Writing '1' to INTERNAL_FW_UPDATE_RESET also sets CPTRA_RESET_REASON"); 
            end
          end

          "INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES"     : exp_data = ahb_indata & get_mask(addr_name) | axi_rodata;  
          "INTERNAL_NMI_VECTOR"                      : exp_data = ahb_indata | axi_rodata;  
          "INTERNAL_HW_ERROR_FATAL_MASK"             : exp_data = ahb_indata & get_mask(addr_name) | axi_rodata;  
          "INTERNAL_HW_ERROR_NON_FATAL_MASK"         : exp_data = ahb_indata & get_mask(addr_name) | axi_rodata;  
          "INTERNAL_FW_ERROR_FATAL_MASK"             : exp_data = ahb_indata | axi_rodata;  
          "INTERNAL_FW_ERROR_NON_FATAL_MASK"         : exp_data = ahb_indata | axi_rodata;  
          "INTERNAL_RV_MTIME_L"                      : exp_data = ahb_indata | axi_rodata;
          "INTERNAL_RV_MTIME_H"                      : exp_data = ahb_indata | axi_rodata;
          "INTERNAL_RV_MTIMECMP_L"                   : exp_data = ahb_indata | axi_rodata;
          "INTERNAL_RV_MTIMECMP_H"                   : exp_data = ahb_indata | axi_rodata;

          "SS_CPTRA_BASE_ADDR_L"                          : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_CPTRA_BASE_ADDR_H"                          : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_MCI_BASE_ADDR_L"                            : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_MCI_BASE_ADDR_H"                            : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_RECOVERY_IFC_BASE_ADDR_L"                   : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_RECOVERY_IFC_BASE_ADDR_H"                   : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L"          : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H"          : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_OTP_FC_BASE_ADDR_L"                         : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_OTP_FC_BASE_ADDR_H"                         : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_UDS_SEED_BASE_ADDR_L"                       : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_UDS_BASE_ADDR_H"                            : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET" : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES"    : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_DEBUG_INTENT"                               : exp_data = fuses_locked ? curr_data : axi_indata;
          "SS_CPTRA_DMA_AXI_USER"                         : exp_data = fuses_locked ? curr_data : axi_indata;
          
          "SS_DBG_SERVICE_REG_REQ"                  : begin
            ss_debug_intent = _exp_register_data_dict["SS_DEBUG_INTENT"];
            //$display("ss_debug_intent = 0x%08x", ss_debug_intent);
            //$display("axi_indata = 0x%08x", axi_indata);
            //$display("ahb_indata = 0x%08x", axi_indata);
            //$display("mask = 0x%08x", get_mask(addr_name));
            //$display("curr_data = 0x%08x", curr_data);
            exp_data = ss_debug_intent ? axi_indata & get_mask(addr_name) | ahb_indata & get_mask(addr_name) : curr_data;
          end
          
          //"SS_DBG_SERVICE_REG_RSP_PROD_UNLOCK"                  : begin
          //  tmpstr = "SS_DBG_SERVICE_REG_RSP";
          //  ss_debug_intent = _exp_register_data_dict["SS_DEBUG_INTENT"];
          //  exp_data = ss_debug_intent ? ahb_indata & get_mask(addr_name) : curr_data;
          //end
          
          default: begin
            //$display("DEBUG: Default: %s", addr_name);
            exp_data = indata & get_mask(addr_name); 
          end
        endcase

      end 
      _exp_register_data_dict[addr_name] = exp_data;
       //$display ("TB DEBUG: Expected data for addr_name %s (addr 0x%08x) = 0x%08x", addr_name, addr, exp_data); 
    end
    //$display("Done update_exp_regval: %s", addr_name);

  endfunction // update_exp_regval


  function automatic strq_t get_soc_regnames();

    strq_t soc_regs; 

    foreach (_soc_register_dict[rkey]) begin
      soc_regs.push_back(rkey); 
    end

    return soc_regs;

  endfunction // get_soc_regnames


  function automatic strq_t get_fuse_regnames();

    strq_t fuse_regs; 

    foreach (_soc_register_dict[rkey]) begin
      if (rkey.substr(0,3) == "FUSE")
        fuse_regs.push_back(rkey); 
      // SS_* registers are straps that get their initial values from 
      // input wires to soc_ifc and can be written until CPTRA_FUSE_WR_DONE 
      // is set. After, they are locked for writes similar to fuses.
      else if (rkey.substr(0,1) == "SS")
        fuse_regs.push_back(rkey);
    end 

    return fuse_regs;

  endfunction // get_fuse_regnames

  function automatic strq_t get_fuse_regnames_minus_ss_straps();

    strq_t fuse_regs; 

    foreach (_soc_register_dict[rkey]) begin
      if (rkey.substr(0,3) == "FUSE")
        fuse_regs.push_back(rkey); 
    end 

    return fuse_regs;

  endfunction // get_fuse_regnames_minus_ss_straps

  function automatic strq_t get_ss_strap_regnames();

    strq_t ss_strap_regs; 

    foreach (_soc_register_dict[rkey]) begin
      // SS_* registers are straps that get their initial values from 
      // input wires to soc_ifc and can be written until CPTRA_FUSE_WR_DONE 
      // is set. After, they are locked for writes similar to fuses.
      if (rkey.substr(0,1) == "SS")
        ss_strap_regs.push_back(rkey); 
      
    end 

    return ss_strap_regs;

  endfunction // get_ss_strap_regnames


  function automatic strq_t get_intrblk_regnames();

    strq_t intr_regs; 

    foreach (_soc_register_dict[rkey]) begin
      if (str_startswith(rkey, "INTR_BRF"))
        intr_regs.push_back(rkey); 
    end 

    return intr_regs;

  endfunction // get_intrblk_regnames


  function automatic strq_t get_sha_acc_intrblk_regnames();

    strq_t sha_intr_regs; 

    foreach (_soc_register_dict[rkey]) begin
      if (str_startswith(rkey, "SHA_ACC_INTR_BRF"))
        sha_intr_regs.push_back(rkey); 
    end 

    return sha_intr_regs;

  endfunction // get_intrblk_regnames


  function automatic strq_t get_intrblk_regnames_minus_incr();

    strq_t intr_regs; 

    foreach (_soc_register_dict[rkey]) begin
      if (str_startswith(rkey, "INTR_BRF") && !str_endswith(rkey, "INCR_R"))
        intr_regs.push_back(rkey); 
    end 

    return intr_regs;

  endfunction // get_intrblk_regnames_minus_incr


  function automatic strq_t get_soc_regnames_minus_fuse();

    strq_t soc_regs; 

    foreach (_soc_register_dict[rkey]) begin
      if ((rkey.substr(0,3) != "FUSE") || (rkey.substr(0,1) != "SS"))
        soc_regs.push_back(rkey); 
    end 

    return soc_regs;

  endfunction // get_soc_regnames_minus_fuse


  function automatic strq_t get_soc_regnames_minus_intr();

    strq_t soc_regs; 

    foreach (_soc_register_dict[rkey]) begin
      if (rkey.substr(0,7) != "INTR_BRF") 
        soc_regs.push_back(rkey); 
    end 

    return soc_regs;

  endfunction // get_soc_regnames_minus_intr


  function automatic strq_t get_soc_regnames_minus_fuse_intr();

    strq_t soc_regs; 

    foreach (_soc_register_dict[rkey]) begin
      if (str_startswith(rkey, "INTR_BRF") || 
          str_startswith(rkey, "SHA_ACC_INTR_BRF") || 
          str_startswith(rkey, "FUSE") ||
          str_startswith(rkey, "SS")) 
          continue;
      soc_regs.push_back(rkey); 
    end 

    return soc_regs;

  endfunction // get_soc_regnames_minus_fuse_intr


  function automatic word_addrq_t get_undef_regs();
   // Just flattens and expands the extent ranges into a single queue 

    word_addrq_t undef_addrs; 
    word_addr_t addr; 
    word_addr_t addr_min, addr_max; 
    int i;

    for (i = 0; i < _undefined_addr_ranges.size(); i++) begin 

        addr_min = _undefined_addr_ranges[i].addr_min; 
        addr_max = _undefined_addr_ranges[i].addr_max;
        addr = addr_min;
        while (addr <= addr_max) begin
            // $display ("Adding to undefined registers list 0x%x", addr);
            undef_addrs.push_back(addr); 
            addr += 32'h4;
        end
    end  

    return undef_addrs;

  endfunction  // get_undef_regs
        

  function automatic void reset_exp_data();
    // this peforms update for power-on reset

    begin
      $display ("** Clearing all expected reg values for cold reset **");
      foreach (_soc_register_dict[rname]) begin
        _exp_register_data_dict[rname] = get_initval(rname); 
        $display("TB DEBUG: Init value for %s: 0x%x", rname, _exp_register_data_dict[rname]);
      end
    end
  endfunction // reset_exp_data


  function automatic void warm_reset_exp_data();
    // Unlike reset_exp_data which assumes cold boot, this preserves sticky bits 

    int wrmrst_pfx_match = 0;
    string sticky_rname;
    
    begin
      $display ("** Updating expected reg values for warm reset **");

      foreach (_soc_register_dict[rname]) begin
        wrmrst_pfx_match = 0;

        foreach (_sticky_register_prefix_dict[sticky_rname]) begin
          if (str_startswith(rname, sticky_rname) && !str_contains(rname, "SS_GENERIC_FW_EXEC_CTRL")) begin
            wrmrst_pfx_match = 1;
            //$display("Current reg: %s", rname);
            //$display("Expected before update: 0x%0x", _exp_register_data_dict[rname]);
            _exp_register_data_dict[rname] = _exp_register_data_dict[rname] & _sticky_register_prefix_dict[sticky_rname];
             $display("TB INFO. Assigning sticky value _exp_register_data_dict[%-30s] = 0x%08x", rname, _exp_register_data_dict[rname]); 
            break;
          end
        end

        if (!wrmrst_pfx_match) begin
          _exp_register_data_dict[rname] = get_initval(rname);
           //$display("assigning init value   _exp_register_data_dict[%-30s] = 0x%08x", rname, _exp_register_data_dict[rname]); 
        end
      end
      $display ("** Done updating expected reg values for warm reset **");
    end 

  endfunction // warm_reset_exp_data();


  function automatic int is_pulsed_reg(string rname);

    string tmplist [$];

    begin
      tmplist = _pulsed_regnames.find_first with (item == rname);
      return (tmplist.size() > 0);
    end 

  endfunction // is_pulsed_reg


  // ---------------------------------------------------------------------------
  // -- Generic Utility functions that have less to do with custom data types
  // ---------------------------------------------------------------------------
  function automatic logic str_startswith(string s1, string s2);

    return(s2 == s1.substr(0, s2.len() - 1));

  endfunction  // str_startswith


  function automatic int str_endswith(string s1, string s2);

    int s1_eix = s1.len() - 1;  
    int s2_eix = s2.len() - 1;  

    return (s2 == s1.substr(s1_eix - s2_eix, s1_eix));

  endfunction  // str_endswith

  function automatic int str_contains(string s1, string s2); 
    
    int s1_len = s1.len();
    int s2_len = s2.len();

    $display(s1);
    $display(s2);

    for (int i = 0; i <= s1_len - s2_len; i++) begin
      string sub = s1.substr(i, s2_len-1);
      //$display("Checking substring: %s", sub);

      if (sub == s2) begin
          //$display("Substring found");
          return 1; // Substring found
      end
    end
    //$display("Substring NOT found");
    return 0; // Substring not found

  endfunction // str_contains


  function automatic del_from_strq(inout strq_t mutable_strq, input string name);  
  // NOTE. This function works ONLY for a single name that matches one-index

    int iq [$];
    int j;

    iq = mutable_strq.find_index with (item == name); 
    j = iq[0];
    
    mutable_strq.delete(j);

  endfunction // del_from_strq


  function automatic delm_from_strq(inout strq_t mutable_strq, input string pfx);  
  // NOTE. This function works by deleting multiple names with matching prefix

    strq_t filtq;

    foreach(mutable_strq[i])  begin
      if (str_startswith(mutable_strq[i], pfx))
        continue;
      filtq.push_back(mutable_strq[i]);
    end

    mutable_strq = {}; 
    mutable_strq = filtq;

  endfunction // delm_from_strq

  function automatic add_to_strq(inout strq_t mutable_strq, input string name); 
  // NOTE: This function works ONLY for a single name that will be stored in one index

    mutable_strq.push_back(name);

  endfunction

  function automatic dword_t mask_shifted(dword_t v, dword_t n);

    /* Shift 'v' by number of bits that mask 'n' has zeros on right. Example:
        v (bin):                                         1001 (0x9)       value to move 
        n (bin):      0000_0000_0001_1110_0000_0000_0000_0000 (0x1e0000)  4-bit mask 
        Return (bin): 0000_0000_0001_0010_0000_0000_0000_0000 (0x120000)  moved to mask position 
    */

    return v << count_trailing_zeros(n);
  endfunction // mask_shifted


  function automatic int count_trailing_zeros(dword_t n);

    int k = 0;
    dword_t nshift = n;

      if (n == 0)  
          return 32; 

      while (k < 32) begin
        if (n[k] == 1'b1)
          break; 
        k += 1;
      end
      return k;

  endfunction // count_trailing_zeros


  function automatic void print_banner(string txtstr, string s = "-");

      int L = txtstr.len(); 
      $display({L{s}}); 
      $display(txtstr); 
      $display({L{s}});

  endfunction // print_banner

  // ================================================================================ 
  // Class definitions 
  // ================================================================================ 

  // -------------------------------------------------------------------------------- 
  class WordTransaction;
  // -------------------------------------------------------------------------------- 

    word_addr_t    addr; 
    rand dword_t   data;
    int            tid;    

    extern function void update(word_addr_t addr, dword_t data, int tid);    
    extern function void update_byname(string addr_name, dword_t data, int tid);    
    extern function void update_tid(int tid);    
    extern function void update_data(dword_t data);
    extern function void display(); 
    extern function void copy_from(WordTransaction atrans); 

  endclass // WordTransaction


  function void WordTransaction::update(word_addr_t addr, dword_t data, int tid);    

    this.addr = addr;
    this.data = data;
    this.tid = tid;    

  endfunction 

  
  function void WordTransaction::update_byname(string addr_name, dword_t data, int tid);    

    word_addr_t addr;

    this.addr = _soc_register_dict[addr_name];  
    this.data = data;
    this.tid = tid;    

  endfunction 


  function void WordTransaction::update_tid(int tid);    

    this.tid = tid; 

  endfunction 


  function void WordTransaction::update_data(dword_t data);

    this.data = data; 

  endfunction 


  function void WordTransaction::display(); 

    $display("Addr: 0x%08x, Data: 0x%08x, TID: %03d", addr, data, tid); 

  endfunction

  
  function void WordTransaction::copy_from(WordTransaction atrans); 

    this.update(atrans.addr, atrans.data, atrans.tid);    

  endfunction 

  
  // -------------------------------------------------------------------------------- 
  class SocRegisters;
  // -------------------------------------------------------------------------------- 
    
    // once these static vars have been set, assoicated modifier functions should have no effect
    static int widereg_expanded = 0; 
    static int imap_built = 0; 
    // static int fuses_locked = 0; 
    static string security_state_name = "UNDEFINED2"; 
    static int undef_addr_built = 0; 

    extern function new();
    extern function lock_fuses();
    extern function unlock_fuses();
    extern function void build_inverse_addr_map();
    extern function void init_regs();
    extern function word_addr_t get_addr(string name);
    extern function string get_name(word_addr_t addr);
    extern function void update_security_state(string ssname);
    extern function void display_exp_regs();      
    extern function dword_t get_exp_regval(string rname);      

  endclass // SocRegisters


  function SocRegisters::new();
    if (!widereg_expanded) begin
      init_regs();
      widereg_expanded = 1;
    end

    if (!imap_built) begin
      build_inverse_addr_map();
      imap_built = 1;
    end 

    reset_exp_data();
 
  endfunction  // new 


  function SocRegisters::lock_fuses();
    // assume over APB or some other means. NOTE that CPTRA_FUSE_WR_DONE 
    // may be set from 1 to 0, which will have no effect on this variable. 
    
    _fuses_locked = 1;  // set this global var for now 

  endfunction  // lock_fuses 


  function SocRegisters::unlock_fuses();
    // unset global var; done over cold boot, warm reset or mailbox command  

    _fuses_locked = 0; 

  endfunction  // unlock_fuses 
 

  function void SocRegisters::build_inverse_addr_map();

    if (imap_built) 
      return;

    foreach (_soc_register_dict[tmpstr]) 
      _imap_soc_register_dict[_soc_register_dict[tmpstr]] = tmpstr;   

  endfunction  // build_inverse_addr_map


  function void SocRegisters::init_regs();
    // The default _soc_register_dict only has root addr name-value mappings for 
    // simple 32-bit registers. Wider registers implemented as array need to be 
    // populated w/a function

    word_addr_t start_addr;
    int i;
    string istr;
    dword_t initval;

    if (widereg_expanded) 
      return;

    foreach (_wide_register_dict[rname]) begin 
      if (_soc_register_dict.exists(rname)) begin 
        start_addr = _soc_register_dict[rname];
        for (i = 0; i < _wide_register_dict[rname]; i++) begin
          istr.itoa(i);
          _soc_register_dict[{rname, istr}] = start_addr + 4*i; 
        end
        _soc_register_dict.delete(rname);
      end else 
        $display ("TB ERROR. Soc register and wide register data structures incomplete!");
    end 

    // The same is done for 'reset' values of registers 
    // Names that don't exist in _soc_register_initval_dict assume "0" values
    foreach (_wide_register_dict[rname]) begin 
      if (_soc_register_initval_dict.exists(rname)) begin 
        initval = _soc_register_initval_dict[rname];
        for (i = 0; i < _wide_register_dict[rname]; i++) begin
          istr.itoa(i);
          _soc_register_initval_dict[{rname, istr}] = initval;
        end
        _soc_register_initval_dict.delete(rname);
      end
    end

    // foreach (_soc_register_initval_dict[rname]) 
    //   $display ("-- INIT VAL %30s <= 0x%08x", rname, _soc_register_initval_dict[rname]);

  endfunction  // init_regs


  function word_addr_t SocRegisters::get_addr(string name);

    if (_soc_register_dict.exists(name)) begin
      $display("Address [%s] = 0x%x", name, _soc_register_dict[name]);
      return _soc_register_dict[name];
    end else begin
      $display("TB WARNING. Address %s not found in reg name->addr map. Returning 0", name); 
      return '0; 
    end

  endfunction // get_addr


  function string SocRegisters::get_name(word_addr_t addr);

    if (_imap_soc_register_dict.exists(addr))
      return _imap_soc_register_dict[addr];
    else begin
      $display("TB WARNING. Address 0x%08x not found in reg addr->name map. Returning empty str", addr); 
      return ""; 
    end

  endfunction // get_name


  function void SocRegisters::update_security_state(string ssname);

    security_state_name = ssname; 

  endfunction // update_security_state


  function void SocRegisters::display_exp_regs();      

    $display ("\n\n-- Current state of expected register values --\n");
    foreach (_exp_register_data_dict[rname]) begin
      $display (" -- expected value of addr %-40s (0x%08x) = 0x%08x", 
        rname, get_addr(rname), _exp_register_data_dict[rname]);
    end
    $display (" ---------------------------------------------\n "); 

  endfunction // display_exp_regs


  function dword_t SocRegisters::get_exp_regval(string rname);      

    // $display (" -- expected value of addr %-40s (0x%08x) = 0x%08x", 
    //   rname, get_addr(rname), _exp_register_data_dict[rname]);
    return _exp_register_data_dict[rname];
  endfunction // get_exp_regval


  // -------------------------------------------------------------------------------- 
  class RegScoreboard;
  // -------------------------------------------------------------------------------- 

    int err_count;
    transq_t addr_table [word_addr_t];      // store a queue of transactions for each address

    extern function new();
    extern function void record_reset_values(tid, access_t modify); 
    extern function void record_entry(WordTransaction transaction, access_t modify, string pfx="DEFAULT"); 
    extern function intpair_t find_matching_transaction(word_addr_t addr, int tid); 
    extern function int check_entry(WordTransaction transaction);
    extern function int check_entry_inrange(WordTransaction transaction, int minval, int maxval);
    extern function transq_t get_entries (string addr_name);
    extern function transq_t get_entries_withtid (string addr_name, int tid);
    extern function void del_entry_withtid(string addr_name, int tid);
    extern function void del_entries(string addr_name);
    extern function void del_all();
    extern function void display_all();      

  endclass // RegScoreboard


  function RegScoreboard::new();

    string tmpstr;

    begin
      err_count = 0;
    end 
  endfunction // new


  function void RegScoreboard::record_reset_values(tid, access_t modify); 
    // useful for reset of all registers 

    word_addr_t addr;
    transaction_t new_trans; 
    dword_t sscode;

    if (modify == COLD_RESET)
      reset_exp_data();
    else if (modify == WARM_RESET)
      warm_reset_exp_data();
    else begin
      $display ("TB ERROR. Mass update of registers unsupported w/access type %s", modify.name());
      return;
    end

    foreach (_soc_register_dict[rname]) begin
   
      addr = _soc_register_dict[rname];
      new_trans = {addr: addr, data: _exp_register_data_dict[rname], tid: tid};

      if (addr_table.exists(addr)) 
        addr_table[addr].push_back(new_trans); 
      else 
        addr_table[addr] = {new_trans}; 
    end

  endfunction  // record_reset_vaules


  function void RegScoreboard::record_entry(WordTransaction transaction, access_t modify, string pfx="DEFAULT"); 
    // NOTE. when an entry is recorded, instead of storing the transaction
    // the expected data is stored, so that comparison can be made later on  
    // for a previous 'tid'.

    word_addr_t addr = transaction.addr;
    dword_t data = transaction.data;
    int tid = transaction.tid;
    dword_t sscode; 

    transaction_t new_trans; 
    dword_t exp_data; 
    string addr_name;

    addr_name = _imap_soc_register_dict[addr];
    if(pfx.compare("DEFAULT") == 0)
      update_exp_regval(addr_name, data, modify);
    else
      update_exp_regval(addr_name, data, modify, pfx);

    exp_data = _exp_register_data_dict[addr_name];

    new_trans = {addr: addr, data: exp_data, tid: tid};

    if (addr_table.exists(addr)) begin
      // $display ("INFO. Pushing new transaction into existing queue"); 
      addr_table[addr].push_back(new_trans); 
    end else begin
      // $display ("Adding transaction for addr %x", addr);
      addr_table[addr] = {new_trans}; 
    end

  endfunction // record_entry


  function intpair_t RegScoreboard::find_matching_transaction(word_addr_t addr, int tid); 
    // returns {data, valid} struct pair  
    // Ideally searches through scoreboard table to fine matching transaction.  For 
    // all practical purposes, for a register model only the most recent modication matters. 
    // The code is kept for reference/future usage.

    transaction_t temp_trans; 
    intpair_t matched_p; 
    transq_t qr; 

    int err_found = 0;
    int matched_d = 0; 

    if (!addr_table.exists(addr)) begin
      $display ("TB fault. Address %x does not exist", addr);
      err_found = 1;
    end else begin
      qr = addr_table[addr];
      if (qr.size() == 0) begin
        $display ("TB fault. qr size is 0 for addr %x", addr); 
        err_found = 1; 
      end else if (qr.size() == 1) begin
        // FIXME. This needs a better change. If a write to a register modified register model
        //    (_exp_register_data_dict) and then some other reg operation modified that, this 
        //    transaction's entry in scoreboard is no longer valid! Need TIMESTAMP!
        //
        // temp_trans = qr[0]; 
        // matched_d = int'(temp_trans.data);

        matched_d = int'(_exp_register_data_dict[_imap_soc_register_dict[addr]]);
      end else begin
        qr = addr_table[addr].find_first with(item.tid == tid); 
        if (qr.size() == 0)  begin
          $display ("TB fault. No transaction with id %d found for addr %x", tid, addr);
          err_found = 1; 
        end else if (qr.size() > 1) begin
          $display ("TB fault. Multiple transactions with id %d found for addr %x", tid, addr);
          err_found = 1; 
      end else begin
          // TODO. Same issue related to FIXME above.
          // temp_trans = qr[0];
          // matched_d = int'(temp_trans.data);

          matched_d = int'(_exp_register_data_dict[_imap_soc_register_dict[addr]]);
        end
      end

      if (err_found) 
          $display("ERROR. No matching transaction with tid %d in Reg Scoreboard for addr = %s(0x%08x)",
            tid, _imap_soc_register_dict[addr], addr);
    end

    err_count += err_found;   
    matched_p = {d: matched_d, v: int'(err_found == 0)};
    return matched_p; 

  endfunction // find_matching_transaction


  function int RegScoreboard::check_entry(WordTransaction transaction);
    // returns cumulative (object.)error count - ignore tid if only one transaction

    word_addr_t addr = transaction.addr;
    dword_t data = transaction.data;
    int tid = transaction.tid;

    intpair_t matched_p;
    int err_found = 1; 

    matched_p = find_matching_transaction(addr, tid);

    if (matched_p.v) 
      err_found = int'(matched_p.d != data);

    if (err_found) begin
      $display("ERROR from Reg Scoreboard for addr = %s(0x%08x); observed data = 0x%08x | expected data = 0x%08x",
        _imap_soc_register_dict[addr], addr, data, matched_p.d); 
    end

    err_count += err_found;   
    return err_count; 

  endfunction // check_entry 


  function int RegScoreboard::check_entry_inrange(WordTransaction transaction, int minval, int maxval);
    // Just like RegScoreboard::check_entry but has range to compare against

    word_addr_t addr = transaction.addr;
    dword_t data = transaction.data;
    int tid = transaction.tid;

    intpair_t matched_p;
    int err_found = 1; 

    matched_p = find_matching_transaction(addr, tid);

    if (matched_p.v)  // NOTE. ignore matching data since range needed
      err_found = int'((data < minval) || (data > maxval));

    if (err_found) begin
      $display("ERROR from Reg Scoreboard for addr = %s(0x%08x); observed data = 0x%08x | expected data in [0x%08x, 0x%08x]",
        _imap_soc_register_dict[addr], addr, data, minval, maxval); 
    end

    err_count += err_found;   
    return err_count; 

  endfunction  // check_entry_in_range


  function transq_t RegScoreboard::get_entries (string addr_name);

    word_addr_t addr; 
    transq_t entries; // queue of transactions 

    addr = _soc_register_dict[addr_name]; 

    if (addr_table.exists(addr)) begin
      entries = addr_table[addr];  
    end else 
      $display("TB WARNING. get_entries: No addr %s (0x%08x) found in scoreboard", addr_name, addr);

    return entries;

  endfunction  // get_entries


  function transq_t RegScoreboard::get_entries_withtid (string addr_name, int tid);

    word_addr_t addr; 
    transq_t entries; // queue of transactions 

    addr = _soc_register_dict[addr_name]; 

    if (addr_table.exists(addr)) begin
      entries = addr_table[addr].find with(item.tid == tid); 
    end else 
      $display("TB WARNING. get_entries_withtid: No addr %s (0x%08x) found in scoreboard", addr_name, addr);

    return entries;

  endfunction // get_entries_withtid 


  function void RegScoreboard::del_entry_withtid(string addr_name, int tid);

    int qi [$]; 
    int err_found = 0;

    word_addr_t addr; 

    addr = _soc_register_dict[addr_name]; 

    if (!(addr_table.exists(addr))) begin
      $display("TB WARNING. del_entry_withtid: No addr %s (0x%08x) found in scoreboard", addr_name, addr);
      return;
    end 

    qi = addr_table[addr].find_index with(item.tid == tid); 
    if (qi.size() == 0) 
      $display("TB WARNING. No tid %d / addr (0x%08x) combination found in scoreboard", tid, addr);
    else if (qi.size() == 1) 
      addr_table.delete(addr);
    else begin 
      $display("TB WARNING. Multiple tid %d found for addr (0x%08x) in scoreboard", tid, addr);
      foreach (qi[i])  // Note. This works fine for a hash table, not a queue/array 
        addr_table[addr].delete(qi[i]);
    end

  endfunction  // del_entry_withtid


  function void RegScoreboard::del_entries(string addr_name);
  
    word_addr_t addr;

    addr = _soc_register_dict[addr_name]; 

    if (addr_table.exists(addr)) 
      addr_table.delete(addr);
    else   
      $display("TB WARNING. del_entries: No addr %s (0x%08x) found in scoreboard", addr_name, addr);

  endfunction  // del_entries


  function void RegScoreboard::del_all();

    foreach (addr_table[addr])
      addr_table.delete(addr);

  endfunction  // del_all


  function void RegScoreboard::display_all();      

    int i;
    word_addr_t tmpkey;
    transaction_t tmptrans; 
    transq_t tmpq; 

    $display ("\n\n-- Current state of scoreboard --\n");
    foreach (addr_table[tmpkey]) begin
      tmpq = addr_table[tmpkey]; 
      foreach (tmpq[i]) begin 
          tmptrans = tmpq[i]; 
          $display (" -- Queue for addr %x[%03d]: {addr = %x, data = %x, tid = %x}", 
            tmpkey, i , tmptrans.addr, tmptrans.data, tmptrans.tid);
      end
      $display (" --------------------------------------------- "); 
    end

  endfunction // display_all


endpackage // soc_ifc_tb_pkg

`endif // SOC_IFC_TB_PKG


