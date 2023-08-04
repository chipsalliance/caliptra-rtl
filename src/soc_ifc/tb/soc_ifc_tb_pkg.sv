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



package soc_ifc_tb_pkg;

  `include "caliptra_reg_defines.svh" // This is from integration/rtl level 

  localparam SOCIFC_BASE = `CLP_SOC_IFC_REG_BASE_ADDR;
  localparam SHAACC_BASE = `CLP_SHA512_ACC_CSR_BASE_ADDR;
  localparam ADDR_WIDTH = 32; // SHould be 18; will let APB & AHB bus widths truncate as needed


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
    SET_APB, SET_AHB, SET_DIRECT,
    GET_APB, GET_AHB, GET_DIRECT
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
    "CPTRA_MBOX_VALID_PAUSER"               : 5,  
    "CPTRA_MBOX_PAUSER_LOCK"                : 5,  
    "CPTRA_TRNG_DATA"                       : 12,
    "CPTRA_GENERIC_INPUT_WIRES"             : 2,  
    "CPTRA_GENERIC_OUTPUT_WIRES"            : 2,  
    "CPTRA_FW_REV_ID"                       : 2,
    "FUSE_UDS_SEED"                         : 12,
    "FUSE_FIELD_ENTROPY"                    : 8,
    "FUSE_KEY_MANIFEST_PK_HASH"             : 12,
    "FUSE_OWNER_PK_HASH"                    : 12,
    "FUSE_RUNTIME_SVN"                      : 4,  
    "FUSE_IDEVID_CERT_ATTR"                 : 24, 
    "FUSE_IDEVID_MANUF_HSM_ID"              : 4, 
    "INTERNAL_OBF_KEY"                      : 8  
  };


  // ** NOTE. INTR_BRF (== INTR_BLOCK_RF) registers are NOT explictly tested. Only provided to check for undefined ranges, and for future **
  //  
  // Identifier                                       Base Addr      Offset                                                          // Offset   Description
  word_addr_t _soc_register_dict [string] = {
    "CPTRA_HW_ERROR_FATAL"                          : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_ERROR_FATAL,                               // 0x000      Hardware Error Fatal 
    "CPTRA_HW_ERROR_NON_FATAL"                      : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL,                           // 0x004      Hardware Error Non-Fatal 
    "CPTRA_FW_ERROR_FATAL"                          : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_ERROR_FATAL,                               // 0x008      Firmware Error Fatal 
    "CPTRA_FW_ERROR_NON_FATAL"                      : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_ERROR_NON_FATAL,                           // 0x00c      Firmware Error Non-Fatal 
    "CPTRA_HW_ERROR_ENC"                            : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_ERROR_ENC,                                 // 0x010      Hardware Error Encoding 
    "CPTRA_FW_ERROR_ENC"                            : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_ERROR_ENC,                                 // 0x014      Firmware Error Encoding 
    "CPTRA_FW_EXTENDED_ERROR_INFO"                  : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0,                     // 0x018 [8]  Firmware Extended Error Information 
    "CPTRA_BOOT_STATUS"                             : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_BOOT_STATUS,                                  // 0x038      Boot Status 
    "CPTRA_FLOW_STATUS"                             : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FLOW_STATUS,                                  // 0x03c      Flow Status 
    "CPTRA_RESET_REASON"                            : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_RESET_REASON,                                 // 0x040      Reset Reason 
    "CPTRA_SECURITY_STATE"                          : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_SECURITY_STATE,                               // 0x044      Security State 
    "CPTRA_MBOX_VALID_PAUSER"                       : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_MBOX_VALID_PAUSER_0,                          // 0x048 [5]  Valid User Registers 
    "CPTRA_MBOX_PAUSER_LOCK"                        : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_MBOX_PAUSER_LOCK_0,                           // 0x05c [5]  Valid User Register Lock 
    "CPTRA_TRNG_VALID_PAUSER"                       : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_VALID_PAUSER,                            // 0x070      Valid User for TRNG 
    "CPTRA_TRNG_PAUSER_LOCK"                        : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_PAUSER_LOCK,                             // 0x074      Valid User for TRNG PAUSER Lock 
    "CPTRA_TRNG_DATA"                               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_DATA_0,                                  // 0x078 [12] TRNG Data 
    "CPTRA_TRNG_STATUS"                             : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_STATUS,                                  // 0x0a8      TRNG Status 
    "CPTRA_FUSE_WR_DONE"                            : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FUSE_WR_DONE,                                 // 0x0ac      Fuse Write Done 
    "CPTRA_TIMER_CONFIG"                            : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TIMER_CONFIG,                                 // 0x0b0      Timer Config 
    "CPTRA_BOOTFSM_GO"                              : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_BOOTFSM_GO,                                   // 0x0b4      BOOTFSM GO 
    "CPTRA_DBG_MANUF_SERVICE_REG"                   : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_DBG_MANUF_SERVICE_REG,                        // 0x0b8      DEBUG & MANUF SERVICE REG
    "CPTRA_CLK_GATING_EN"                           : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_CLK_GATING_EN,                                // 0x0bc      Global Caliptra Clk gating enable 
    "CPTRA_GENERIC_INPUT_WIRES"                     : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0,                        // 0x0c0 [2]  Generic Input Wires 
    "CPTRA_GENERIC_OUTPUT_WIRES"                    : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0,                       // 0x0c8 [2]  Generic Output Wires 
    "CPTRA_HW_REV_ID"                               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_REV_ID,                                    // 0x0d0      Caliptra HW RevID 
    "CPTRA_FW_REV_ID"                               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_REV_ID_0,                                  // 0x0d4      Caliptra FW RevID
    "CPTRA_HW_CONFIG"                               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_CONFIG,                                    // 0x0dc      Caliptra HW Config
    "CPTRA_WDT_TIMER1_EN"                           : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_TIMER1_EN,                                // 0x0e0      Caliptra WDT Timer1 EN register  
    "CPTRA_WDT_TIMER1_CTRL"                         : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL,                              // 0x0e4      Caliptra WDT Timer1 CTRL register  
    "CPTRA_WDT_TIMER1_TIMEOUT_PERIOD"               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0,                  // 0x0e8 [2]  Caliptra WDT Timer1 Timeout Period register  
    "CPTRA_WDT_TIMER2_EN"                           : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_TIMER2_EN,                                // 0x0f0      Caliptra WDT Timer2 EN register  
    "CPTRA_WDT_TIMER2_CTRL"                         : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL,                              // 0x0f4      Caliptra WDT Timer2 CTRL register  
    "CPTRA_WDT_TIMER2_TIMEOUT_PERIOD"               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0,                  // 0x0f8 [2]  Caliptra WDT Timer2 Timeout Period register  
    "CPTRA_WDT_STATUS"                              : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_WDT_STATUS,                                   // 0x100      Caliptra WDT STATUS register
    "CPTRA_FUSE_VALID_PAUSER"                       : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FUSE_VALID_PAUSER,                            // 0x104      Valid User for FUSE 
    "CPTRA_FUSE_PAUSER_LOCK"                        : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FUSE_PAUSER_LOCK,                             // 0x108      Valid User for FUSE PAUSER Lock
    // 0x10c..0x1fc
    "FUSE_UDS_SEED"                                 : SOCIFC_BASE + `SOC_IFC_REG_FUSE_UDS_SEED_0,                                    // 0x200 [12] Unique Device Secret 
    "FUSE_FIELD_ENTROPY"                            : SOCIFC_BASE + `SOC_IFC_REG_FUSE_FIELD_ENTROPY_0,                               // 0x230 [8]  Field Entropy 
    "FUSE_KEY_MANIFEST_PK_HASH"                     : SOCIFC_BASE + `SOC_IFC_REG_FUSE_KEY_MANIFEST_PK_HASH_0,                        // 0x250 [12] - 
    "FUSE_KEY_MANIFEST_PK_HASH_MASK"                : SOCIFC_BASE + `SOC_IFC_REG_FUSE_KEY_MANIFEST_PK_HASH_MASK,                     // 0x280      - 
    "FUSE_OWNER_PK_HASH"                            : SOCIFC_BASE + `SOC_IFC_REG_FUSE_OWNER_PK_HASH_0,                               // 0x284 [12] - 
    "FUSE_FMC_KEY_MANIFEST_SVN"                     : SOCIFC_BASE + `SOC_IFC_REG_FUSE_FMC_KEY_MANIFEST_SVN,                          // 0x2b4      - 
    "FUSE_RUNTIME_SVN"                              : SOCIFC_BASE + `SOC_IFC_REG_FUSE_RUNTIME_SVN_0,                                 // 0x2b8 [4]  - 
    "FUSE_ANTI_ROLLBACK_DISABLE"                    : SOCIFC_BASE + `SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE,                         // 0x2c8      - 
    "FUSE_IDEVID_CERT_ATTR"                         : SOCIFC_BASE + `SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0,                            // 0x2cc [24] - 
    "FUSE_IDEVID_MANUF_HSM_ID"                      : SOCIFC_BASE + `SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_0,                         // 0x32c [4]  - 
    "FUSE_LIFE_CYCLE"                               : SOCIFC_BASE + `SOC_IFC_REG_FUSE_LIFE_CYCLE,                                    // 0x33c      - 
    "FUSE_LMS_VERIFY"                               : SOCIFC_BASE + `SOC_IFC_REG_FUSE_LMS_VERIFY,                                    // 0x340      -
    "FUSE_LMS_REVOCATION"                           : SOCIFC_BASE + `SOC_IFC_REG_FUSE_LMS_REVOCATION,                                // 0x344      -
    // 0x348..0x5fc           
    "INTERNAL_OBF_KEY"                              : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_OBF_KEY_0,                                 // 0x600 [8]  De-Obfuscation Key 
    "INTERNAL_ICCM_LOCK"                            : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_ICCM_LOCK,                                 // 0x620      ICCM Lock 
    "INTERNAL_FW_UPDATE_RESET"                      : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET,                           // 0x624      FW Update Reset 
    "INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES"          : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES,               // 0x628      FW Update Reset Wait Cycles 
    "INTERNAL_NMI_VECTOR"                           : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_NMI_VECTOR,                                // 0x62c      NMI Vector 
    "INTERNAL_HW_ERROR_FATAL_MASK"                  : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK,                       // 0x630      Hardware Error Fatal Mask   
    "INTERNAL_HW_ERROR_NON_FATAL_MASK"              : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK,                   // 0x634      Hardware Error Non-Fatal Mask   
    "INTERNAL_FW_ERROR_FATAL_MASK"                  : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_FW_ERROR_FATAL_MASK,                       // 0x638      Firmware Error Fatal Mask   
    "INTERNAL_FW_ERROR_NON_FATAL_MASK"              : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK,                   // 0x63C      Firmware Error Non-Fatal Mask 0
    "INTERNAL_RV_MTIME_L"                           : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_RV_MTIME_L,                                // 0x640      mtime low   
    "INTERNAL_RV_MTIME_H"                           : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_RV_MTIME_H,                                // 0x644      mtime high  
    "INTERNAL_RV_MTIMECMP_L"                        : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_RV_MTIMECMP_L,                             // 0x648      mtimecmp low  
    "INTERNAL_RV_MTIMECMP_H"                        : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_RV_MTIMECMP_H,                             // 0x64C      mtimecmp high
    // 0x650..0x7fc    
    // SoC IFC Interrupt Block Register 
    "INTR_BRF_GLOBAL_INTR_EN_R"                     : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R,                     // 0x800
    "INTR_BRF_ERROR_INTR_EN_R"                      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R,                      // 0x804
    "INTR_BRF_NOTIF_INTR_EN_R"                      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R,                      // 0x808
    "INTR_BRF_ERROR_GLOBAL_INTR_R"                  : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R,                  // 0x80c
    "INTR_BRF_NOTIF_GLOBAL_INTR_R"                  : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R,                  // 0x810
    "INTR_BRF_ERROR_INTERNAL_INTR_R"                : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R,                // 0x814
    "INTR_BRF_NOTIF_INTERNAL_INTR_R"                : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R,                // 0x818
    "INTR_BRF_ERROR_INTR_TRIG_R"                    : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R,                    // 0x81c
    "INTR_BRF_NOTIF_INTR_TRIG_R"                    : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R,                    // 0x820
    // 0x824..0x8fc
    "INTR_BRF_ERROR_INTERNAL_INTR_COUNT_R"          : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R,          // 0x900
    "INTR_BRF_ERROR_INV_DEV_INTR_COUNT_R"           : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R,           // 0x904
    "INTR_BRF_ERROR_CMD_FAIL_INTR_COUNT_R"          : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R,          // 0x908
    "INTR_BRF_ERROR_BAD_FUSE_INTR_COUNT_R"          : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R,          // 0x90c
    "INTR_BRF_ERROR_ICCM_BLOCKED_INTR_COUNT_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R,      // 0x910
    "INTR_BRF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R,      // 0x914
    "INTR_BRF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R": SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R,// 0x918   
    "INTR_BRF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R": SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R,// 0x91c   
    // 0x920..0x97c
    "INTR_BRF_NOTIF_CMD_AVAIL_INTR_COUNT_R"         : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R,         // 0x980
    "INTR_BRF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R,      // 0x984
    "INTR_BRF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R,      // 0x988
    "INTR_BRF_NOTIF_SCAN_MODE_INTR_COUNT_R"         : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R,         // 0x98c 
    "INTR_BRF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R,      // 0x990 
    "INTR_BRF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R"     : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R,     // 0x994
    // 0x998..0x9fc 
    "INTR_BRF_ERROR_INTERNAL_INTR_COUNT_INCR_R"     : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R,     // 0xa00
    "INTR_BRF_ERROR_INV_DEV_INTR_COUNT_INCR_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R,      // 0xa04
    "INTR_BRF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R"     : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R,     // 0xa08
    "INTR_BRF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R"     : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R,     // 0xa0c
    "INTR_BRF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R" : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R, // 0xa10
    "INTR_BRF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R" : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R, // 0xa14
    "INTR_BRF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R" : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R,  // 0xa18  
    "INTR_BRF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R" : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R,  // 0xa1c  
    "INTR_BRF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R"    : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R,    // 0xa20
    "INTR_BRF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R" : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R, // 0xa24   
    "INTR_BRF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R" : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R, // 0xa28 
    "INTR_BRF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R" : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R, // 0xa2c

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
    '{addr_min: SOCIFC_BASE + 16'h010c, addr_max: SOCIFC_BASE + 16'h01fc},
    '{addr_min: SOCIFC_BASE + 16'h0348, addr_max: SOCIFC_BASE + 16'h05fc},
    '{addr_min: SOCIFC_BASE + 16'h0650, addr_max: SOCIFC_BASE + 16'h07fc},
    '{addr_min: SOCIFC_BASE + 16'h0824, addr_max: SOCIFC_BASE + 16'h08fc},
    '{addr_min: SOCIFC_BASE + 16'h0920, addr_max: SOCIFC_BASE + 16'h097c},
    '{addr_min: SOCIFC_BASE + 16'h0998, addr_max: SOCIFC_BASE + 16'h09fc}
  };
 

  // Only non-zero power-on values are stored; also populated by SocRegisters instantiation 
  dword_t _soc_register_initval_dict [string] = {
    "CPTRA_MBOX_VALID_PAUSER"              : 32'hffff_ffff,
    "CPTRA_TRNG_VALID_PAUSER"              : 32'hffff_ffff,
    "INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES" : 32'h5,
    "CPTRA_HW_REV_ID"                      : 32'h1,
    "CPTRA_WDT_TIMER1_TIMEOUT_PERIOD"      : 32'hffff_ffff,
    "CPTRA_WDT_TIMER2_TIMEOUT_PERIOD"      : 32'hffff_ffff,
    "CPTRA_FUSE_VALID_PAUSER"              : 32'hffff_ffff
  };


  // Sticky registers preserve values across warm reset -- groups of regs might be populated by code
  // mask of all bits to be protected in case of warm reset
  word_addr_t _sticky_register_prefix_dict [string] = {
    "FUSE_":                                           32'hffff_ffff, 
    "CPTRA_HW_ERROR_":                                 32'hffff_ffff, // FATAL, NON_FATAL, ENC                          
    "CPTRA_FW_ERROR_":                                 32'hffff_ffff, // FATAL, NON_FATAL, ENC                          
    "CPTRA_FW_EXTENDED_ERROR_INFO":                    32'hffff_ffff,
    "CPTRA_RESET_REASON":                              32'h2,         // field WARM_RESET 
    "CPTRA_FUSE_WR_DONE":                              32'h1,         // field 0 
    "CPTRA_FUSE_VALID_PAUSER":                         32'hffff_ffff,
    "CPTRA_FUSE_PAUSER_LOCK":                          32'h1,
    "CPTRA_TIMER_CONFIG":                              32'hffff_ffff,                           
    "INTERNAL_RV_MTIME_L":                             32'hffff_ffff,
    "INTERNAL_RV_MTIME_H":                             32'hffff_ffff,
    "INTERNAL_RV_MTIMECMP_L":                          32'hffff_ffff,
    "INTERNAL_RV_MTIMECMP_H":                          32'hffff_ffff,
    "INTR_BRF_ERROR_INTERNAL_INTR_R":                  32'h3f,        // fields 5:0
    "INTR_BRF_ERROR_INTERNAL_INTR_COUNT_R":            32'hffff_ffff,          
    "INTR_BRF_ERROR_INV_DEV_INTR_COUNT_R":             32'hffff_ffff,
    "INTR_BRF_ERROR_CMD_FAIL_INTR_COUNT_R":            32'hffff_ffff,
    "INTR_BRF_ERROR_BAD_FUSE_INTR_COUNT_R":            32'hffff_ffff,
    "INTR_BRF_ERROR_ICCM_BLOCKED_INTR_COUNT_R":        32'hffff_ffff,
    "INTR_BRF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R":        32'hffff_ffff,
    "INTR_BRF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R":  32'hffff_ffff,
    "INTR_BRF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R":  32'hffff_ffff
  };



  // mask bits that reflect which fields can be modified  
  dword_t _soc_register_mask_dict [string] = {
    "CPTRA_HW_CONFIG"                                  : (`SOC_IFC_REG_CPTRA_HW_CONFIG_ITRNG_EN_MASK |
                                                          `SOC_IFC_REG_CPTRA_HW_CONFIG_QSPI_EN_MASK  |                                                  
                                                          `SOC_IFC_REG_CPTRA_HW_CONFIG_I3C_EN_MASK),
    "FUSE_ANTI_ROLLBACK_DISABLE"                       : `SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_MASK, 
    "FUSE_KEY_MANIFEST_PK_HASH_MASK"                   : `SOC_IFC_REG_FUSE_KEY_MANIFEST_PK_HASH_MASK_MASK_MASK,
    "FUSE_LIFE_CYCLE"                                  : `SOC_IFC_REG_FUSE_LIFE_CYCLE_LIFE_CYCLE_MASK, 
    "FUSE_LMS_VERIFY"                                  : `SOC_IFC_REG_FUSE_LMS_VERIFY_LMS_VERIFY_MASK,
    "CPTRA_FLOW_STATUS"                                : (`SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK             |
                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK        |
                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FW_MASK       |
                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK  |
                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK    |
                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_MASK),
    "CPTRA_MBOX_PAUSER_LOCK"                           : `SOC_IFC_REG_CPTRA_MBOX_PAUSER_LOCK_0_LOCK_MASK,   // same for all 5 pausers
    "CPTRA_TRNG_PAUSER_LOCK"                           : `SOC_IFC_REG_CPTRA_TRNG_PAUSER_LOCK_LOCK_MASK,
    "CPTRA_TRNG_STATUS.APB"                            : `SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_MASK, 
    "CPTRA_TRNG_STATUS.AHB"                            : `SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_REQ_MASK,     
    "CPTRA_FUSE_WR_DONE"                               : `SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK,
    "CPTRA_BOOTFSM_GO"                                 : `SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_MASK, 
    "CPTRA_CLK_GATING_EN"                              : `SOC_IFC_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_MASK,
    "CPTRA_WDT_TIMER1_EN"                              : `SOC_IFC_REG_CPTRA_WDT_TIMER1_EN_TIMER1_EN_MASK,
    "CPTRA_WDT_TIMER1_CTRL"                            : `SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_MASK,
    "CPTRA_WDT_TIMER2_EN"                              : `SOC_IFC_REG_CPTRA_WDT_TIMER2_EN_TIMER2_EN_MASK,
    "CPTRA_WDT_TIMER2_CTRL"                            : `SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_MASK,
    "CPTRA_WDT_STATUS"                                 : (`SOC_IFC_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_MASK | 
                                                          `SOC_IFC_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_MASK),
    "CPTRA_FUSE_PAUSER_LOCK"                           : `SOC_IFC_REG_CPTRA_FUSE_PAUSER_LOCK_LOCK_MASK, 
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

    return _soc_register_initval_dict.exists(addr_name) ? _soc_register_initval_dict[addr_name] : '0; 

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
      tmp_data = tmp_data & (32'hffff_ffff ^ `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK)    
                          & (32'hffff_ffff ^ `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK); 
      tmp_data = tmp_data | mask_shifted(debug_locked, `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK)
                          | mask_shifted(gen_input_wire_toggle, `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK);
      update_exp_regval("INTR_BRF_NOTIF_INTERNAL_INTR_R", tmp_data, SET_DIRECT);

      $display( "TB INFO. Updated expected value of INTR_BRF_NOTIF_INTERNAL_INTR_R = 0x%08x", _exp_register_data_dict["INTR_BRF_NOTIF_INTERNAL_INTR_R"]);
      return _exp_register_data_dict["INTR_BRF_NOTIF_INTERNAL_INTR_R"];
    end 

  endfunction // update_INTR_BRF_NOTIF_INTERNAL_INTR_R


  // Needs RMW of register without APB or AHB writes 
  function automatic dword_t update_CPTRA_FLOW_STATUS(int fuse_ready_val, logic [2:0] boot_fsm_ps);

    dword_t tmp_data;

    begin

      tmp_data = _exp_register_data_dict["CPTRA_FLOW_STATUS"]; // then preserve read-only bit fields per masks 
      tmp_data = tmp_data & (32'hffff_ffff ^ `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK);
      tmp_data = tmp_data | mask_shifted(fuse_ready_val, `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK);
      tmp_data = tmp_data & (32'hffff_ffff ^ `SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK);
      tmp_data = tmp_data | mask_shifted(boot_fsm_ps, `SOC_IFC_REG_CPTRA_FLOW_STATUS_BOOT_FSM_PS_MASK);
      $display( "TB DEBUG. update_CPTRA_FLOW_STATUS(%x, %x) at time %t. new tmp_data = 0x%08x", fuse_ready_val, boot_fsm_ps, $realtime, tmp_data); 

      update_exp_regval("CPTRA_FLOW_STATUS", tmp_data, SET_DIRECT); 

      $display( "TB INFO. Updated expected value of CPTRA_FLOW_STATUS = 0x%08x", _exp_register_data_dict["CPTRA_FLOW_STATUS"]);
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


  function void update_exp_regval(string addr_name, dword_t indata, access_t modify);
    // "expected" model of register. Read-modify-write model 
   
    word_addr_t addr; 
    dword_t curr_data, exp_data;
    dword_t ahb_indata, apb_indata, apb_rodata, ahb_rodata;

    string tmpstr; 
    string pauser_suffix; 
    string pauser_lock_regname; 
    int pauser_locked, fuses_locked, lock_mask, iccm_locked; 

    dword_t sscode;
    dword_t tmp_data;

    begin

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
            _exp_register_data_dict["INTERNAL_ICCM_LOCK"] = '0;  
            $display ("TB INFO: Cross modification - Writing '1' to INTERNAL_FW_UPDATE_RESET also reset INTERNAL_ICCM_LOCK"); 

            tmp_data = _exp_register_data_dict["CPTRA_RESET_REASON"]; 
            tmp_data = tmp_data & (32'hffff_ffff ^ `SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK)  |
                        tmp_data & mask_shifted(1'b1, `SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK); 
            $display ("TB INFO: Cross modification - Writing '1' to INTERNAL_FW_UPDATE_RESET also sets CPTRA_RESET_REASON"); 
        end
        return;
      end 


      fuses_locked = _fuses_locked; 

      curr_data = _exp_register_data_dict[addr_name];

      apb_indata = indata & {32{(modify == SET_APB)}}; // apb_mutable;
      ahb_indata = indata & {32{(modify == SET_AHB)}}; // ahb_mutable;

      apb_rodata = curr_data & {32{(modify == SET_APB)}}; // apb_readonly;
      ahb_rodata = curr_data & {32{(modify == SET_AHB)}}; // ahb_readonly;

      // handle wide registers first, then normal sized ones

      if (str_startswith(addr_name, "CPTRA_TRNG_DATA"))
        exp_data = ahb_rodata | apb_indata;  // ahb-RO

      else if (str_startswith(addr_name, "CPTRA_FW_REV_ID")) begin
        exp_data = ahb_indata | apb_rodata; // apb-RO
        // $display( "TB DEBUG. CPTRA_FW_REV_ID: addr %-30s, exp_data 0x%08x", addr_name, exp_data); 
      
      end else if ((str_startswith(addr_name, "FUSE_UDS_SEED")) || (str_startswith(addr_name, "FUSE_FIELD_ENTROPY")))
        exp_data = '0; // not accessible over APB or AHB 

      else if (str_startswith(addr_name, "FUSE_"))
        exp_data = fuses_locked ? curr_data : (ahb_rodata | apb_indata & get_mask(addr_name)); // ahb-RO 

      else if (str_startswith(addr_name, "CPTRA_MBOX_VALID_PAUSER")) begin    // find equivalent pauser lock & if set, apb-RO 
        tmpstr = "CPTRA_MBOX_VALID_PAUSER";
        pauser_suffix = addr_name.substr(tmpstr.len(), addr_name.len()-1);
        pauser_lock_regname = {"CPTRA_MBOX_PAUSER_LOCK", pauser_suffix};
        pauser_locked = _exp_register_data_dict[pauser_lock_regname]; 
        exp_data = pauser_locked ? curr_data : (ahb_indata | apb_indata); 

      end else if (str_startswith(addr_name, "CPTRA_MBOX_PAUSER_LOCK")) begin //  if pauser locked, apb-RO
        tmpstr = "CPTRA_MBOX_PAUSER_LOCK";
        pauser_locked = _exp_register_data_dict[addr_name];
        exp_data = pauser_locked ? curr_data & get_mask(tmpstr) :  (ahb_indata | apb_indata) & get_mask(tmpstr); 

      end else if (str_startswith(addr_name, "CPTRA_GENERIC_INPUT_WIRES")) 
        exp_data = curr_data; // all bits are RO 

      else if (str_startswith(addr_name, "CPTRA_GENERIC_OUTPUT_WIRES"))  
        exp_data = ahb_indata | apb_rodata; // all bits are apb-RO 

      else if (str_startswith(addr_name, "CPTRA_HW_CONFIG"))
        exp_data = curr_data & get_mask("CPTRA_HW_CONFIG"); // all bits are RO 

      else if (str_startswith(addr_name, "INTERNAL_OBF_KEY"))            
        exp_data = '0;  // not accessible over APB or AHB 

      else if (str_startswith(addr_name, "SHA_ACC_INTR_BRF"))
        if (str_endswith(addr_name, "INCR_R"))
          exp_data = ahb_rodata | apb_rodata; 
        else if ((addr_name == "SHA_ACC_INTR_BRF_ERROR_GLOBAL_INTR_R") || (addr_name == "SHA_ACC_INTR_BRF_NOTIF_GLOBAL_INTR_R"))
          exp_data = ahb_rodata | apb_rodata; 
        else
          exp_data = ahb_indata & get_mask(addr_name) | apb_rodata; 

      else if (str_startswith(addr_name, "INTR_BRF_")) begin // Interrupt block has its own sub-cases

        if (is_pulsed_reg(addr_name)) begin
          exp_data = '0;
          
        end else begin
          case (addr_name)

            "INTR_BRF_ERROR_GLOBAL_INTR_R":exp_data = ahb_rodata | apb_rodata; // set by HW  
            "INTR_BRF_NOTIF_GLOBAL_INTR_R":exp_data = ahb_rodata | apb_rodata; // set by HW  
            "INTR_BRF_ERROR_INTR_TRIG_R": exp_data = ((ahb_indata & get_mask(addr_name)) != 0) ? '0: apb_rodata; // TODO. Pulsed reg 
            "INTR_BRF_NOTIF_INTR_TRIG_R": exp_data = ((ahb_indata & get_mask(addr_name)) != 0) ? '0: apb_rodata; // TODO. Pulsed reg 
            "INTR_BRF_ERROR_INTERNAL_INTR_R": exp_data = apb_rodata | (~(ahb_indata & get_mask(addr_name)) & curr_data);
            "INTR_BRF_NOTIF_INTERNAL_INTR_R": exp_data = apb_rodata | (~(ahb_indata & get_mask(addr_name)) & curr_data);

            default: exp_data = ahb_indata & get_mask(addr_name) | apb_rodata;

          endcase

        end

      end else begin    
        
        case (addr_name)
    
          "CPTRA_HW_ERROR_FATAL", "CPTRA_HW_ERROR_NON_FATAL": begin
            exp_data = ahb_indata | apb_indata;  
            exp_data = '0; // write-one to clear -- effectively always 0
          end

          "CPTRA_FLOW_STATUS"                    : exp_data = ahb_indata & get_mask(addr_name) | apb_rodata; //  32'hbfff_ffff; // apb-RO 
          "CPTRA_RESET_REASON"                   : exp_data = ahb_rodata | apb_rodata; //  bit 1:0 is RO 
          "CPTRA_SECURITY_STATE"                 : exp_data = curr_data & get_mask(addr_name); // & sscode;  //  bit 3:0 is RO 

          "CPTRA_TRNG_VALID_PAUSER" : begin // find equivalent pauser lock & if set, apb-RO 
            pauser_locked = _exp_register_data_dict["CPTRA_TRNG_PAUSER_LOCK"]; 
            exp_data = pauser_locked ? curr_data : (ahb_indata | apb_indata); 
          end

          "CPTRA_TRNG_PAUSER_LOCK": begin
            lock_mask = get_mask(addr_name); 
            pauser_locked = curr_data & get_mask(addr_name); // TODO. TRNG registers may need exclusion 
            exp_data = pauser_locked ? curr_data & lock_mask :  (ahb_indata | apb_indata) & lock_mask;  
          end

          "CPTRA_TRNG_STATUS": begin                                        //                   WR_DONE        REQ
            dword_t ahb_mask = get_mask("CPTRA_TRNG_STATUS.AHB"); 
            dword_t apb_mask = get_mask("CPTRA_TRNG_STATUS.APB"); 
            exp_data = (ahb_rodata & ~ahb_mask | ahb_indata & ahb_mask) |   // Caliptra Access:       RO         RW 
                       (apb_rodata & ~apb_mask | apb_indata & apb_mask) ;   // SOC Access:            RW         RO
          end

          "CPTRA_HW_REV_ID"                                 : exp_data = curr_data;  
          "CPTRA_WDT_TIMER1_EN"                             : exp_data = ahb_indata & get_mask(addr_name) | apb_rodata;
          "CPTRA_WDT_TIMER1_CTRL"                           : exp_data = ((ahb_indata & get_mask(addr_name)) != 0) ? '0: apb_rodata; // TODO. Pulsed reg
          "CPTRA_WDT_TIMER1_TIMEOUT_PERIOD"                 : exp_data = ahb_indata | apb_rodata; 
          "CPTRA_WDT_TIMER2_EN"                             : exp_data = ahb_indata & get_mask(addr_name) | apb_rodata;
          "CPTRA_WDT_TIMER2_CTRL"                           : exp_data = ((ahb_indata & get_mask(addr_name)) != 0) ? '0: apb_rodata; // TODO. Pulsed reg 
          "CPTRA_WDT_TIMER2_TIMEOUT_PERIOD"                 : exp_data = ahb_indata | apb_rodata; 
          "CPTRA_WDT_STATUS"                                : exp_data = curr_data; 
          "CPTRA_FUSE_WR_DONE"                              : exp_data = fuses_locked ? curr_data : (ahb_rodata | apb_indata & get_mask(addr_name)); 
          "CPTRA_BOOTFSM_GO"                                : exp_data = ahb_rodata | apb_indata & get_mask(addr_name) ; 
          "CPTRA_BOOT_STATUS"                               : exp_data = ahb_indata | apb_rodata; 
          "CPTRA_CLK_GATING_EN"                             : exp_data = ahb_rodata | apb_indata & get_mask(addr_name) ; 

          "CPTRA_FUSE_VALID_PAUSER" : begin // find equivalent pauser lock & if set, apb-RO 
            pauser_locked = _exp_register_data_dict["CPTRA_FUSE_PAUSER_LOCK"]; 
            exp_data = pauser_locked ? curr_data : (ahb_indata | apb_indata); 
          end

          "CPTRA_FUSE_PAUSER_LOCK": begin
            lock_mask = get_mask(addr_name); 
            pauser_locked = curr_data & get_mask(addr_name); 
            exp_data = pauser_locked ? curr_data & lock_mask :  (ahb_indata | apb_indata) & lock_mask;  
          end 

          "INTERNAL_ICCM_LOCK"                              : begin
            iccm_locked = curr_data & get_mask(addr_name); 
            exp_data = iccm_locked ? curr_data : (ahb_indata & get_mask(addr_name) | apb_rodata); 
          end 

          "INTERNAL_FW_UPDATE_RESET"                        : begin
            exp_data = ahb_indata & get_mask(addr_name) | apb_rodata; 

            // $display ("TB DEBUG: ahb_indata = 0x%x and exp_data for INTERNAL_FW_UPDATE_RESET = 0x%x", ahb_indata, exp_data); 
            if (exp_data[0]) begin  // write-one to clear
              _exp_register_data_dict["INTERNAL_ICCM_LOCK"] = '0;  
              $display ("TB INFO: Cross modification - Writing '1' to INTERNAL_FW_UPDATE_RESET also reset INTERNAL_ICCM_LOCK"); 

              _exp_register_data_dict["CPTRA_RESET_REASON"] = 32'h1;  //TODO. Ignoring warm reset for now 
              $display ("-- CPTRA_RESET_REASON is now %d", _exp_register_data_dict["CPTRA_RESET_REASON"]); 
              $display ("TB INFO: Cross modification - Writing '1' to INTERNAL_FW_UPDATE_RESET also sets CPTRA_RESET_REASON"); 
            end
          end

          "INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES"            : exp_data = ahb_indata & get_mask(addr_name) | apb_rodata;  
          "INTERNAL_NMI_VECTOR"                             : exp_data = ahb_indata | apb_rodata;  
          "INTERNAL_HW_ERROR_FATAL_MASK"                    : exp_data = ahb_indata & get_mask(addr_name) | apb_rodata;  
          "INTERNAL_HW_ERROR_NON_FATAL_MASK"                : exp_data = ahb_indata & get_mask(addr_name) | apb_rodata;  
          "INTERNAL_FW_ERROR_FATAL_MASK"                    : exp_data = ahb_indata | apb_rodata;  
          "INTERNAL_FW_ERROR_NON_FATAL_MASK"                : exp_data = ahb_indata | apb_rodata;  
          "INTERNAL_RV_MTIME_L"                             : exp_data = ahb_indata | apb_rodata;
          "INTERNAL_RV_MTIME_H"                             : exp_data = ahb_indata | apb_rodata;
          "INTERNAL_RV_MTIMECMP_L"                          : exp_data = ahb_indata | apb_rodata;
          "INTERNAL_RV_MTIMECMP_H"                          : exp_data = ahb_indata | apb_rodata;

          default: exp_data = indata;

        endcase

      end 
      _exp_register_data_dict[addr_name] = exp_data;
      // $display ("TB DEBUG: Expected data for addr_name %s (addr 0x%08x) = 0x%08x", addr_name, addr, exp_data); 
    end

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
    end 

    return fuse_regs;

  endfunction // get_fuse_regnames


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
      if (rkey.substr(0,3) != "FUSE")
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
          str_startswith(rkey, "FUSE")) 
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
      foreach (_soc_register_dict[rname]) 
        _exp_register_data_dict[rname] = get_initval(rname); 
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
          if (str_startswith(rname, sticky_rname)) begin
            wrmrst_pfx_match = 1;
            _exp_register_data_dict[rname] = _exp_register_data_dict[rname] & _sticky_register_prefix_dict[sticky_rname];
            // $display("assigning sticky value _exp_register_data_dict[%-30s] = 0x%08x", rname, _exp_register_data_dict[rname]); 
            break;
          end
        end

        if (!wrmrst_pfx_match) begin
          _exp_register_data_dict[rname] = get_initval(rname);
          // $display("assigning init value   _exp_register_data_dict[%-30s] = 0x%08x", rname, _exp_register_data_dict[rname]); 
        end

      end
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
  function automatic int str_startswith(string s1, string s2);

    return (s2 == s1.substr(0, s2.len() - 1));

  endfunction  // str_startswith


  function automatic int str_endswith(string s1, string s2);

    int s1_eix = s1.len() - 1;  
    int s2_eix = s2.len() - 1;  

    return (s2 == s1.substr(s1_eix - s2_eix, s1_eix));

  endfunction  // str_endswith


  function automatic del_from_strq(inout strq_t mutable_strq, input string name);  

    automatic int iq [$];

    iq = mutable_strq.find_index with (item == name); 
    foreach (iq[i]) 
      mutable_strq.delete(iq[i]);

  endfunction // del_from_strq


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

    if (_soc_register_dict.exists(name))
      return _soc_register_dict[name];
    else begin
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
    extern function void record_entry(WordTransaction transaction, access_t modify); 
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


  function void RegScoreboard::record_entry(WordTransaction transaction, access_t modify); 
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
    update_exp_regval(addr_name, data, modify);
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
      foreach (qi[i]) 
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


