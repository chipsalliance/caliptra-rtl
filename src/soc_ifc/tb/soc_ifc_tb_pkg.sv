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

  typedef transaction_t tidq_t [$];  

  typedef string strq_t [$];  

  typedef enum {
    COLD_RESET, WARM_RESET,
    SET_APB, SET_AHB, SET_DIRECT,
    GET_APB, GET_AHB, GET_DIRECT
  } access_t; 


  // ================================================================================ 
  // Constants & Global Data Structures
  // ================================================================================ 

  int _fuses_locked = 0; // TODO. This is a crutch; should be static var inside a class

  // typedef enum logic [2:0] { 
  logic [2:0] security_state_dict [string] = {
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

  // TODO. This will be merged into register dict at some point as a pair 
  word_addr_t wide_register_dict [string] = {
    "CPTRA_FW_EXTENDED_ERROR_INFO"          : 8, 
    "CPTRA_VALID_PAUSER"                    : 5,  
    "CPTRA_PAUSER_LOCK"                     : 5,  
    "CPTRA_GENERIC_INPUT_WIRES"             : 2,  
    "CPTRA_GENERIC_OUTPUT_WIRES"            : 2,  
    "FUSE_UDS_SEED"                         : 12,
    "FUSE_FIELD_ENTROPY"                    : 8,
    "FUSE_KEY_MANIFEST_PK_HASH"             : 12,
    "FUSE_OWNER_PK_HASH"                    : 12,
    "FUSE_RUNTIME_SVN"                      : 4,  
    "FUSE_IDEVID_CERT_ATTR"                 : 24, 
    "FUSE_IDEVID_MANUF_HSM_ID"              : 4, 
    "INTERNAL_OBF_KEY"                      : 8  
  };


  // Identifier                              Base Addr        Offset                                     // Offset    Description
  word_addr_t soc_register_dict [string] = {
    "CPTRA_HW_ERROR_FATAL"                  : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_ERROR_FATAL,           // 0x000    Hardware Error Fatal 
    "CPTRA_HW_ERROR_NON_FATAL"              : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL,       // 0x004    Hardware Error Non-Fatal 
    "CPTRA_FW_ERROR_FATAL"                  : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_ERROR_FATAL,           // 0x008    Firmware Error Fatal 
    "CPTRA_FW_ERROR_NON_FATAL"              : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_ERROR_NON_FATAL,       // 0x00C    Firmware Error Non-Fatal 
    "CPTRA_HW_ERROR_ENC"                    : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_HW_ERROR_ENC,             // 0x010    Hardware Error Encoding 
    "CPTRA_FW_ERROR_ENC"                    : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_ERROR_ENC,             // 0x014    Firmware Error Encoding 
    "CPTRA_FW_EXTENDED_ERROR_INFO"          : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0, // 0x018    [8]  Firmware Extended Error Information 
    "CPTRA_BOOT_STATUS"                     : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_BOOT_STATUS,              // 0x038    Boot Status 
    "CPTRA_FLOW_STATUS"                     : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FLOW_STATUS,              // 0x03C    Flow Status 
    "CPTRA_RESET_REASON"                    : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_RESET_REASON,             // 0x040    Reset Reason 
    "CPTRA_SECURITY_STATE"                  : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_SECURITY_STATE,           // 0x044    Security State 
    "CPTRA_VALID_PAUSER"                    : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_VALID_PAUSER_0,           // 0x048    [5]  Valid User Registers 
    "CPTRA_PAUSER_LOCK"                     : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_PAUSER_LOCK_0,            // 0x05C    [5]  Valid User Register Lock 
    "CPTRA_TRNG_VALID_PAUSER"               : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_VALID_PAUSER,        // 0x070    Valid User for TRNG 
    "CPTRA_TRNG_PAUSER_LOCK"                : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_PAUSER_LOCK,         // 0x074    Valid User for TRNG PAUSER Lock 
    "CPTRA_TRNG_DATA"                       : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_DATA_0,              // 0x078    [12] TRNG Data 
    "CPTRA_TRNG_STATUS"                     : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TRNG_STATUS,              // 0x0A8    TRNG Status 
    "CPTRA_FUSE_WR_DONE"                    : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FUSE_WR_DONE,             // 0x0AC    Fuse Write Done 
    "CPTRA_TIMER_CONFIG"                    : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_TIMER_CONFIG,             // 0x0B0    Timer Config 
    "CPTRA_BOOTFSM_GO"                      : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_BOOTFSM_GO,               // 0x0B4    BOOTFSM GO 

    "CPTRA_CLK_GATING_EN"                   : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_CLK_GATING_EN,            // 0x0BC    Global Caliptra Clk gating enable 
    "CPTRA_GENERIC_INPUT_WIRES"             : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0,    // 0x0C0    [2]  Generic Input Wires 
    "CPTRA_GENERIC_OUTPUT_WIRES"            : SOCIFC_BASE + `SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0,   // 0x0C8    [2]  Generic Output Wires 
                                                                                                         // 0x0D0    -    - 
    "FUSE_UDS_SEED"                         : SOCIFC_BASE + `SOC_IFC_REG_FUSE_UDS_SEED_0,                // 0x200    [12] Unique Device Secret 
    "FUSE_FIELD_ENTROPY"                    : SOCIFC_BASE + `SOC_IFC_REG_FUSE_FIELD_ENTROPY_0,           // 0x230    [8]  Field Entropy 
    "FUSE_KEY_MANIFEST_PK_HASH"             : SOCIFC_BASE + `SOC_IFC_REG_FUSE_KEY_MANIFEST_PK_HASH_0,    // 0x250    [12] - 
    "FUSE_KEY_MANIFEST_PK_HASH_MASK"        : SOCIFC_BASE + `SOC_IFC_REG_FUSE_KEY_MANIFEST_PK_HASH_MASK, // 0x280    - 
    "FUSE_OWNER_PK_HASH"                    : SOCIFC_BASE + `SOC_IFC_REG_FUSE_OWNER_PK_HASH_0,           // 0x284    [12] - 
    "FUSE_FMC_KEY_MANIFEST_SVN"             : SOCIFC_BASE + `SOC_IFC_REG_FUSE_FMC_KEY_MANIFEST_SVN,      // 0x2B4    - 
    "FUSE_RUNTIME_SVN"                      : SOCIFC_BASE + `SOC_IFC_REG_FUSE_RUNTIME_SVN_0,             // 0x2B8    [4]  - 
    "FUSE_ANTI_ROLLBACK_DISABLE"            : SOCIFC_BASE + `SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE,     // 0x2C8         - 
    "FUSE_IDEVID_CERT_ATTR"                 : SOCIFC_BASE + `SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0,        // 0x2CC    [24] - 
    "FUSE_IDEVID_MANUF_HSM_ID"              : SOCIFC_BASE + `SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_0,     // 0x32C    [4]  - 
    "FUSE_LIFE_CYCLE"                       : SOCIFC_BASE + `SOC_IFC_REG_FUSE_LIFE_CYCLE,                // 0x33C         - 
            
    "INTERNAL_OBF_KEY"                      : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_OBF_KEY_0,             // 0x600    [8]  De-Obfuscation Key 
    "INTERNAL_ICCM_LOCK"                    : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_ICCM_LOCK,             // 0x620    ICCM Lock 
    "INTERNAL_FW_UPDATE_RESET"              : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET,       // 0x624    FW Update Reset 
    "INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES"  : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES,// 0x628   FW Update Reset Wait Cycles 
    "INTERNAL_NMI_VECTOR"                   : SOCIFC_BASE + `SOC_IFC_REG_INTERNAL_NMI_VECTOR             // 0x62C    NMI Vector 
                                                                                                         // 0x630..0x7fc    
  };
    // Following needs to be added into the block 
    // "intr_block_rf"                         : `SOCIFC_BASE + ... 

/*
    "INTR_BLOCK_RF_GLOBAL_INTR_EN_R"                       : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R,                      // 0x800
    "INTR_BLOCK_RF_ERROR_INTR_EN_R"                        : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R,                       // 0x804
    "INTR_BLOCK_RF_NOTIF_INTR_EN_R"                        : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R,                       // 0x808
    "INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R"                    : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R,                   // 0x80c
    "INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R"                    : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R,                   // 0x810
    "INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R"                  : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R,                 // 0x814
    "INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R"                  : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R,                 // 0x818
    "INTR_BLOCK_RF_ERROR_INTR_TRIG_R"                      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R,                     // 0x81c
    "INTR_BLOCK_RF_NOTIF_INTR_TRIG_R"                      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R,                     // 0x820
    // - 0x824..0x8fc
    "INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R"            : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R,           // 0x900
    "INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R"             : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R,            // 0x904
    "INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R"            : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R,           // 0x908
    "INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R"            : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R,           // 0x90c
    "INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R"        : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R,       // 0x910
    "INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R"        : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R,       // 0x914
    // - 0x914..0x97c
    "INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R"           : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R,          // 0x980
    "INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R"        : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R,       // 0x984
    "INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R"        : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R,       // 0x988
    // - 0x98c..0x9fc 
    "INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R"       : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R,      // 0xa00
    "INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R"        : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R,       // 0xa04
    "INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R"       : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R,      // 0xa08
    "INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R"       : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R,      // 0xa0c
    "INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R"   : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R,  // 0xa10
    "INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R"   : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R,  // 0xa14
    "INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R"      : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R,     // 0xa18
    "INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R"   : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R,  // 0xa1c
    "INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R"   : SOCIFC_BASE + `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R,  // 0xa20



  // Check these MASK bits
    "INTR_BLOCK_RF_GLOBAL_INTR_EN_R"                       : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & `SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R,                      // 0x800
    "INTR_BLOCK_RF_ERROR_INTR_EN_R"                        : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R,                       // 0x804
    "INTR_BLOCK_RF_NOTIF_INTR_EN_R"                        : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R,                       // 0x808
    "INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R"                    : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R,                   // 0x80c
    "INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R"                    : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R,                   // 0x810
    "INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R"                  : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R,                 // 0x814
    "INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R"                  : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R,                 // 0x818
    "INTR_BLOCK_RF_ERROR_INTR_TRIG_R"                      : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R,                     // 0x81c
    "INTR_BLOCK_RF_NOTIF_INTR_TRIG_R"                      : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & `SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R,                     // 0x820
 

  // 1-bit count increment
    "INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R"         : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R_PULSE_MASK    
    "INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R"          : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R_PULSE_MASK     
    "INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R"         : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R_PULSE_MASK    
    "INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R"         : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R_PULSE_MASK    
    "INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R"     : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R_PULSE_MASK
    "INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R"     : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R_PULSE_MASK
    "INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R"        : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R_PULSE_MASK   
    "INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R"     : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R_PULSE_MASK
    "INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R"     : exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R_PULSE_MASK
*/


  // Only non-zero power-on values are stored; also populated by SocRegisters instantiation 
  word_addr_t soc_register_initval_dict [string] = {
    "CPTRA_VALID_PAUSER"                   : 32'hffff_ffff,
    "CPTRA_TRNG_VALID_PAUSER"              : 32'hffff_ffff,
    "INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES" : 32'h5
  };

  // holds addr -> name inverse map of soc_register_dict - populated by SocRegisters instantiation 
  string imap_soc_register_dict [word_addr_t]; 

  // Populated by SocRegisters instantiation
  word_addr_t exp_reg_data_dict [string]; 


  // ================================================================================ 
  // Functions 
  // ================================================================================ 

  function int get_ss_code(input string ss_name);

    if (security_state_dict.exists(ss_name)) 
      return int'(security_state_dict[ss_name]);
    else 
      return -1;

  endfunction


  function string get_ss_name(input int ss_code);

    logic [2:0] ss_code_3bit; 

    foreach (security_state_dict[ss_name]) begin
      if (security_state_dict[ss_name] == ss_code[2:0]) 
        return ss_name; 
    end
    return "";

  endfunction


  function int str_startswith(string s1, string s2);

    return (s2 == s1.substr(0, s2.len() - 1));

  endfunction  
  

  function dword_t get_initval(string addr_name);

    return soc_register_initval_dict.exists(addr_name) ? soc_register_initval_dict[addr_name] : '0; 

  endfunction


  function void set_initval(string addr_name, dword_t value); 

    if (soc_register_initval_dict.exists(addr_name))
      soc_register_initval_dict[addr_name] = value;
    
  endfunction




  function void update_exp_regval(word_addr_t addr, dword_t indata, access_t modify);
    // Find out what was attempted to be modified 
    // Look at existing regval
    // Update regval state 
   
    string addr_name;
    dword_t curr_data, exp_data, apb_wr_mask, ahb_wr_mask;

    // NOTE. (apb|ahb)_wr_mask => if set, that particular bit CAN be written over (apb|ahb). 

    string tmpstr; 
    string pauser_suffix; 
    string pauser_lock_regname; 
    int pauser_locked, fuses_locked; 

    dword_t sscode;

    begin

      sscode = soc_register_initval_dict["CPTRA_SECURITY_STATE"];

      if (modify == COLD_RESET) begin
        reset_exp_data();
        return;

      end else if (modify == WARM_RESET) begin
        warm_reset_exp_data();
        return;

      end else if (!imap_soc_register_dict.exists(addr)) begin
        $display ("TB ERROR.  Address 0x%08x not found in inverse address map!", addr);
        return;
      
      end

      addr_name = imap_soc_register_dict[addr];  

      if (modify == SET_DIRECT) begin
        exp_reg_data_dict[addr_name] = indata;
        return;

      end 

      curr_data = exp_reg_data_dict[addr_name];
      apb_wr_mask = {32{(modify == SET_APB)}}; 
      ahb_wr_mask = {32{(modify == SET_AHB)}}; 

      // handle wide registers first, then normal sized ones
      //  RW access => indata & a?b_wr_mask
      //  RO access => curr_data & a?b_wr_mask

      // fuses_locked = (exp_reg_data_dict["CPTRA_FUSE_WR_DONE"]);
      fuses_locked = _fuses_locked; 

      if (str_startswith(addr_name, "FUSE_UDS_SEED"))                    
        exp_data = '0; // not accessible over APB or AHB 

      else if (str_startswith(addr_name, "FUSE_FIELD_ENTROPY"))          
        exp_data = '0; // not accessible over APB or AHB 

      else if ((str_startswith(addr_name, "FUSE_KEY_MANIFEST_PK_HASH"))  && (addr_name != "FUSE_KEY_MANIFEST_PK_HASH_MASK"))
        exp_data = fuses_locked ? curr_data : (indata & apb_wr_mask | curr_data & ahb_wr_mask); // ahb-RO 

      else if (str_startswith(addr_name, "FUSE_OWNER_PK_HASH"))                    
        exp_data = fuses_locked ? curr_data : (indata & apb_wr_mask | curr_data & ahb_wr_mask); // ahb-RO 

      else if (str_startswith(addr_name, "FUSE_RUNTIME_SVN"))
        exp_data = fuses_locked ? curr_data : (indata & apb_wr_mask | curr_data & ahb_wr_mask); // ahb-RO 

      else if (str_startswith(addr_name, "FUSE_IDEVID_CERT_ATTR"))                 
        exp_data = fuses_locked ? curr_data : (indata & apb_wr_mask | curr_data & ahb_wr_mask); // ahb-RO 

      else if (str_startswith(addr_name, "FUSE_IDEVID_MANUF_HSM_ID"))
        exp_data = fuses_locked ? curr_data : (indata & apb_wr_mask | curr_data & ahb_wr_mask); // ahb-RO 

      else if (str_startswith(addr_name, "CPTRA_VALID_PAUSER")) begin    // find equivalent pauser lock & if set, apb-RO 
        tmpstr = "CPTRA_VALID_PAUSER";
        pauser_suffix = addr_name.substr(tmpstr.len(), addr_name.len()-1);
        pauser_lock_regname = {"CPTRA_PAUSER_LOCK", pauser_suffix};
        pauser_locked = exp_reg_data_dict[pauser_lock_regname]; 
        exp_data = indata & ahb_wr_mask | ((pauser_locked ? curr_data : indata) & apb_wr_mask);

      end else if (str_startswith(addr_name, "CPTRA_PAUSER_LOCK")) begin 
        pauser_locked = exp_reg_data_dict[addr_name];
        exp_data = indata & `SOC_IFC_REG_CPTRA_PAUSER_LOCK_0_LOCK_MASK & ahb_wr_mask | 
                  ((pauser_locked ? curr_data : indata) & apb_wr_mask); //  32'h0000_0001; if pauser locked, apb-RO

      end else if (str_startswith(addr_name, "CPTRA_GENERIC_INPUT_WIRES")) 
        exp_data = curr_data; // all bits are RO 

      else if (str_startswith(addr_name, "CPTRA_GENERIC_OUTPUT_WIRES"))  
        exp_data = curr_data & apb_wr_mask | indata & ahb_wr_mask; // all bits are apb-RO 

      else if (str_startswith(addr_name, "INTERNAL_OBF_KEY"))            
        exp_data = '0;  // not accessible over APB or AHB 

      else begin    
        
        case (addr_name)
          "FUSE_ANTI_ROLLBACK_DISABLE"           : exp_data = fuses_locked ? curr_data : (
                                                              indata    & apb_wr_mask & `SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE_DIS_MASK | 
                                                              curr_data & ahb_wr_mask); // 32'h0000_0001; ahb-RO

          "FUSE_KEY_MANIFEST_PK_HASH_MASK"       : exp_data = fuses_locked ? curr_data : ( 
                                                              indata    & apb_wr_mask & `SOC_IFC_REG_FUSE_KEY_MANIFEST_PK_HASH_MASK_MASK_MASK | 
                                                              curr_data & ahb_wr_mask); // 32'h0000_000f; ahb-RO

          "FUSE_FMC_KEY_MANIFEST_SVN"            : exp_data = fuses_locked ? curr_data : ( 
                                                              indata    & apb_wr_mask | curr_data & ahb_wr_mask);  // ahb-RO

          "FUSE_LIFE_CYCLE"                      : exp_data = fuses_locked ? curr_data : (
                                                              indata    & apb_wr_mask & `SOC_IFC_REG_FUSE_LIFE_CYCLE_LIFE_CYCLE_MASK |
                                                              curr_data & ahb_wr_mask); // 32'h0000_0003; // ahb-RO

          "CPTRA_FLOW_STATUS"                    : exp_data = indata    & ahb_wr_mask & (`SOC_IFC_REG_CPTRA_FLOW_STATUS_STATUS_MASK  |
                                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FW_MASK       |
                                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK  |
                                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_MASK    |
                                                                          `SOC_IFC_REG_CPTRA_FLOW_STATUS_MAILBOX_FLOW_DONE_MASK) | 
                                                              curr_data & apb_wr_mask;  //  32'hbfff_ffff; // apb-RO 

          "CPTRA_RESET_REASON"                   : exp_data = curr_data & (`SOC_IFC_REG_CPTRA_RESET_REASON_FW_UPD_RESET_MASK | 
                                                                          `SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK); //  bit 1:0 is apb-RO 

          "CPTRA_SECURITY_STATE"                 : exp_data = curr_data & (`SOC_IFC_REG_CPTRA_SECURITY_STATE_DEVICE_LIFECYCLE_MASK |
                                                                          `SOC_IFC_REG_CPTRA_SECURITY_STATE_DEBUG_LOCKED_MASK      |
                                                                          `SOC_IFC_REG_CPTRA_SECURITY_STATE_SCAN_MODE_MASK) & sscode; //  bit 3:0 is RO 

          "CPTRA_TRNG_VALID_PAUSER" : begin // find equivalent pauser lock & if set, apb-RO 
            pauser_locked = exp_reg_data_dict["CPTRA_TRNG_PAUSER_LOCK"]; 
            exp_data = indata & ahb_wr_mask | ((pauser_locked ? curr_data : indata) & apb_wr_mask);
          end

          "CPTRA_TRNG_PAUSER_LOCK": begin
            // pauser_locked = exp_reg_data_dict["CPTRA_TRNG_PAUSER_LOCK"]; 
            pauser_locked = curr_data & `SOC_IFC_REG_CPTRA_TRNG_PAUSER_LOCK_LOCK_MASK;   // FIXME. Is it?
            exp_data = indata & ahb_wr_mask & `SOC_IFC_REG_CPTRA_TRNG_PAUSER_LOCK_LOCK_MASK  | 
                       (pauser_locked ? curr_data : indata) 
                              & apb_wr_mask & `SOC_IFC_REG_CPTRA_TRNG_PAUSER_LOCK_LOCK_MASK; // 32'h1 
          end

          "CPTRA_TRNG_STATUS"                    :                                                      //                   WR_DONE        REQ
            exp_data = (indata    & `SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_MASK | 
                        curr_data & `SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_REQ_MASK)     & apb_wr_mask |   //  Caliptra Access:      RO         RW
                      (indata     & `SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_REQ_MASK  | 
                        curr_data & `SOC_IFC_REG_CPTRA_TRNG_STATUS_DATA_WR_DONE_MASK) & ahb_wr_mask;    //  SOC Access:           RW         RO

          "CPTRA_FUSE_WR_DONE"                   : exp_data = indata    & apb_wr_mask & `SOC_IFC_REG_CPTRA_FUSE_WR_DONE_DONE_MASK |
                                                              curr_data & ahb_wr_mask; // 32'h0000_0001; 

          "CPTRA_BOOTFSM_GO"                     : exp_data = indata    & apb_wr_mask & `SOC_IFC_REG_CPTRA_BOOTFSM_GO_GO_MASK |
                                                              curr_data & ahb_wr_mask;  // 32'h0000_0001;  // bit 0 is ahb-RO 

          "CPTRA_BOOT_STATUS"                    : exp_data = indata    & ahb_wr_mask | curr_data & apb_wr_mask; // apb-RO

          "CPTRA_CLK_GATING_EN"                  : exp_data = indata    & apb_wr_mask & `SOC_IFC_REG_CPTRA_CLK_GATING_EN_CLK_GATING_EN_MASK |
                                                              curr_data & ahb_wr_mask; // 32'h0000_0001;  

          "INTERNAL_ICCM_LOCK"                   : exp_data = indata    & ahb_wr_mask & `SOC_IFC_REG_INTERNAL_ICCM_LOCK_LOCK_MASK |
                                                              curr_data & apb_wr_mask; // 32'h0000_0001;   apb-RO     

          "INTERNAL_FW_UPDATE_RESET"             : exp_data = indata    & ahb_wr_mask & `SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_CORE_RST_MASK | 
                                                              curr_data & apb_wr_mask; // only bit-0 valid  apb-RO

          "INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES" : exp_data = indata    & ahb_wr_mask & `SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES_WAIT_CYCLES_MASK |  
                                                              curr_data & apb_wr_mask;  // 32'h0000_00ff;  apb-RO 

          "INTERNAL_NMI_VECTOR"                  : exp_data = indata    & ahb_wr_mask | curr_data & apb_wr_mask;  //  all bits are apb-RO 

          default: exp_data = indata;
        endcase

      end 
      exp_reg_data_dict[addr_name] = exp_data;
      // $display ("Expected data for addr_name %s (addr 0x%08x) = 0x%08x", addr_name, addr, exp_data); 
    end

  endfunction // update_exp_regval


  function void warm_reset_exp_data();
    // Unlike reset_exp_data which assumes cold boot, this preserves sticky bits 
    $display ("** Updating expected reg values for warm reset **");
    // <PLACEHOLDER>
    // for stick
  endfunction 


  function strq_t get_fuse_regnames();

    string rkey;
    strq_t fuse_regs; 

    foreach (soc_register_dict[rkey]) begin
      if (rkey.substr(0,3) == "FUSE")
        fuse_regs.push_back(rkey); 
    end 

    return fuse_regs;

  endfunction


  function strq_t get_soc_regnames_minus_fuse();

    string rkey;
    strq_t soc_regs; 

    foreach (soc_register_dict[rkey]) begin
      if (rkey.substr(0,3) != "FUSE")
        soc_regs.push_back(rkey); 
    end 

    return soc_regs;

  endfunction


  function strq_t get_soc_regnames();

    strq_t soc_regs; 

    foreach (soc_register_dict[rkey]) 
      soc_regs.push_back(rkey); 

    return soc_regs;

  endfunction


  function void reset_exp_data();
    // this peforms update for power-on reset

    foreach (soc_register_dict[rname]) 
      exp_reg_data_dict[rname] = get_initval(rname); 

  endfunction 



  // ================================================================================ 
  // Class definitions 
  // ================================================================================ */

  class WordTransaction;

    word_addr_t    addr; 
    rand dword_t   data;
    int            tid;    

    function void update(word_addr_t addr, dword_t data, int tid);    

      this.addr = addr;
      this.data = data;
      this.tid = tid;    

    endfunction 

  
    function void display(); 

      $display("Addr: 0x%08x, Data: 0x%08x, TID: %03d", addr, data, tid); 

    endfunction

    
    function void copy_from(WordTransaction atrans); 

      this.update(atrans.addr, atrans.data, atrans.tid);    

    endfunction 

  endclass // WordTransaction


  // ================================================================================ //
  class SocRegisters;
    
    // once these static vars have been set, assoicated modifier functions should have no effect
    static int widereg_expanded = 0; 
    static int imap_built = 0; 
    // static int fuses_locked = 0; 
    static string security_state_name = "UNDEFINED2"; 

    function new();
      if (!widereg_expanded) begin
        init_regs();
        widereg_expanded = 1;
      end

      if (!imap_built) begin
        build_inverse_addr_map();
        imap_built = 1;
      end 

      reset_exp_data();
    endfunction   


    function lock_fuses();
      // assume over APB or some other means. NOTE that CPTRA_FUSE_WR_DONE 
      // may be set from 1 to 0, which will have no effect on this variable. 
      
      _fuses_locked = 1;  // set this global var for now 

    endfunction   


    function unlock_fuses();
      // unset global var; done over cold boot, warm reset or mailbox command  

      _fuses_locked = 0; 

    endfunction   


    function void build_inverse_addr_map();

      if (imap_built) 
        return;

      foreach (soc_register_dict[tmpstr]) 
        imap_soc_register_dict[soc_register_dict[tmpstr]] = tmpstr;   

    endfunction 


    function void init_regs();
      // The default soc_register_dict only has root addr name-value mappings for 
      // simple 32-bit registers. Wider registers implemented as array need to be 
      // populated w/a function

      word_addr_t start_addr;
      int i;
      string istr;

      if (widereg_expanded) 
        return;

      foreach (wide_register_dict[rname]) begin 
        if (soc_register_dict.exists(rname)) begin 
          start_addr = soc_register_dict[rname];
          for (i = 0; i < wide_register_dict[rname]; i++) begin
            istr.itoa(i);
            soc_register_dict[{rname, istr}] = start_addr + 4*i; 
          end
          soc_register_dict.delete(rname);
        end else 
          $display ("TB ERROR. Soc register and wide register data structures incomplete!");
      end 

      // The same is done for 'reset' values of registers 
      // Names that don't exist in soc_register_initval_dict assume "0" values
      foreach (wide_register_dict[rname]) begin 
        if (soc_register_initval_dict.exists(rname)) begin 
          start_addr = soc_register_initval_dict[rname];
          for (i = 0; i < wide_register_dict[rname]; i++) begin
            istr.itoa(i);
            soc_register_initval_dict[{rname, istr}] = start_addr + 4*i; 
          end
          soc_register_initval_dict.delete(rname);
        end
      end

    endfunction

 
    function word_addr_t get_addr(string name);

      if (soc_register_dict.exists(name))
        return soc_register_dict[name];
      else begin
        $display("TB WARNING. Address %s not found in reg name->addr map. Returning 0", name); 
        return '0; 
      end

    endfunction


    function string get_name(word_addr_t addr);

      if (imap_soc_register_dict.exists(addr))
        return imap_soc_register_dict[addr];
      else begin
        $display("TB WARNING. Address 0x%08x not found in reg addr->name map. Returning empty str", addr); 
        return ""; 
      end

    endfunction


    function void update_security_state(string ssname);

      security_state_name = ssname; 

    endfunction



  endclass // SocRegisters


  // ================================================================================ //
  class RegScoreboard;

    int err_count;
    tidq_t addr_table [word_addr_t];      // store a queue of transactions for each address

    function new();

      string tmpstr;

      begin
        err_count = 0;
      end 
    endfunction


    function void record_reset_values(tid, access_t modify); 
      // useful for reset of all registers 

      word_addr_t addr;
      transaction_t new_trans; 
      dword_t sscode;

      if ((modify != COLD_RESET) && (modify != WARM_RESET)) begin
        $display ("TB ERROR. Mass update of registers unsupported w/access type %s", modify.name());
        return;
      end

      update_exp_regval('0, '0, modify);

      foreach (soc_register_dict[rname]) begin
     
        addr = soc_register_dict[rname];
        new_trans = {addr: addr, data: exp_reg_data_dict[rname], tid: tid};

        if (addr_table.exists(addr)) 
          addr_table[addr].push_back(new_trans); 
        else 
          addr_table[addr] = {new_trans}; 
      end

    endfunction 


    function void record_entry(WordTransaction transaction, access_t modify); 
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

      update_exp_regval(addr, data, modify);
      addr_name = imap_soc_register_dict[addr];
      exp_data = exp_reg_data_dict[addr_name];

      new_trans = {addr: addr, data: exp_data, tid: tid};
      
      if (addr_table.exists(addr)) begin
        // $display ("INFO. Pushing new transaction into existing queue"); 
        addr_table[addr].push_back(new_trans); 
      end else begin
        // $display ("Adding transaction for addr %x", addr);
        addr_table[addr] = {new_trans}; 
      end

    endfunction


    // TODO. Need to implement deletion
    function int check_anddel_entry(WordTransaction transaction);
      // returns cumulative (object.)error count
      // don't check tid if only one transaction

      err_count = check_entry(transaction);
      // Need to check if addr match and tid matched, else not  
      return err_count;

    endfunction


    function int check_entry(WordTransaction transaction);
      // returns cumulative (object.)error count
      // don't check tid if only one transaction

      word_addr_t addr = transaction.addr;
      dword_t data = transaction.data;
      int tid = transaction.tid;

      transaction_t temp_trans; 

      tidq_t qr; 
      int err_found = 0;

      if (!addr_table.exists(addr)) 
        $display ("TB fault. Address %x does not exist", addr);
      else begin
        qr = addr_table[addr];
        if (qr.size() == 0)
          $display ("TB fault. qr size is %d", qr.size()); 
        else if (qr.size() == 1) begin
          temp_trans = qr[0]; 
          err_found = int'(temp_trans.data != data);
        end else begin
          qr = addr_table[addr].find_first with(item.tid == tid); 
          if (qr.size() == 0) 
            $display ("TB fault. No transaction with id %d found", tid);
          else begin
            temp_trans = qr[0];
            err_found = int'(temp_trans.data != data);
          end
        end

        if (err_found) 
            $display("ERROR from Reg Scoreboard for addr = %s(0x%08x); checking data = 0x%08x | expected data = 0x%08x",
              imap_soc_register_dict[addr], addr, data, qr[0].data); 
      end

      err_count += err_found;   
      return err_count;

    endfunction 


    function void del_entry_withtid(word_addr_t addr, int tid);

      int qi [$]; 
      int err_found = 0;

      if (!(addr_table.exists(addr))) begin
        $display("TB WARNING. No addr (0x%08x) found in scoreboard", addr);
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

    endfunction 


    function void del_entry(word_addr_t addr);

      if (addr_table.exists(addr)) 
        addr_table.delete(addr);
      else   
        $display("TB WARNING. No addr (0x%08x) found in scoreboard", addr);

    endfunction 


    function void del_all();

      foreach (addr_table[addr])
        addr_table.delete(addr);

    endfunction 


    function void display_all();      

      int i;
      word_addr_t tmpkey;
      transaction_t tmptrans; 
      tidq_t tmpq; 

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

    endfunction


  endclass // RegScoreboard


endpackage // soc_ifc_tb_pkg

`endif // SOC_IFC_TB_PKG

