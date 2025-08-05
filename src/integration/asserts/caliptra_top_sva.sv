// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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


`include "caliptra_macros.svh"
`include "config_defines.svh"
//`include "kv_defines_pkg.sv"
//`include "doe_defines_pkg.sv"
`ifndef CPTRA_TB_TOP_NAME
  `ifdef UVMF_CALIPTRA_TOP
    `define CPTRA_TB_TOP_NAME hdl_top
  `else
    `define CPTRA_TB_TOP_NAME caliptra_top_tb
  `endif
`endif
`ifndef CPTRA_TOP_PATH
  `define CPTRA_TOP_PATH      `CPTRA_TB_TOP_NAME.caliptra_top_dut
`endif
`define KEYVAULT_PATH       `CPTRA_TOP_PATH.key_vault1
`define KEYVAULT_REG_PATH   `KEYVAULT_PATH.kv_reg1
`define PCRVAULT_PATH       `CPTRA_TOP_PATH.pcr_vault1
`define PCRVAULT_REG_PATH   `PCRVAULT_PATH.pv_reg1
`define DATA_VAULT_PATH     `CPTRA_TOP_PATH.data_vault1
`define DATA_VAULT_REG_PATH `DATA_VAULT_PATH.dv_reg1
`define DOE_INST_PATH       `CPTRA_TOP_PATH.doe.doe_inst
`define DOE_PATH            `DOE_INST_PATH.doe_fsm1
`define DOE_REG_PATH        `DOE_INST_PATH.i_doe_reg
`define SERVICES_PATH       `CPTRA_TB_TOP_NAME.tb_services_i
`define SHA512_PATH         `CPTRA_TOP_PATH.sha512.sha512_inst
`define ABR_PATH            `CPTRA_TOP_PATH.abr_inst.abr_ctrl_inst
`define ABR_REG_PATH        `CPTRA_TOP_PATH.abr_inst.abr_reg_inst
`define HMAC_PATH           `CPTRA_TOP_PATH.hmac.hmac_inst
`define HMAC_REG_PATH       `HMAC_PATH.i_hmac_reg
`define ECC_PATH            `CPTRA_TOP_PATH.ecc_top1.ecc_dsa_ctrl_i
`define ECC_REG_PATH        `CPTRA_TOP_PATH.ecc_top1.ecc_reg1
`define HMAC_DRBG_PATH      `CPTRA_TOP_PATH.ecc_top1.ecc_dsa_ctrl_i.ecc_hmac_drbg_interface_i.hmac_drbg_i
`define SHA256_PATH         `CPTRA_TOP_PATH.sha256.sha256_inst
`define SHA512_MASKED_PATH  `CPTRA_TOP_PATH.ecc_top1.ecc_dsa_ctrl_i.ecc_hmac_drbg_interface_i.hmac_drbg_i.HMAC_K.u_sha512_core_h1
`define SOC_IFC_TOP_PATH    `CPTRA_TOP_PATH.soc_ifc_top1
`define WDT_PATH            `SOC_IFC_TOP_PATH.i_wdt
`define ABR_RAMS_PATH       `SERVICES_PATH.abr_mem_top_inst
`define ABR_TOP_PATH        `CPTRA_TOP_PATH.abr_inst

`define SVA_RDC_CLK `CPTRA_TOP_PATH.rdc_clk_cg
`define CPTRA_FW_UPD_RST_WINDOW `SOC_IFC_TOP_PATH.i_soc_ifc_boot_fsm.fw_update_rst_window
`ifdef UVMF_CALIPTRA_TOP
  `define SVA_CLK `CPTRA_TB_TOP_NAME.clk
  `define SVA_RST `CPTRA_TB_TOP_NAME.soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b
`else
  `define SVA_CLK `CPTRA_TB_TOP_NAME.core_clk
  `define SVA_RST `CPTRA_TB_TOP_NAME.cptra_rst_b
`endif
`define MLDSA_ZEROIZATION   `CPTRA_TOP_PATH.abr_inst.abr_ctrl_inst.abr_reg_hwif_out.MLDSA_CTRL.ZEROIZE.value
`define ABR_SCAN_DEBUG    `CPTRA_TOP_PATH.abr_inst.debugUnlock_or_scan_mode_switch

module caliptra_top_sva
  import doe_defines_pkg::*;
  import kv_defines_pkg::*;
  ();

  //TODO: pass these parameters from their architecture into here
  localparam SHA512_DIG_NUM_DWORDS    = 16;   //`SHA512_PATH.DIG_NUM_DWORDS;
  localparam SHA512_BLOCK_NUM_DWORDS  = 32;   //`SHA512_PATH.BLOCK_NUM_DWORDS;
  localparam MLDSA_SEED_NUM_DWORDS    = 8;   //`ABR_PATH.SEED_NUM_DWORDS;
  localparam HMAC_KEY_NUM_DWORDS      = 12;   //`HMAC_PATH.KEY_NUM_DWORDS
  localparam HMAC_TAG_NUM_DWORDS      = 12;   //`HMAC_PATH.TAG_NUM_DWORDS
  localparam HMAC_BLOCK_NUM_DWORDS    = 32;   //`HMAC_PATH.BLOCK_NUM_DWORDS
  localparam ECC_REG_NUM_DWORDS       = 12;   //'ECC_PATH.REG_NUM_DWORDS
  localparam ECC_MEM_ADDR             = 2**6; //'ECC_PATH.ecc_arith_unit_i.ram_tdp_file_i.mem.ADDR_LENGTH
  localparam SHA256_DIG_NUM_DWORDS    = 8;    //`SHA256_PATH.DIG_NUM_DWORDS;
  localparam SHA256_BLOCK_NUM_DWORDS  = 16;   //`SHA256_PATH.BLOCK_NUM_DWORDS;
  localparam DOE_256_NUM_ROUNDS       = 14;   //`DOE_INST_PATH.i_doe_core_cbc.keymem.DOE_256_NUM_ROUNDS
  localparam SEED_NUM_DWORDS = 8;
  localparam MSG_NUM_DWORDS = 16;
  localparam PRIVKEY_NUM_DWORDS = 1224;
  localparam PRIVKEY_REG_NUM_DWORDS = 32;
  localparam PRIVKEY_REG_RHO_NUM_DWORDS = 8;
  localparam SIGNATURE_H_NUM_DWORDS = 21;
  localparam VERIFY_RES_NUM_DWORDS = 16;
  localparam PRIVKEY_MEM_NUM_DWORDS = PRIVKEY_NUM_DWORDS - PRIVKEY_REG_NUM_DWORDS;
  localparam SIGNATURE_C_NUM_DWORDS = 16;
  localparam SIGNATURE_Z_NUM_DWORDS = 1120;
  localparam SIGNATURE_NUM_DWORDS = SIGNATURE_H_NUM_DWORDS + SIGNATURE_Z_NUM_DWORDS + SIGNATURE_C_NUM_DWORDS;

  localparam MLDSA_REG_RHO_P_NUM_DWORDS = PRIVKEY_REG_RHO_NUM_DWORDS;
  localparam ABR_SCRATCH_REG_NUM_DWORDS = 48;
  localparam MLDSA_ENTROPY_NUM_DWORDS   = 16;
  localparam MLDSA_SIGN_RND_NUM_DWORDS  = 8; 


  //TODO: add disable condition based on doe cmd reg
  DOE_lock_uds_set:        assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (~`SVA_RST)
                                            $rose(`DOE_PATH.flow_done) && $past(doe_cmd_reg_t'(`DOE_PATH.doe_cmd_reg.cmd) == DOE_UDS) |=> `DOE_PATH.lock_uds_flow
                                          )
                            else $display("SVA ERROR: lock_uds_flow was not set after UDS flow");

  //Note: lock + reset checks will use ungated clock. Using RDC clk throws the SVA off in the very first cycle where lock was 0
  //but there's no $past value to compare against. This problem doesn't exist when using ungated clk because in the first cycle,
  //pwrgood is also 0, so SVA is disabled.
  DOE_lock_uds_cold_reset: assert property (
                                            @(posedge `SVA_CLK)
                                            ~`DOE_PATH.hard_rst_b |-> (`DOE_PATH.lock_uds_flow == 0)
                                          )
                            else $display("SVA ERROR: lock_uds_flow was not reset on hard reset");

  DOE_lock_uds_warm_reset: assert property (
                                            @(posedge `SVA_CLK)
                                            disable iff (~`DOE_PATH.rst_b && ~`DOE_PATH.hard_rst_b)
                                            ~`DOE_PATH.rst_b |-> $past(`DOE_PATH.lock_uds_flow) == `DOE_PATH.lock_uds_flow
                                          )
                            else $display("SVA ERROR: lock_uds_flow toggled after warm reset");
  DOE_lock_fe_set:         assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (~`SVA_RST)
                                            $rose(`DOE_PATH.flow_done) && $past(doe_cmd_reg_t'(`DOE_PATH.doe_cmd_reg.cmd) == DOE_FE) |=> `DOE_PATH.lock_fe_flow
                                          )
                            else $display("SVA ERROR: lock_fe_flow was not set after FE flow");

  DOE_lock_fe_cold_reset:    assert property (
                                            @(posedge `SVA_CLK)
                                            ~`DOE_PATH.hard_rst_b |-> (`DOE_PATH.lock_fe_flow == 0)
                                          )
                            else $display("SVA ERROR: lock_fe_flow was not reset on hard reset");

  DOE_lock_fe_warm_reset:    assert property (
                                            @(posedge `SVA_CLK)
                                            disable iff (~`DOE_PATH.rst_b && ~`DOE_PATH.hard_rst_b)
                                            ~`DOE_PATH.rst_b |-> $past(`DOE_PATH.lock_fe_flow) == `DOE_PATH.lock_fe_flow
                                          )
                            else $display("SVA ERROR: lock_fe_flow toggled after warm reset");

  //Corner case: when clear_obf_secrets and reset events happen in the same cycle, reset deassertion will cause SVA to start checking
  //But if clear_obf_secrets was already 1 (not a pulse), it expects to see status valid in the next clk, but in design, it takes an extra
  //cycle to update status. Adding a 1 cycle delay to avoid this case by starting the check when reset is deasserted
  DOE_clear_obf_status_valid: assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (~`DOE_PATH.rst_b)
                                            `CPTRA_TOP_PATH.clear_obf_secrets && `DOE_PATH.rst_b |=> (`DOE_REG_PATH.field_storage.DOE_STATUS.VALID.value && `DOE_REG_PATH.field_storage.DOE_STATUS.DEOBF_SECRETS_CLEARED.value)
                                          )
                            else $display("SVA ERROR: DOE STATUS valid bit not set after clear obf secrets cmd");

  KV_haddr_valid:          assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (~`KEYVAULT_PATH.hsel_i)
                                            `KEYVAULT_PATH.hsel_i |-> !$isunknown(`KEYVAULT_PATH.haddr_i)
                                          )
                            else $display("SVA ERROR: AHB address not valid in keyvault");

  generate 
    for(genvar entry=0; entry < KV_NUM_KEYS; entry++) begin
      for(genvar dword = 0; dword < KV_NUM_DWORDS; dword++) begin
        KV_debug_value0:         assert property (
                                                  @(posedge `SVA_RDC_CLK)
                                                  disable iff(!`KEYVAULT_PATH.cptra_pwrgood)
                                                  $rose(~`CPTRA_TOP_PATH.cptra_security_state_Latched.debug_locked || `SOC_IFC_TOP_PATH.cptra_error_fatal || `CPTRA_TOP_PATH.cptra_scan_mode_Latched) && (`KEYVAULT_PATH.kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value.value == 0) && `KEYVAULT_PATH.cptra_pwrgood |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[entry][dword].data.value == CLP_DEBUG_MODE_KV_0)
                                                )
                                  else $display("SVA ERROR: KV not flushed with correct debug values");

        KV_debug_value1:         assert property (
                                                  @(posedge `SVA_RDC_CLK)
                                                  disable iff(!`KEYVAULT_PATH.cptra_pwrgood)
                                                  $rose(~`CPTRA_TOP_PATH.cptra_security_state_Latched.debug_locked || `SOC_IFC_TOP_PATH.cptra_error_fatal || `CPTRA_TOP_PATH.cptra_scan_mode_Latched) && (`KEYVAULT_PATH.kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value.value == 1) && `KEYVAULT_PATH.cptra_pwrgood |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[entry][dword].data.value == CLP_DEBUG_MODE_KV_1)
                                                )
                                  else $display("SVA ERROR: KV not flushed with correct debug values");
      end
    end
  endgenerate

  generate
    for(genvar dword = 0; dword < KV_NUM_DWORDS; dword++) begin
      if (dword < MLDSA_SEED_NUM_DWORDS) begin
      //mldsa seed read
      kv_mldsa_seed_r_flow:   assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            $rose(`ABR_PATH.kv_mldsa_seed_done) && (dword < (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_CTRL[`ABR_PATH.kv_read[0].read_entry].last_dword.value + 1)) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_read[0].read_entry][dword].data.value == `ABR_PATH.mldsa_seed_reg[(MLDSA_SEED_NUM_DWORDS-1) - dword])
                                            )
                                else $display("SVA ERROR: MLDSA seed mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_read[0].read_entry][dword].data.value, `ABR_PATH.mldsa_seed_reg[(MLDSA_SEED_NUM_DWORDS-1) - dword]);
      end

      //hmac block read
      kv_hmac_block_r_flow:     assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            $rose(`HMAC_PATH.kv_block_done) && (dword < (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_CTRL[`HMAC_PATH.kv_read[1].read_entry].last_dword.value + 1)) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_read[1].read_entry][dword].data.value == `HMAC_PATH.block_reg[dword])
                                            )
                                else $display("SVA ERROR: HMAC384 block mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_read[1].read_entry][dword].data.value, `HMAC_PATH.block_reg[dword]);

      //hmac key read
      if (dword < HMAC_KEY_NUM_DWORDS) begin
        kv_hmac_key_r_flow:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              $fell(`HMAC_PATH.kv_key_write_en) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_read[0].read_entry][dword].data.value == `HMAC_PATH.key_reg[dword])
                                              )
                                  else $display("SVA ERROR: HMAC384 key mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_read[0].read_entry][dword].data.value, `HMAC_PATH.key_reg[dword]);
      end

      //hmac tag write
      if (dword < HMAC_TAG_NUM_DWORDS) begin
        kv_hmac_tag_w_flow:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `HMAC_PATH.kv_write_done |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value == `HMAC_PATH.kv_reg[(`HMAC_PATH.TAG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: HMAC384 tag mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value, `HMAC_PATH.kv_reg[(`HMAC_PATH.TAG_NUM_DWORDS-1) - dword]);                    
      end
      
      // ECC
      if (dword < ECC_REG_NUM_DWORDS) begin
        //ecc privkey read
        kv_ecc_privkey_r_flow:    assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              $fell(`ECC_PATH.kv_privkey_write_en) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_read[0].read_entry][dword].data.value == `ECC_PATH.privkey_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: ECC privkey read mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_read[0].read_entry][dword].data.value, `ECC_PATH.privkey_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword]);
        kv_ecc_seed_r_flow:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              $fell(`ECC_PATH.kv_seed_write_en) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_read[1].read_entry][dword].data.value == `ECC_PATH.seed_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: ECC seed mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_read[1].read_entry][dword].data.value, `ECC_PATH.seed_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword]);
        //ecc privkey write
        kv_ecc_privkey_w_flow:    assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `ECC_PATH.kv_write_done |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value == `ECC_PATH.kv_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: ECC privkey write mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value, `ECC_PATH.kv_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword]);

        //ecc sign r
        pcr_ecc_sign_r:    assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `SERVICES_PATH.check_pcr_ecc_signing |-> (`SERVICES_PATH.ecc_test_vector.R[dword] == `ECC_PATH.hwif_out.ECC_SIGN_R[dword].SIGN_R.value)
                                              )
                                  else $display("SVA ERROR: PCR SIGNING SIGN_R mismatch!, 0x%04x, 0x%04x", `SERVICES_PATH.ecc_test_vector.R[dword], `ECC_PATH.hwif_out.ECC_SIGN_R[dword].SIGN_R.value);                     
        
        //ecc sign s
        pcr_ecc_sign_s:    assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `SERVICES_PATH.check_pcr_ecc_signing |-> (`SERVICES_PATH.ecc_test_vector.S[dword] == `ECC_PATH.hwif_out.ECC_SIGN_S[dword].SIGN_S.value)
                                              )
                                  else $display("SVA ERROR: PCR SIGNING SIGN_S mismatch!, 0x%04x, 0x%04x", `SERVICES_PATH.ecc_test_vector.S[dword], `ECC_PATH.hwif_out.ECC_SIGN_S[dword].SIGN_S.value); 
      end
    end
  endgenerate

  `ifndef VERILATOR
  generate
    begin: SHA256_WNTZ_data_check
      for(genvar dword = 0; dword < 8; dword++) begin
        SHA256_WNTZ_data_check: assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            //disable iff (`CPTRA_TOP_PATH.)
                                            (`SERVICES_PATH.WriteData == 'hdd && `SERVICES_PATH.mailbox_write) |=> ##[1:$] $rose(`SHA256_PATH.digest_valid_reg) |=> (`SHA256_PATH.digest_reg[dword] == `SERVICES_PATH.sha256_wntz_test_vector.sha256_wntz_digest[dword])
                                          )
                                  else $display("SVA ERROR: SHA256 wntz digest %h does not match expected digest %h!", `SHA256_PATH.digest_reg[dword], `SERVICES_PATH.sha256_wntz_test_vector.sha256_wntz_digest[dword]);
      end //for
    end //data check
  endgenerate

  generate
    begin: UDS_data_check
    for(genvar dword = 0; dword < `CLP_OBF_UDS_DWORDS; dword++) begin
      DOE_UDS_data_check:  assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (`CPTRA_TOP_PATH.scan_mode || !`CPTRA_TOP_PATH.security_state.debug_locked)
                                            (`SERVICES_PATH.WriteData == 'hEC && `SERVICES_PATH.mailbox_write) |=> ##[1:$] $rose(`DOE_PATH.lock_uds_flow) |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword].data.value == `SERVICES_PATH.doe_test_vector.uds_plaintext[dword])
                                
                                          )
                                  else $display("SVA ERROR: DOE UDS output %h does not match plaintext %h!", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword].data.value, `SERVICES_PATH.doe_test_vector.uds_plaintext[dword]);
    end
    end
  endgenerate
  generate
    begin: FE_data_check
    for(genvar dword = 0; dword < `CLP_OBF_FE_DWORDS; dword++) begin
  
      DOE_FE_data_check:   assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (`CPTRA_TOP_PATH.scan_mode || !`CPTRA_TOP_PATH.security_state.debug_locked)
                                            (`SERVICES_PATH.WriteData == 'hED && `SERVICES_PATH.mailbox_write) |=> ##[1:$] $rose(`DOE_PATH.lock_fe_flow) |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword].data.value == `SERVICES_PATH.doe_test_vector.fe_plaintext[dword])
                                          )
                                  else $display("SVA ERROR: DOE FE output %h does not match plaintext %h!", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword].data.value, `SERVICES_PATH.doe_test_vector.fe_plaintext[dword]);

    end
    end
  endgenerate
  `endif

  `ifndef VERILATOR
  //MLDSA data checks
  generate
    begin: MLDSA_keygen_data_check
      for (genvar dword = 0; dword < PRIVKEY_REG_NUM_DWORDS; dword++) begin
        MLDSA_privkey_0_31_data_check: assert property (
            @(posedge `SVA_RDC_CLK)
            disable iff (`CPTRA_TOP_PATH.scan_mode || !`CPTRA_TOP_PATH.security_state.debug_locked)
            (((`SERVICES_PATH.mldsa_keygen || `SERVICES_PATH.mldsa_keygen_signing) && `ABR_PATH.abr_status_done) |=> (`ABR_PATH.abr_scratch_reg.raw[dword] == {`SERVICES_PATH.mldsa_test_vector.privkey[dword][7:0], `SERVICES_PATH.mldsa_test_vector.privkey[dword][15:8], `SERVICES_PATH.mldsa_test_vector.privkey[dword][23:16], `SERVICES_PATH.mldsa_test_vector.privkey[dword][31:24]}))
        )
        else $display("SVA ERROR: [MLDSA keygen] SK output %h does not match expected SK %h at index %h",`ABR_PATH.abr_scratch_reg.raw[dword], {`SERVICES_PATH.mldsa_test_vector.privkey[dword][7:0], `SERVICES_PATH.mldsa_test_vector.privkey[dword][15:8], `SERVICES_PATH.mldsa_test_vector.privkey[dword][23:16], `SERVICES_PATH.mldsa_test_vector.privkey[dword][31:24]}, dword);
      end

      for (genvar dword = 0; dword < PRIVKEY_MEM_NUM_DWORDS/2; dword++) begin
        MLDSA_privkey_even_data_check: assert property (
            @(posedge `SVA_RDC_CLK)
            disable iff (`CPTRA_TOP_PATH.scan_mode || !`CPTRA_TOP_PATH.security_state.debug_locked)
            (((`SERVICES_PATH.mldsa_keygen || `SERVICES_PATH.mldsa_keygen_signing) && `ABR_PATH.abr_status_done) |=> (`ABR_RAMS_PATH.mldsa_sk_mem_bank0_inst.ram[dword] == {`SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+(2*dword)][7:0], `SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+(2*dword)][15:8], `SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+(2*dword)][23:16], `SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+(2*dword)][31:24]}))
        )
        else $display("SVA ERROR: [MLDSA keygen] SK output %h does not match expected SK %h at index %h",`ABR_RAMS_PATH.mldsa_sk_mem_bank0_inst.ram[dword], {`SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+(2*dword)][7:0], `SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+(2*dword)][15:8], `SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+(2*dword)][23:16], `SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+(2*dword)][31:24]}, PRIVKEY_REG_NUM_DWORDS+(2*dword));
      end

      for (genvar dword = 0; dword < PRIVKEY_MEM_NUM_DWORDS/2; dword++) begin
        MLDSA_privkey_odd_data_check: assert property (
            @(posedge `SVA_RDC_CLK)
            disable iff (`CPTRA_TOP_PATH.scan_mode || !`CPTRA_TOP_PATH.security_state.debug_locked)
            (((`SERVICES_PATH.mldsa_keygen || `SERVICES_PATH.mldsa_keygen_signing) && `ABR_PATH.abr_status_done) |=> (`ABR_RAMS_PATH.mldsa_sk_mem_bank1_inst.ram[dword] == {`SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+1+(2*dword)][7:0], `SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+1+(2*dword)][15:8], `SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+1+(2*dword)][23:16], `SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+1+(2*dword)][31:24]}))
        )
        else $display("SVA ERROR: [MLDSA keygen] SK output %h does not match expected SK %h at index %h",`ABR_RAMS_PATH.mldsa_sk_mem_bank1_inst.ram[dword], {`SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+1+(2*dword)][7:0], `SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+1+(2*dword)][15:8], `SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+1+(2*dword)][23:16], `SERVICES_PATH.mldsa_test_vector.privkey[PRIVKEY_REG_NUM_DWORDS+1+(2*dword)][31:24]}, PRIVKEY_REG_NUM_DWORDS+1+(2*dword));
      end

      for (genvar dword = 0; dword < 8; dword++) begin
        MLDSA_pubkey_0_7_data_check: assert property (
          @(posedge `SVA_RDC_CLK)
          disable iff (`CPTRA_TOP_PATH.scan_mode || !`CPTRA_TOP_PATH.security_state.debug_locked)
          (((`SERVICES_PATH.mldsa_keygen || `SERVICES_PATH.mldsa_keygen_signing) && `ABR_PATH.abr_status_done) |=> (`ABR_PATH.abr_scratch_reg.raw[dword] == {`SERVICES_PATH.mldsa_test_vector.pubkey[dword][7:0], `SERVICES_PATH.mldsa_test_vector.pubkey[dword][15:8], `SERVICES_PATH.mldsa_test_vector.pubkey[dword][23:16], `SERVICES_PATH.mldsa_test_vector.pubkey[dword][31:24]}))
        )
        else $display("SVA ERROR: [MLDSA keygen] PK output %h does not match expected PK %h at index %h", `ABR_PATH.abr_scratch_reg.raw[dword], {`SERVICES_PATH.mldsa_test_vector.pubkey[dword][7:0], `SERVICES_PATH.mldsa_test_vector.pubkey[dword][15:8], `SERVICES_PATH.mldsa_test_vector.pubkey[dword][23:16], `SERVICES_PATH.mldsa_test_vector.pubkey[dword][31:24]}, dword);
      end
    end
  endgenerate
  generate
    begin: MLDSA_pubkey_data_check
      for (genvar i = 0; i < 64; i++) begin
        for (genvar j = 0; j < 10; j++) begin
          MLDSA_pubkey_8_647_data_check: assert property (
            @(posedge `SVA_RDC_CLK)
            disable iff (`CPTRA_TOP_PATH.scan_mode || !`CPTRA_TOP_PATH.security_state.debug_locked)
            (((`SERVICES_PATH.mldsa_keygen || `SERVICES_PATH.mldsa_keygen_signing) && `ABR_PATH.abr_status_done) |=> (`ABR_RAMS_PATH.mldsa_pk_mem_inst.ram[i][j*4+3:j*4] == {`SERVICES_PATH.mldsa_test_vector.pubkey[i*10+8+j][7:0], `SERVICES_PATH.mldsa_test_vector.pubkey[i*10+8+j][15:8], `SERVICES_PATH.mldsa_test_vector.pubkey[i*10+8+j][23:16], `SERVICES_PATH.mldsa_test_vector.pubkey[i*10+8+j][31:24]}))
          )
          else $display("SVA ERROR: [MLDSA keygen] PK output %h does not match expected PK %h at index %0d %0d", `ABR_RAMS_PATH.mldsa_pk_mem_inst.ram[i][j*4+3:j*4], {`SERVICES_PATH.mldsa_test_vector.pubkey[i*10+8+j][7:0], `SERVICES_PATH.mldsa_test_vector.pubkey[i*10+8+j][15:8], `SERVICES_PATH.mldsa_test_vector.pubkey[i*10+8+j][23:16], `SERVICES_PATH.mldsa_test_vector.pubkey[i*10+8+j][31:24]}, i, j);
        end
      end
    end
  endgenerate
  generate
    begin: MLDSA_signature_data_check
      for (genvar dword = 0; dword < SIGNATURE_H_NUM_DWORDS; dword++) begin
        MLDSA_signature_16_36_data_check: assert property (
            @(posedge `SVA_RDC_CLK)
            disable iff (`CPTRA_TOP_PATH.scan_mode || !`CPTRA_TOP_PATH.security_state.debug_locked || `SERVICES_PATH.disable_mldsa_sva)
            (((`SERVICES_PATH.mldsa_signing || `SERVICES_PATH.mldsa_keygen_signing) && `ABR_PATH.abr_status_done) |=> (`ABR_PATH.signature_reg.raw[SIGNATURE_C_NUM_DWORDS+dword] == {`SERVICES_PATH.mldsa_test_vector.signature[(SIGNATURE_NUM_DWORDS-1)-((SIGNATURE_H_NUM_DWORDS-1)-dword)][7:0], `SERVICES_PATH.mldsa_test_vector.signature[(SIGNATURE_NUM_DWORDS-1)-((SIGNATURE_H_NUM_DWORDS-1)-dword)][15:8], `SERVICES_PATH.mldsa_test_vector.signature[(SIGNATURE_NUM_DWORDS-1)-((SIGNATURE_H_NUM_DWORDS-1)-dword)][23:16], `SERVICES_PATH.mldsa_test_vector.signature[(SIGNATURE_NUM_DWORDS-1)-((SIGNATURE_H_NUM_DWORDS-1)-dword)][31:24]}))
        )
        else $display("SVA ERROR: [MLDSA signing] Signature output %h does not match expected signature %h at index %h",`ABR_PATH.signature_reg.raw[SIGNATURE_C_NUM_DWORDS+dword], {`SERVICES_PATH.mldsa_test_vector.signature[(SIGNATURE_NUM_DWORDS-1)-((SIGNATURE_H_NUM_DWORDS-1)-dword)][7:0], `SERVICES_PATH.mldsa_test_vector.signature[(SIGNATURE_NUM_DWORDS-1)-((SIGNATURE_H_NUM_DWORDS-1)-dword)][15:8], `SERVICES_PATH.mldsa_test_vector.signature[(SIGNATURE_NUM_DWORDS-1)-((SIGNATURE_H_NUM_DWORDS-1)-dword)][23:16], `SERVICES_PATH.mldsa_test_vector.signature[(SIGNATURE_NUM_DWORDS-1)-((SIGNATURE_H_NUM_DWORDS-1)-dword)][31:24]}, SIGNATURE_C_NUM_DWORDS+dword);
      end

      for (genvar dword = 0; dword < SIGNATURE_C_NUM_DWORDS; dword++) begin
        MLDSA_signature_0_15_data_check: assert property (
            @(posedge `SVA_RDC_CLK)
            disable iff (`CPTRA_TOP_PATH.scan_mode || !`CPTRA_TOP_PATH.security_state.debug_locked || `SERVICES_PATH.disable_mldsa_sva)
            (((`SERVICES_PATH.mldsa_signing || `SERVICES_PATH.mldsa_keygen_signing) && `ABR_PATH.abr_status_done) |=> (`ABR_PATH.signature_reg.raw[dword] == {`SERVICES_PATH.mldsa_test_vector.signature[dword][7:0], `SERVICES_PATH.mldsa_test_vector.signature[dword][15:8], `SERVICES_PATH.mldsa_test_vector.signature[dword][23:16], `SERVICES_PATH.mldsa_test_vector.signature[dword][31:24]}))
        )
        else $display("SVA ERROR: [MLDSA signing] Signature output %h does not match expected signature %h at index %h",`ABR_PATH.signature_reg.raw[dword], {`SERVICES_PATH.mldsa_test_vector.signature[dword][7:0], `SERVICES_PATH.mldsa_test_vector.signature[dword][15:8], `SERVICES_PATH.mldsa_test_vector.signature[dword][23:16], `SERVICES_PATH.mldsa_test_vector.signature[dword][31:24]}, dword);
      end
    end
  endgenerate
  generate
    begin: MLDSA_sig_z_data_check
      for (genvar i = 0; i < 224; i++) begin
        for (genvar j = 0; j < 5; j++) begin
          MLDSA_sig_37_1135_data_check: assert property (
            @(posedge `SVA_RDC_CLK)
            disable iff (`CPTRA_TOP_PATH.scan_mode || !`CPTRA_TOP_PATH.security_state.debug_locked || `SERVICES_PATH.disable_mldsa_sva)
            (((`SERVICES_PATH.mldsa_signing || `SERVICES_PATH.mldsa_keygen_signing) && `ABR_PATH.abr_status_done) |=> (`ABR_RAMS_PATH.mldsa_sig_z_mem_inst.ram[i][j*4+3:j*4] == {`SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][7:0], `SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][15:8], `SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][23:16], `SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][31:24]}))
          )
          else $display("SVA ERROR: [MLDSA signing] Sig output %h does not match expected sig %h at index %0d %0d", `ABR_RAMS_PATH.mldsa_sig_z_mem_inst.ram[i][j*4+3:j*4], {`SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][7:0], `SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][15:8], `SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][23:16], `SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][31:24]}, i, j);
        end
      end
    end
  endgenerate
  generate
    begin: MLDSA_verify_data_check
      for (genvar dword = 0; dword < VERIFY_RES_NUM_DWORDS; dword++) begin
        MLDSA_verify_res_data_check: assert property (
            @(posedge `SVA_RDC_CLK)
            disable iff (`CPTRA_TOP_PATH.scan_mode || !`CPTRA_TOP_PATH.security_state.debug_locked)
            ((`SERVICES_PATH.mldsa_verify && `ABR_PATH.abr_status_done) |=> (`ABR_REG_PATH.hwif_out.MLDSA_VERIFY_RES[dword] == {`SERVICES_PATH.mldsa_test_vector.verify_res[(VERIFY_RES_NUM_DWORDS-1)-dword][7:0], `SERVICES_PATH.mldsa_test_vector.verify_res[(VERIFY_RES_NUM_DWORDS-1)-dword][15:8], `SERVICES_PATH.mldsa_test_vector.verify_res[(VERIFY_RES_NUM_DWORDS-1)-dword][23:16], `SERVICES_PATH.mldsa_test_vector.verify_res[(VERIFY_RES_NUM_DWORDS-1)-dword][31:24]}))
        )
        else $display("SVA ERROR: [MLDSA verify] Verify output %h does not match expected verify res %h at index %h",`ABR_REG_PATH.hwif_out.MLDSA_VERIFY_RES[dword], {`SERVICES_PATH.mldsa_test_vector.verify_res[(VERIFY_RES_NUM_DWORDS-1)-dword][7:0], `SERVICES_PATH.mldsa_test_vector.verify_res[(VERIFY_RES_NUM_DWORDS-1)-dword][15:8], `SERVICES_PATH.mldsa_test_vector.verify_res[(VERIFY_RES_NUM_DWORDS-1)-dword][23:16], `SERVICES_PATH.mldsa_test_vector.verify_res[(VERIFY_RES_NUM_DWORDS-1)-dword][31:24]}, dword);
      end
    end
  endgenerate

  generate
    begin: PCR_MLDSA_Signing
      //MLDSA_signature_data_check
      for (genvar dword = 0; dword < SIGNATURE_C_NUM_DWORDS; dword++) begin
        PCR_MLDSA_signature_0_15_data_check: assert property (
            @(posedge `SVA_RDC_CLK)
            (`SERVICES_PATH.check_pcr_mldsa_signing |->  (`ABR_PATH.signature_reg.enc.c[dword] == {`SERVICES_PATH.mldsa_test_vector.signature[dword][7:0], `SERVICES_PATH.mldsa_test_vector.signature[dword][15:8], `SERVICES_PATH.mldsa_test_vector.signature[dword][23:16], `SERVICES_PATH.mldsa_test_vector.signature[dword][31:24]}))
        )
        else $display("SVA ERROR: [PCR MLDSA signing] Signature output %h does not match expected signature %h at index %h",`ABR_PATH.signature_reg.enc.c[dword], {`SERVICES_PATH.mldsa_test_vector.signature[dword][7:0], `SERVICES_PATH.mldsa_test_vector.signature[dword][15:8], `SERVICES_PATH.mldsa_test_vector.signature[dword][23:16], `SERVICES_PATH.mldsa_test_vector.signature[dword][31:24]}, dword);
      end

      for (genvar dword = 0; dword < SIGNATURE_H_NUM_DWORDS; dword++) begin
        PCR_MLDSA_signature_16_36_data_check: assert property (
            @(posedge `SVA_RDC_CLK)
            (`SERVICES_PATH.check_pcr_mldsa_signing |-> (`ABR_PATH.signature_reg.enc.h[dword] == {`SERVICES_PATH.mldsa_test_vector.signature[SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS+dword][7:0], `SERVICES_PATH.mldsa_test_vector.signature[SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS+dword][15:8], `SERVICES_PATH.mldsa_test_vector.signature[SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS+dword][23:16], `SERVICES_PATH.mldsa_test_vector.signature[SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS+dword][31:24]}))
        )
        else $display("SVA ERROR: [PCR MLDSA signing] Signature output %h does not match expected signature %h at index %h",`ABR_PATH.signature_reg.enc.h[dword], {`SERVICES_PATH.mldsa_test_vector.signature[SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS+dword][7:0], `SERVICES_PATH.mldsa_test_vector.signature[SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS+dword][15:8], `SERVICES_PATH.mldsa_test_vector.signature[SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS+dword][23:16], `SERVICES_PATH.mldsa_test_vector.signature[SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS+dword][31:24]}, SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS+dword);
      end

     //MLDSA_sig_z_data_check
      for (genvar i = 0; i < 224; i++) begin
        for (genvar j = 0; j < 5; j++) begin
          PCR_MLDSA_sig_37_1135_data_check: assert property (
            @(posedge `SVA_RDC_CLK)
           (`SERVICES_PATH.check_pcr_mldsa_signing |-> (`ABR_RAMS_PATH.mldsa_sig_z_mem_inst.ram[i][j*4+3:j*4] == {`SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][7:0], `SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][15:8], `SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][23:16], `SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][31:24]}))
          )
          else $display("SVA ERROR: [PCR MLDSA signing] Sig output %h does not match expected sig %h at index %0d %0d", `ABR_RAMS_PATH.mldsa_sig_z_mem_inst.ram[i][j*4+3:j*4], {`SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][7:0], `SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][15:8], `SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][23:16], `SERVICES_PATH.mldsa_test_vector.signature[i*5+16+j][31:24]}, i, j);
        end
      end
    end
  endgenerate
  // MLDSA Scan, Debug and Zeroization Assertions
  generate
    // Check abr_scratch_reg (accessed via its raw field) word-by-word using MLDSA_PRIVKEY_REG_NUM_DWORDS
    for (genvar i = 0; i < ABR_SCRATCH_REG_NUM_DWORDS; i++) begin: privkey_check
      ZERO_MLDSA_K_scratch_reg_check: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##1 (`ABR_PATH.abr_scratch_reg.raw[i] == 0))
      )
      else $display("SVA ERROR: ABR_PATH.abr_scratch_reg.raw[%0d] is not zero", i);
    end

    ZERO_MLDSA_priv_key_rd_port: assert property (
      @(posedge `SVA_RDC_CLK)
      ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##1 (`ABR_PATH.api_reg_rdata == 0))
    )
    else $display("SVA ERROR: ABR_PATH.api_reg_rdata is not zero");

    // Check seed_reg word-by-word using MLDSA_SEED_NUM_DWORDS
    for (genvar i = 0; i < MLDSA_SEED_NUM_DWORDS; i++) begin: seed_check
      ZERO_MLDSA_seed_reg: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##1 (`ABR_PATH.mldsa_seed_reg[i] == 0))
      )
      else $display("SVA ERROR: ABR_PATH.mldsa_seed_reg[%0d] is not zero", i);
    end

    // Check entropy_reg word-by-word using MLDSA_ENTROPY_NUM_DWORDS
    for (genvar i = 0; i < MLDSA_ENTROPY_NUM_DWORDS; i++) begin: entropy_check
      ZERO_MLDSA_entropy_reg: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##1 (`ABR_PATH.entropy_reg[i] == 0))
      )
      else $display("SVA ERROR: ABR_PATH.entropy_reg[%0d] is not zero", i);
    end

    // Check sign_rnd_reg word-by-word using MLDSA_SIGN_RND_NUM_DWORDS
    for (genvar i = 0; i < MLDSA_SIGN_RND_NUM_DWORDS; i++) begin: sign_rnd_check
      ZERO_MLDSA_sign_rnd_reg: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##1 (`ABR_PATH.sign_rnd_reg[i] == 0))
      )
      else $display("SVA ERROR: ABR_PATH.sign_rnd_reg[%0d] is not zero", i);
    end

  endgenerate
  // ABR_TOP_PATH Memory Interface Zeroization Assertions
  generate
    // skencode_mem_rd_data: 2-element array of MLDSA_MEM_DATA_WIDTH bits each.
    for (genvar i = 0; i < 2; i++) begin: skencode_mem_rd_data_check
      ZERO_MLDSA_skencode_mem_rd_data: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##4 (`ABR_TOP_PATH.skencode_mem_rd_data[i] == 0))
      )
      else $display("SVA ERROR: ABR_TOP_PATH.skencode_mem_rd_data[%0d] is not zero", i);
    end
    // skencode_wr_data: Single vector of DATA_WIDTH bits.
    ZERO_MLDSA_skencode_wr_data: assert property (
      @(posedge `SVA_RDC_CLK)
      ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##1 (`ABR_TOP_PATH.skencode_wr_data == 0))
    )
    else $display("SVA ERROR: ABR_TOP_PATH.skencode_wr_data is not zero");

    // skdecode_mem_wr_data: 2-element array of MLDSA_MEM_DATA_WIDTH bits each.
    for (genvar i = 0; i < 2; i++) begin: skdecode_mem_wr_data_check
      ZERO_MLDSA_skdecode_mem_wr_data: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##1 (`ABR_TOP_PATH.skdecode_mem_wr_data[i] == 0))
      )
      else $display("SVA ERROR: ABR_TOP_PATH.skdecode_mem_wr_data[%0d] is not zero", i);
    end

    // skdecode_rd_data: 2-element array of DATA_WIDTH bits each.
    for (genvar i = 0; i < 2; i++) begin: skdecode_rd_data_check
      ZERO_MLDSA_skdecode_rd_data: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##4 (`ABR_TOP_PATH.skdecode_rd_data[i] == 0))
      )
      else $display("SVA ERROR: ABR_TOP_PATH.skdecode_rd_data[%0d] is not zero", i);
    end

    // abr_mem_rdata0_bank: 2-element array of MLDSA_MEM_DATA_WIDTH bits.
    for (genvar i = 0; i < 2; i++) begin: abr_mem_rdata0_bank_check
      ZERO_MLDSA_abr_mem_rdata0_bank: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##3 (`ABR_TOP_PATH.abr_mem_rdata0_bank[i] == 0))
      )
      else $display("SVA ERROR: ABR_TOP_PATH.abr_mem_rdata0_bank[%0d] is not zero", i);
    end

    // abr_mem_wdata: Array indexed from 1 to 3, each element is MLDSA_MEM_DATA_WIDTH bits.
    for (genvar i = 1; i < 3; i++) begin: abr_mem_wdata_check
      ZERO_MLDSA_abr_mem_wdata: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##1 (`ABR_TOP_PATH.abr_mem_wdata[i] == 0))
      )
      else $display("SVA ERROR: ABR_TOP_PATH.abr_mem_wdata[%0d] is not zero", i);
    end

    // abr_mem_wdata: Array indexed from 1 to 3, each element is MLDSA_MEM_DATA_WIDTH bits.
    for (genvar i = 3; i <= 3; i++) begin: abr_mem_masked_wdata_check
      ZERO_MLDSA_abr_mem_wdata: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##1 (`ABR_TOP_PATH.abr_mem_masked_wdata[i] == 0))
      )
      else $display("SVA ERROR: ABR_TOP_PATH.abr_mem_wdata[%0d] is not zero", i);
    end

    // abr_mem_wdata0_bank: 2-element array of MLDSA_MEM_DATA_WIDTH bits.
    for (genvar i = 0; i < 2; i++) begin: abr_mem_wdata0_bank_check
      ZERO_MLDSA_abr_mem_wdata0_bank: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##4 (`ABR_TOP_PATH.abr_mem_wdata0_bank[i] == 0))
      )
      else $display("SVA ERROR: ABR_TOP_PATH.abr_mem_wdata0_bank[%0d] is not zero", i);
    end
  endgenerate
  generate
    begin: MLDSA_mem_zeroize_check
      // Check bank0 memory: even addresses from the private key memory
      for (genvar dword = 0; dword < PRIVKEY_MEM_NUM_DWORDS/2; dword++) begin: bank0_zero_check
        ZERO_MLDSA_sk_mem_bank0_zero: assert property (
            @(posedge `SVA_RDC_CLK)
            $rose(`ABR_PATH.zeroize_mem_done) |-> 
            (`ABR_RAMS_PATH.mldsa_sk_mem_bank0_inst.ram[dword] == 0)
        )
        else $display("SVA ERROR: [MLDSA zeroize] SK bank0 at index %0d is not zero", dword);
      end
  
      // Check bank1 memory: odd addresses from the private key memory
      for (genvar dword = 0; dword < PRIVKEY_MEM_NUM_DWORDS/2; dword++) begin: bank1_zero_check
        ZERO_MLDSA_sk_mem_bank1_zero: assert property (
            @(posedge `SVA_RDC_CLK)
            $rose(`ABR_PATH.zeroize_mem_done) |-> 
            (`ABR_RAMS_PATH.mldsa_sk_mem_bank1_inst.ram[dword] == 0)
        )
        else $display("SVA ERROR: [MLDSA zeroize] SK bank1 at index %0d is not zero", dword);
      end

      // Assertion to check that `ABR_PATH.zeroize_mem_done` transitions from low to high 
      // when (`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) is active
      ZEROIZE_MEM_DONE_TRANSITION: assert property (
        @(posedge `SVA_RDC_CLK)
        (`MLDSA_ZEROIZATION || `ABR_SCAN_DEBUG) |=> 
        ( !`ABR_PATH.zeroize_mem_done )[*0:$] ##1 
        $rose(`ABR_PATH.zeroize_mem_done)
      )
      else $display("SVA ERROR: [MLDSA zeroize] zeroize_mem_done did not rise when expected");

    end
  endgenerate

  


  `endif
  //Generate disable signal for fuse_wr_check sva when hwclr is asserted. The disable needs to be for 3 clks in order to ignore the fuses being cleared
  logic clear_obf_secrets_f;
  logic clear_obf_secrets_ff;
  logic clear_obf_secrets_int;

  logic cptra_in_debug_scan_mode_f;
  logic cptra_in_debug_scan_mode_fall_trans;
  logic cptra_in_debug_scan_mode_fall_trans_f;
  logic cptra_in_debug_scan_mode_int;

  always@(posedge `SVA_RDC_CLK or negedge `CPTRA_TOP_PATH.cptra_rst_b) begin
    if(!`CPTRA_TOP_PATH.cptra_rst_b) begin
      clear_obf_secrets_f <= 'b0;
      clear_obf_secrets_ff <= 'b0;
    end
    else begin
      clear_obf_secrets_f <= `SOC_IFC_TOP_PATH.clear_obf_secrets;
      clear_obf_secrets_ff <= clear_obf_secrets_f;
    end
  end

  always@(posedge `SVA_RDC_CLK or negedge `CPTRA_TOP_PATH.cptra_rst_b) begin
    if(!`CPTRA_TOP_PATH.cptra_rst_b) begin
      cptra_in_debug_scan_mode_f <= 'b0;
      cptra_in_debug_scan_mode_fall_trans_f <= 'b0;
    end
    else begin
      cptra_in_debug_scan_mode_f <= `CPTRA_TOP_PATH.cptra_in_debug_scan_mode;
      cptra_in_debug_scan_mode_fall_trans_f <= cptra_in_debug_scan_mode_fall_trans;
    end
  end

  assign clear_obf_secrets_int = `SOC_IFC_TOP_PATH.clear_obf_secrets | clear_obf_secrets_f | clear_obf_secrets_ff;
  assign cptra_in_debug_scan_mode_fall_trans = !`CPTRA_TOP_PATH.cptra_in_debug_scan_mode && cptra_in_debug_scan_mode_f;
  assign cptra_in_debug_scan_mode_int = cptra_in_debug_scan_mode_fall_trans | cptra_in_debug_scan_mode_fall_trans_f;

  UDS_fuse_wr_check: assert property (
                                  @(posedge `SVA_RDC_CLK)
                                  disable iff(`CPTRA_TOP_PATH.cptra_in_debug_scan_mode || clear_obf_secrets_int || cptra_in_debug_scan_mode_int)
                                  (`SOC_IFC_TOP_PATH.soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value) |-> `CPTRA_TOP_PATH.obf_uds_seed == $past(`CPTRA_TOP_PATH.obf_uds_seed)
  )
  else $display("SVA ERROR: Unexpected write to obf uds seed!");

  FE_fuse_wr_check: assert property (
                                  @(posedge `SVA_RDC_CLK)
                                  disable iff(`CPTRA_TOP_PATH.cptra_in_debug_scan_mode || clear_obf_secrets_int || cptra_in_debug_scan_mode_int)
                                  (`SOC_IFC_TOP_PATH.soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value) |-> `CPTRA_TOP_PATH.obf_field_entropy == $past(`CPTRA_TOP_PATH.obf_field_entropy)
  )
  else $display("SVA ERROR: Unexpected write to obf field entropy!");

  //ZEROIZE SVA
  generate
    for(genvar dword = 0; dword < SHA256_BLOCK_NUM_DWORDS; dword++) begin
        sha256_block_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `SHA256_PATH.hwif_out.SHA256_CTRL.ZEROIZE.value |=> (`SHA256_PATH.hwif_out.SHA256_BLOCK[dword].BLOCK.value == 0)
                                              )
                                  else $display("SVA ERROR: SHA256 block zeroize mismatch!");
    end

    for(genvar dword = 0; dword < SHA256_DIG_NUM_DWORDS; dword++) begin
        sha256_digest_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `SHA256_PATH.hwif_out.SHA256_CTRL.ZEROIZE.value |=> (`SHA256_PATH.digest_reg[dword] == 0) & (`SHA256_PATH.i_sha256_reg.field_storage.SHA256_DIGEST[dword].DIGEST.value == 0)
                                              )
                                  else $display("SVA ERROR: SHA256 digest zeroize mismatch!");                                
    end

    for(genvar dword = 0; dword < SHA512_BLOCK_NUM_DWORDS; dword++) begin
        sha512_block_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `SHA512_PATH.hwif_out.SHA512_CTRL.ZEROIZE.value |=> (`SHA512_PATH.hwif_out.SHA512_BLOCK[dword].BLOCK.value == 0)
                                              )
                                  else $display("SVA ERROR: SHA512 block zeroize mismatch!");
    end

    for(genvar dword = 0; dword < SHA512_DIG_NUM_DWORDS; dword++) begin
        sha512_digest_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `SHA512_PATH.hwif_out.SHA512_CTRL.ZEROIZE.value |=> (`SHA512_PATH.digest_reg[dword] == 0) & (`SHA512_PATH.i_sha512_reg.field_storage.SHA512_DIGEST[dword].DIGEST.value == 0)
                                              )
                                  else $display("SVA ERROR: SHA512 digest zeroize mismatch!");                                
    end

    for(genvar dword = 0; dword < HMAC_KEY_NUM_DWORDS; dword++) begin
        hmac_key_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `HMAC_PATH.hwif_out.HMAC512_CTRL.ZEROIZE.value |=> (`HMAC_PATH.hwif_out.HMAC512_KEY[dword].KEY.value == 0)
                                              )
                                  else $display("SVA ERROR: HMAC384 key zeroize mismatch!");
    end
    
    for(genvar dword = 0; dword < HMAC_BLOCK_NUM_DWORDS; dword++) begin
        hmac_block_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `HMAC_PATH.hwif_out.HMAC512_CTRL.ZEROIZE.value |=> (`HMAC_PATH.hwif_out.HMAC512_BLOCK[dword].BLOCK.value == 0)
                                              )
                                  else $display("SVA ERROR: HMAC384 block zeroize mismatch!");
    end

    for(genvar dword = 0; dword < HMAC_TAG_NUM_DWORDS; dword++) begin
        hmac_tag_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `HMAC_PATH.hwif_out.HMAC512_CTRL.ZEROIZE.value |=> (`HMAC_PATH.tag_reg[dword] == 0) & (`HMAC_PATH.i_hmac_reg.field_storage.HMAC512_TAG[dword].TAG.value == 0)
                                              )
                                  else $display("SVA ERROR: HMAC384 tag zeroize mismatch!");                      
    end


    for(genvar dword = 0; dword < ECC_REG_NUM_DWORDS; dword++) begin
        ecc_reg_zeroize:        assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `ECC_PATH.hwif_out.ECC_CTRL.ZEROIZE.value |=> (`ECC_PATH.hwif_out.ECC_SEED[dword].SEED.value == 0) & (`ECC_PATH.hwif_out.ECC_NONCE[dword].NONCE.value == 0) & (`ECC_PATH.hwif_out.ECC_PRIVKEY_IN[dword].PRIVKEY_IN.value == 0) &
                                              (`ECC_PATH.hwif_out.ECC_MSG[dword].MSG.value == 0) & (`ECC_PATH.hwif_out.ECC_PUBKEY_X[dword].PUBKEY_X.value == 0) & (`ECC_PATH.hwif_out.ECC_PUBKEY_Y[dword].PUBKEY_Y.value == 0) &
                                              (`ECC_PATH.hwif_out.ECC_SIGN_R[dword].SIGN_R.value == 0) & (`ECC_PATH.hwif_out.ECC_SIGN_S[dword].SIGN_S.value == 0) & (`ECC_PATH.hwif_out.ECC_VERIFY_R[dword].VERIFY_R.value == 0) & (`ECC_PATH.hwif_out.ECC_IV[dword].IV.value == 0) &
                                              (`ECC_REG_PATH.field_storage.ECC_PRIVKEY_OUT[dword].PRIVKEY_OUT.value == 0)
                                              )
                                  else $display("SVA ERROR: ECC reg zeroize mismatch!"); 
    end
    
    for(genvar addr = 0; addr < ECC_MEM_ADDR; addr++) begin
        ecc_mem_zeroize:        assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `ECC_PATH.hwif_out.ECC_CTRL.ZEROIZE.value |=> (`ECC_PATH.ecc_arith_unit_i.ram_tdp_file_i.mem[addr] == 0)
                                              )
                                  else $display("SVA ERROR: ECC mem zeroize mismatch!"); 
    end

    for(genvar addr = 0; addr < DOE_256_NUM_ROUNDS; addr++) begin
        doe_mem_zeroize:        assert property (
                                              @(posedge `DOE_INST_PATH.clk)
                                              `DOE_INST_PATH.zeroize |=> (`DOE_INST_PATH.i_doe_core_cbc.keymem.key_mem[addr] == 0)
                                              )
                                  else $display("SVA ERROR: DOE mem zeroize mismatch!"); 
    end
  endgenerate

  sha512_masked_core_digest_zeroize:       assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      `ECC_PATH.hwif_out.ECC_CTRL.ZEROIZE.value |=> (`SHA512_MASKED_PATH.digest == 0) & (`SHA512_MASKED_PATH.a_reg == 0) & (`SHA512_MASKED_PATH.b_reg == 0) & (`SHA512_MASKED_PATH.c_reg == 0) & (`SHA512_MASKED_PATH.d_reg == 0) & (`SHA512_MASKED_PATH.e_reg == 0) & (`SHA512_MASKED_PATH.f_reg == 0) & (`SHA512_MASKED_PATH.g_reg == 0) & (`SHA512_MASKED_PATH.h_reg == 0)
                                      )
                          else $display("SVA ERROR: SHA512_masked_core digest zeroize mismatch!");  
  
  doe_block_zeroize:      assert property (
                                      @(posedge `DOE_INST_PATH.clk)
                                      `DOE_INST_PATH.zeroize |=> (`DOE_INST_PATH.i_doe_core_cbc.enc_block.new_block == 0) & (`DOE_INST_PATH.i_doe_core_cbc.dec_block.new_block == 0)
                                      )
                          else $display("SVA ERROR: DOE block zeroize mismatch!"); 

  doe_reg_zeroize:      assert property (
                                      @(posedge `DOE_INST_PATH.clk)
                                      `DOE_INST_PATH.zeroize |=> (`DOE_INST_PATH.core_block == 0) & (`DOE_INST_PATH.core_IV == 0)
                                      )
                          else $display("SVA ERROR: DOE reg zeroize mismatch!"); 

  doe_key_clear:      assert property (
                                      @(posedge `DOE_INST_PATH.clk)
                                      disable iff(`CPTRA_TOP_PATH.cptra_in_debug_scan_mode)
                                      `DOE_INST_PATH.zeroize |=> (`DOE_INST_PATH.core_key == 0)
                                      )
                          else $display("SVA ERROR: DOE key clear mismatch!"); 

  genvar client;
  generate
    for(client = 0; client < KV_NUM_WRITE; client++) begin
      KV_client_wrdata_not_unknown: assert property (
                                                    @(posedge `SVA_RDC_CLK)
                                                    disable iff (!`KEYVAULT_PATH.kv_write[client].write_en || !`KEYVAULT_PATH.rst_b)
                                                    `KEYVAULT_PATH.kv_write[client].write_en |-> !$isunknown(`KEYVAULT_PATH.kv_write[client].write_data)
                                                  )
                                    else $display("SVA ERROR: KV client %0d data is unknown", client);
    end

    for(client = 0; client < KV_NUM_READ; client++) begin
      KV_client_rddata_not_unknown: assert property (
                                                    @(posedge `SVA_RDC_CLK)
                                                    disable iff (!`KEYVAULT_PATH.rst_b)
                                                    !$isunknown(`KEYVAULT_PATH.kv_rd_resp[client].read_data)
                                                  )
                                    else $display("SVA ERROR: KV client %0d data is unknown", client);
    end
  endgenerate
  
  //WDT checks:
  cascade_wdt_t1_pet: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.timer1_restart && `WDT_PATH.timer1_en && !`WDT_PATH.timer2_en && !`WDT_PATH.t1_timeout) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer1 did not restart on pet");

  cascade_wdt_t2_pet: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.timer2_restart && !`WDT_PATH.timer2_en && !`WDT_PATH.t2_timeout) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer2 did not restart on pet");

  cascade_wdt_t1_service: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.wdt_timer1_timeout_serviced_qual && `WDT_PATH.timer1_en && !`WDT_PATH.timer2_en && !`WDT_PATH.t2_timeout) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer1 did not restart after interrupt service");

  cascade_wdt_t2_service: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.wdt_timer2_timeout_serviced_qual && !`WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer2 did not restart after interrupt service");

  independent_wdt_t1_pet: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.timer1_restart && `WDT_PATH.timer1_en && `WDT_PATH.timer2_en) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer1 did not restart on pet");

  independent_wdt_t2_pet: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.timer2_restart && `WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer2 did not restart on pet");

  independent_wdt_t1_service: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.wdt_timer1_timeout_serviced_qual && `WDT_PATH.timer1_en && `WDT_PATH.timer2_en && !`WDT_PATH.t2_timeout) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer1 did not restart after interrupt service");

  independent_wdt_t2_service: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.wdt_timer2_timeout_serviced_qual && `WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer2 did not restart after interrupt service");

  wdt_status_t1_check: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (~`SVA_RST)
    $rose(`WDT_PATH.t1_timeout) |=> $rose(`SOC_IFC_TOP_PATH.soc_ifc_reg_hwif_out.CPTRA_WDT_STATUS.t1_timeout.value)
  )
  else $display("SVA ERROR: WDT Status bit not set on t1 expiry!");

  wdt_status_t2_check: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (~`SVA_RST)
    $rose(`WDT_PATH.t2_timeout) |=> $rose(`SOC_IFC_TOP_PATH.soc_ifc_reg_hwif_out.CPTRA_WDT_STATUS.t2_timeout.value)
  )
  else $display("SVA ERROR: WDT Status bit not set on t2 expiry!");



  //VALID flag SVA
  sha512_valid_flag:        assert property (
                                    @(posedge `SVA_RDC_CLK)
                                    `SHA512_PATH.digest_valid_reg |-> `SHA512_PATH.ready_reg
                                    )
                        else $display("SVA ERROR: SHA512 VALID flag mismatch!");
                          
  sha256_valid_flag:        assert property (
                                        @(posedge `SVA_RDC_CLK)
                                        `SHA256_PATH.digest_valid_reg |-> `SHA256_PATH.ready_reg
                                        )
                            else $display("SVA ERROR: SHA256 VALID flag mismatch!");

  HMAC_valid_flag:      assert property (
                                    @(posedge `SVA_RDC_CLK)
                                    `HMAC_PATH.tag_valid_reg |-> `HMAC_PATH.ready_reg
                                    )
                        else $display("SVA ERROR: HMAC VALID flag mismatch!"); 

  ECC_valid_flag:       assert property (
                                    @(posedge `SVA_RDC_CLK)
                                    `ECC_PATH.ecc_valid_reg |-> `ECC_PATH.ecc_ready_reg 
                                    )
                        else $display("SVA ERROR: ECC VALID flag mismatch!");
                        
  MLDSA_valid_flag:     assert property (
                          @(posedge `SVA_RDC_CLK)
                          disable iff (`SERVICES_PATH.disable_mldsa_sva)
                          `ABR_PATH.mldsa_valid_reg |-> `ABR_PATH.abr_ready
                      )
                      else $display("SVA ERROR: MLDSA VALID flag mismatch!");

  //SVA for SHA512 restore
  sha512_restore_cmd:   assert property ( 
                                    @(posedge `SVA_RDC_CLK) 
                                    `SHA512_PATH.restore_reg |-> (`SHA512_PATH.next_reg && !`SHA512_PATH.init_reg)
                                    ) 
                         else $display("SVA ERROR: SHA512 restore is not valid!");

  //SVA for modular operations
  ecc_opa_input:        assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      (`ECC_PATH.ecc_arith_unit_i.ecc_fau_i.add_en_i | `ECC_PATH.ecc_arith_unit_i.ecc_fau_i.mult_en_i) |-> (`ECC_PATH.ecc_arith_unit_i.ecc_fau_i.opa_i < `ECC_PATH.ecc_arith_unit_i.ecc_fau_i.prime_i)
                                      )
                          else $display("SVA ERROR: ECC opa input is not valid!"); 

  ecc_opb_input:        assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      (`ECC_PATH.ecc_arith_unit_i.ecc_fau_i.add_en_i | `ECC_PATH.ecc_arith_unit_i.ecc_fau_i.mult_en_i) |-> (`ECC_PATH.ecc_arith_unit_i.ecc_fau_i.opb_i < `ECC_PATH.ecc_arith_unit_i.ecc_fau_i.prime_i)
                                      )
                          else $display("SVA ERROR: ECC opb input is not valid!"); 

  ecc_add_result:       assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      `ECC_PATH.ecc_arith_unit_i.ecc_instr_s.opcode.add_we |-> (`ECC_PATH.ecc_arith_unit_i.add_res_s < `ECC_PATH.ecc_arith_unit_i.adder_prime)
                                      )
                          else $display("SVA ERROR: ECC adder result is not valid!"); 

  ecc_mult_result:       assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      `ECC_PATH.ecc_arith_unit_i.ecc_instr_s.opcode.mult_we |-> (`ECC_PATH.ecc_arith_unit_i.mult_res_s < `ECC_PATH.ecc_arith_unit_i.adder_prime)
                                      )
                          else $display("SVA ERROR: ECC multiplier result is not valid!"); 

  // SVA for LMS WNTZ accelerator
    wntz_mode:        assert property (
                                        @(posedge `SVA_RDC_CLK)
                                        `SHA256_PATH.init_reg |-> !`SHA256_PATH.next_reg
                                        )
                            else $display("SVA ERROR: SHA256 operation is not valid with INIT and NEXT asserted in the same cycle!");

  // Bus IDLE on Firmware Update Reset
  fw_upd_rst_doe_idle:     assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`DOE_REG_PATH.s_cpuif_req)
                           else $display("SVA ERROR: DOE bus not idle after Firmware Update Reset!");
  fw_upd_rst_ecc_idle:     assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`ECC_REG_PATH.s_cpuif_req)
                           else $display("SVA ERROR: ECC bus not idle after Firmware Update Reset!");
  fw_upd_rst_hmac_idle:    assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`HMAC_REG_PATH.s_cpuif_req)
                           else $display("SVA ERROR: HMAC bus not idle after Firmware Update Reset!");
  fw_upd_rst_kv_idle:      assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`KEYVAULT_REG_PATH.s_cpuif_req)
                           else $display("SVA ERROR: Key Vault bus not idle after Firmware Update Reset!");
  fw_upd_rst_pv_idle:      assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`PCRVAULT_REG_PATH.s_cpuif_req)
                           else $display("SVA ERROR: PCR Vault bus not idle after Firmware Update Reset!");
  fw_upd_rst_dv_idle:      assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`DATA_VAULT_REG_PATH.s_cpuif_req)
                           else $display("SVA ERROR: Data Vault bus not idle after Firmware Update Reset!");
  fw_upd_rst_sha256_idle:  assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`SHA256_PATH.i_sha256_reg.s_cpuif_req)
                           else $display("SVA ERROR: SHA256 bus not idle after Firmware Update Reset!");
  fw_upd_rst_sha512_idle:  assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`SHA512_PATH.i_sha512_reg.s_cpuif_req)
                           else $display("SVA ERROR: SHA512 bus not idle after Firmware Update Reset!");
  fw_upd_rst_soc_ifc_idle: assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`SOC_IFC_TOP_PATH.i_ahb_slv_sif_soc_ifc.dv)
                           else $display("SVA ERROR: SOC_IFC bus not idle after Firmware Update Reset!");


  hmac_drbg_zero_result:  assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      `HMAC_DRBG_PATH.valid |-> (`HMAC_DRBG_PATH.drbg != 384'h0 )
                                      )
                          else $display("SVA ERROR: drbg is zero when valid is high"); 

  hmac_drbg_illegal_above_prime:       assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      `HMAC_DRBG_PATH.valid |-> (`HMAC_DRBG_PATH.drbg < `HMAC_DRBG_PATH.HMAC_DRBG_PRIME)
                                      )
                          else $display("SVA ERROR: drbg >= HMAC_DRBG_PRIME when valid is high"); 

endmodule
