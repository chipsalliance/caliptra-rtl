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
`define CPTRA_TOP_PATH  caliptra_top_tb.caliptra_top_dut
`define KEYVAULT_PATH   `CPTRA_TOP_PATH.key_vault1
`define DOE_INST_PATH   `CPTRA_TOP_PATH.doe.doe_inst
`define DOE_PATH        `DOE_INST_PATH.doe_fsm1
`define DOE_REG_PATH    `DOE_INST_PATH.i_doe_reg
`define SERVICES_PATH   caliptra_top_tb.tb_services_i
`define SHA512_PATH     `CPTRA_TOP_PATH.sha512.sha512_inst
`define HMAC_PATH       `CPTRA_TOP_PATH.hmac.hmac_inst
`define ECC_PATH        `CPTRA_TOP_PATH.ecc_top1.ecc_dsa_ctrl_i
`define ECC_REG_PATH    `CPTRA_TOP_PATH.ecc_top1.ecc_reg1
`define SHA256_PATH     `CPTRA_TOP_PATH.sha256.sha256_inst
`define SHA512_MASKED_PATH `CPTRA_TOP_PATH.ecc_top1.ecc_dsa_ctrl_i.ecc_hmac_drbg_interface_i.hmac_drbg_i.HMAC_K.u_sha512_core_h1
`define SOC_IFC_TOP_PATH   `CPTRA_TOP_PATH.soc_ifc_top1
`define WDT_PATH        `SOC_IFC_TOP_PATH.i_wdt


module caliptra_top_sva
  import doe_defines_pkg::*;
  import kv_defines_pkg::*;
  ();

  //TODO: pass these parameters from their architecture into here
  localparam SHA512_DIG_NUM_DWORDS    = 16;   //`SHA512_PATH.DIG_NUM_DWORDS;
  localparam SHA512_BLOCK_NUM_DWORDS  = 32;   //`SHA512_PATH.BLOCK_NUM_DWORDS;
  localparam HMAC_KEY_NUM_DWORDS      = 12;   //`HMAC_PATH.KEY_NUM_DWORDS
  localparam HMAC_TAG_NUM_DWORDS      = 12;   //`HMAC_PATH.TAG_NUM_DWORDS
  localparam HMAC_BLOCK_NUM_DWORDS    = 32;   //`HMAC_PATH.BLOCK_NUM_DWORDS
  localparam ECC_REG_NUM_DWORDS       = 12;   //'ECC_PATH.REG_NUM_DWORDS
  localparam ECC_MEM_ADDR             = 2**6; //'ECC_PATH.ecc_arith_unit_i.ram_tdp_file_i.mem.ADDR_LENGTH
  localparam SHA256_DIG_NUM_DWORDS    = 8;    //`SHA256_PATH.DIG_NUM_DWORDS;
  localparam SHA256_BLOCK_NUM_DWORDS  = 16;   //`SHA256_PATH.BLOCK_NUM_DWORDS;

  //TODO: add disable condition based on doe cmd reg
  DOE_lock_uds_set:        assert property (
                                            @(posedge `DOE_PATH.clk)
                                            $rose(`DOE_PATH.flow_done) && $past(doe_cmd_reg_t'(`DOE_PATH.doe_cmd_reg.cmd) == DOE_UDS) |=> `DOE_PATH.lock_uds_flow
                                          )
                            else $display("SVA ERROR: lock_uds_flow was not set after UDS flow");

  DOE_lock_uds_cold_reset: assert property (
                                            @(posedge `DOE_PATH.clk)
                                            ~`DOE_PATH.hard_rst_b |-> (`DOE_PATH.lock_uds_flow == 0)
                                          )
                            else $display("SVA ERROR: lock_uds_flow was not reset on hard reset");

  DOE_lock_uds_warm_reset: assert property (
                                            @(posedge `DOE_PATH.clk)
                                            disable iff (~`DOE_PATH.rst_b && ~`DOE_PATH.hard_rst_b)
                                            ~`DOE_PATH.rst_b |-> $past(`DOE_PATH.lock_uds_flow) == `DOE_PATH.lock_uds_flow
                                          )
                            else $display("SVA ERROR: lock_uds_flow toggled after warm reset");

  DOE_lock_fe_set:         assert property (
                                            @(posedge `DOE_PATH.clk)
                                            $rose(`DOE_PATH.flow_done) && $past(doe_cmd_reg_t'(`DOE_PATH.doe_cmd_reg.cmd) == DOE_FE) |=> `DOE_PATH.lock_fe_flow
                                          )
                            else $display("SVA ERROR: lock_fe_flow was not set after FE flow");

  DOE_lock_fe_cold_reset:    assert property (
                                            @(posedge `DOE_PATH.clk)
                                            ~`DOE_PATH.hard_rst_b |-> (`DOE_PATH.lock_fe_flow == 0)
                                          )
                            else $display("SVA ERROR: lock_fe_flow was not reset on hard reset");

  DOE_lock_fe_warm_reset:    assert property (
                                            @(posedge `DOE_PATH.clk)
                                            disable iff (~`DOE_PATH.rst_b && ~`DOE_PATH.hard_rst_b)
                                            ~`DOE_PATH.rst_b |-> $past(`DOE_PATH.lock_fe_flow) == `DOE_PATH.lock_fe_flow
                                          )
                            else $display("SVA ERROR: lock_fe_flow toggled after warm reset");

  DOE_clear_obf_status_valid: assert property (
                                            @(posedge `CPTRA_TOP_PATH.clk)
                                            `CPTRA_TOP_PATH.clear_obf_secrets |=> (`DOE_REG_PATH.field_storage.DOE_STATUS.VALID.value && `DOE_REG_PATH.field_storage.DOE_STATUS.DEOBF_SECRETS_CLEARED.value)
                                          )
                            else $display("SVA ERROR: DOE STATUS valid bit not set after clear obf secrets cmd");

  KV_haddr_valid:          assert property (
                                            @(posedge `CPTRA_TOP_PATH.clk)
                                            disable iff (~`KEYVAULT_PATH.hsel_i)
                                            `KEYVAULT_PATH.hsel_i |-> !$isunknown(`KEYVAULT_PATH.haddr_i)
                                          )
                            else $display("SVA ERROR: AHB address not valid in keyvault");

  generate 
    for(genvar entry=0; entry < KV_NUM_KEYS; entry++) begin
      for(genvar dword = 0; dword < KV_NUM_DWORDS; dword++) begin
        KV_debug_value0:         assert property (
                                                  @(posedge `KEYVAULT_PATH.clk)
                                                  disable iff(!`KEYVAULT_PATH.cptra_pwrgood)
                                                  (`KEYVAULT_PATH.flush_keyvault || `SOC_IFC_TOP_PATH.cptra_error_fatal) && (`KEYVAULT_PATH.kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value.value == 0) && `KEYVAULT_PATH.cptra_pwrgood |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[entry][dword] == CLP_DEBUG_MODE_KV_0)
                                                )
                                  else $display("SVA ERROR: KV not flushed with correct debug values");

        KV_debug_value1:         assert property (
                                                  @(posedge `KEYVAULT_PATH.clk)
                                                  disable iff(!`KEYVAULT_PATH.cptra_pwrgood)
                                                  (`KEYVAULT_PATH.flush_keyvault || `SOC_IFC_TOP_PATH.cptra_error_fatal) && (`KEYVAULT_PATH.kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value.value == 1) && `KEYVAULT_PATH.cptra_pwrgood |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[entry][dword] == CLP_DEBUG_MODE_KV_1)
                                                )
                                  else $display("SVA ERROR: KV not flushed with correct debug values");
      end
    end
  endgenerate

  generate
    for(genvar dword = 0; dword < KV_NUM_DWORDS; dword++) begin
      //sha512 block read
      kv_sha512_block_r_flow:   assert property (
                                            @(posedge `KEYVAULT_PATH.clk)
                                            $rose(`SHA512_PATH.kv_src_done & ~`SHA512_PATH.pcr_hash_extend_ip) && (dword < (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_CTRL[`SHA512_PATH.kv_read.read_entry].last_dword + 1)) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`SHA512_PATH.kv_read.read_entry][dword] == `SHA512_PATH.block_reg[dword])
                                            )
                                else $display("SVA ERROR: SHA384 block mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`SHA512_PATH.kv_read.read_entry][dword], `SHA512_PATH.block_reg[dword]);

      //sha512 digest write
      if (dword < SHA512_DIG_NUM_DWORDS) begin
        kv_sha512_digest_w_flow:  assert property (
                                              @(posedge `KEYVAULT_PATH.clk)
                                              `SHA512_PATH.kv_dest_done & ~`SHA512_PATH.pcr_hash_extend_ip |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`SHA512_PATH.kv_write_ctrl_reg.write_entry][dword] == `SHA512_PATH.kv_reg[(KV_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: SHA384 digest mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`SHA512_PATH.kv_write_ctrl_reg.write_entry][dword], `SHA512_PATH.kv_reg[(KV_NUM_DWORDS-1) - dword]);
      end

      //hmac block read
      kv_hmac_block_r_flow:     assert property (
                                            @(posedge `KEYVAULT_PATH.clk)
                                            $rose(`HMAC_PATH.kv_block_done) && (dword < (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_CTRL[`HMAC_PATH.kv_read[1].read_entry].last_dword + 1)) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_read[1].read_entry][dword] == `HMAC_PATH.block_reg[dword])
                                            )
                                else $display("SVA ERROR: HMAC384 block mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_read[1].read_entry][dword], `HMAC_PATH.block_reg[dword]);

      //hmac key read
      if (dword < HMAC_KEY_NUM_DWORDS) begin
        kv_hmac_key_r_flow:       assert property (
                                              @(posedge `KEYVAULT_PATH.clk)
                                              $fell(`HMAC_PATH.kv_key_write_en) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_read[0].read_entry][dword] == `HMAC_PATH.key_reg[dword])
                                              )
                                  else $display("SVA ERROR: HMAC384 key mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_read[0].read_entry][dword], `HMAC_PATH.key_reg[dword]);
      end

      //hmac tag write
      if (dword < HMAC_TAG_NUM_DWORDS) begin
        kv_hmac_tag_w_flow:       assert property (
                                              @(posedge `KEYVAULT_PATH.clk)
                                              `HMAC_PATH.kv_write_done |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword] == `HMAC_PATH.kv_reg[(`HMAC_PATH.TAG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: HMAC384 tag mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword], `HMAC_PATH.kv_reg[(`HMAC_PATH.TAG_NUM_DWORDS-1) - dword]);                    
      end
      
      // ECC
      if (dword < ECC_REG_NUM_DWORDS) begin
        //ecc privkey read
        kv_ecc_privkey_r_flow:    assert property (
                                              @(posedge `KEYVAULT_PATH.clk)
                                              $fell(`ECC_PATH.kv_privkey_write_en) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_read[0].read_entry][dword] == `ECC_PATH.privkey_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: ECC privkey read mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_read[0].read_entry][dword], `ECC_PATH.privkey_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword]);
        kv_ecc_seed_r_flow:       assert property (
                                              @(posedge `KEYVAULT_PATH.clk)
                                              $fell(`ECC_PATH.kv_seed_write_en) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_read[1].read_entry][dword] == `ECC_PATH.seed_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: ECC seed mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_read[1].read_entry][dword], `ECC_PATH.seed_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword]);
        //ecc privkey write
        kv_ecc_privkey_w_flow:    assert property (
                                              @(posedge `KEYVAULT_PATH.clk)
                                              `ECC_PATH.kv_write_done |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword] == `ECC_PATH.kv_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: ECC privkey write mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword], `ECC_PATH.kv_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword]);

        //ecc sign r
        pcr_ecc_sign_r:    assert property (
                                              @(posedge `SERVICES_PATH.clk)
                                              `SERVICES_PATH.check_pcr_signing |-> (`SERVICES_PATH.test_vector.R[dword] == `ECC_PATH.hwif_out.ECC_SIGN_R[dword].SIGN_R.value)
                                              )
                                  else $display("SVA ERROR: PCR SIGNING SIGN_R mismatch!, 0x%04x, 0x%04x", `SERVICES_PATH.test_vector.R[dword], `ECC_PATH.hwif_out.ECC_SIGN_R[dword].SIGN_R.value);                     
        
        //ecc sign s
        pcr_ecc_sign_s:    assert property (
                                              @(posedge `SERVICES_PATH.clk)
                                              `SERVICES_PATH.check_pcr_signing |-> (`SERVICES_PATH.test_vector.S[dword] == `ECC_PATH.hwif_out.ECC_SIGN_S[dword].SIGN_S.value)
                                              )
                                  else $display("SVA ERROR: PCR SIGNING SIGN_S mismatch!, 0x%04x, 0x%04x", `SERVICES_PATH.test_vector.S[dword], `ECC_PATH.hwif_out.ECC_SIGN_S[dword].SIGN_S.value); 
      end
    end
  endgenerate

  `ifndef VERILATOR
  generate
    begin: UDS_data_check
    for(genvar dword = 0; dword < `CLP_OBF_UDS_DWORDS; dword++) begin
      DOE_UDS_data_check:  assert property (
                                            @(posedge `DOE_PATH.clk)
                                            (`SERVICES_PATH.WriteData == 'hEC && `SERVICES_PATH.mailbox_write) |=> ##[1:$] $rose(`DOE_PATH.lock_uds_flow) |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword] == `SERVICES_PATH.doe_test_vector.uds_plaintext[dword])
                                
                                          )
                                  else $display("SVA ERROR: DOE UDS output %h does not match plaintext %h!", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword], `SERVICES_PATH.doe_test_vector.uds_plaintext[dword]);
    end
    end
  endgenerate
  generate
    begin: FE_data_check
    for(genvar dword = 0; dword < `CLP_OBF_FE_DWORDS; dword++) begin
  
      DOE_FE_data_check:   assert property (
                                            @(posedge `DOE_PATH.clk)
                                            (`SERVICES_PATH.WriteData == 'hED && `SERVICES_PATH.mailbox_write) |=> ##[1:$] $rose(`DOE_PATH.lock_fe_flow) |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword] == `SERVICES_PATH.doe_test_vector.fe_plaintext[dword])
                                          )
                                  else $display("SVA ERROR: DOE FE output %h does not match plaintext %h!", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword], `SERVICES_PATH.doe_test_vector.fe_plaintext[dword]);

    end
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

  always@(posedge `SOC_IFC_TOP_PATH.clk or negedge `CPTRA_TOP_PATH.cptra_rst_b) begin
    if(!`CPTRA_TOP_PATH.cptra_rst_b) begin
      clear_obf_secrets_f <= 'b0;
      clear_obf_secrets_ff <= 'b0;
    end
    else begin
      clear_obf_secrets_f <= `SOC_IFC_TOP_PATH.clear_obf_secrets;
      clear_obf_secrets_ff <= clear_obf_secrets_f;
    end
  end

  always@(posedge `CPTRA_TOP_PATH.clk or negedge `CPTRA_TOP_PATH.cptra_rst_b) begin
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
                                  @(posedge `SOC_IFC_TOP_PATH.clk)
                                  disable iff(`CPTRA_TOP_PATH.cptra_in_debug_scan_mode || clear_obf_secrets_int || cptra_in_debug_scan_mode_int)
                                  (`SOC_IFC_TOP_PATH.soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value) |-> `CPTRA_TOP_PATH.obf_uds_seed_dbg == $past(`CPTRA_TOP_PATH.obf_uds_seed_dbg)
  )
  else $display("SVA ERROR: Unexpected write to obf uds seed!");

  FE_fuse_wr_check: assert property (
                                  @(posedge `SOC_IFC_TOP_PATH.clk)
                                  disable iff(`CPTRA_TOP_PATH.cptra_in_debug_scan_mode || clear_obf_secrets_int || cptra_in_debug_scan_mode_int)
                                  (`SOC_IFC_TOP_PATH.soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value) |-> `CPTRA_TOP_PATH.obf_field_entropy_dbg == $past(`CPTRA_TOP_PATH.obf_field_entropy_dbg)
  )
  else $display("SVA ERROR: Unexpected write to obf field entropy!");

  //ZEROIZE SVA
  generate
    for(genvar dword = 0; dword < SHA256_BLOCK_NUM_DWORDS; dword++) begin
        sha256_block_zeroize:       assert property (
                                              @(posedge `SHA256_PATH.clk)
                                              `SHA256_PATH.hwif_out.SHA256_CTRL.ZEROIZE.value |=> (`SHA256_PATH.hwif_out.SHA256_BLOCK[dword].BLOCK.value == 0)
                                              )
                                  else $display("SVA ERROR: SHA256 block zeroize mismatch!");
    end

    for(genvar dword = 0; dword < SHA256_DIG_NUM_DWORDS; dword++) begin
        sha256_digest_zeroize:       assert property (
                                              @(posedge `SHA256_PATH.clk)
                                              `SHA256_PATH.hwif_out.SHA256_CTRL.ZEROIZE.value |=> (`SHA256_PATH.digest_reg[dword] == 0) & (`SHA256_PATH.i_sha256_reg.decoded_reg_strb.SHA256_DIGEST[dword] == 0)
                                              )
                                  else $display("SVA ERROR: SHA256 digest zeroize mismatch!");                                
    end

    for(genvar dword = 0; dword < SHA512_BLOCK_NUM_DWORDS; dword++) begin
        sha512_block_zeroize:       assert property (
                                              @(posedge `SHA512_PATH.clk)
                                              `SHA512_PATH.hwif_out.SHA512_CTRL.ZEROIZE.value |=> (`SHA512_PATH.hwif_out.SHA512_BLOCK[dword].BLOCK.value == 0)
                                              )
                                  else $display("SVA ERROR: SHA512 block zeroize mismatch!");
    end

    for(genvar dword = 0; dword < SHA512_DIG_NUM_DWORDS; dword++) begin
        sha512_digest_zeroize:       assert property (
                                              @(posedge `SHA512_PATH.clk)
                                              `SHA512_PATH.hwif_out.SHA512_CTRL.ZEROIZE.value |=> (`SHA512_PATH.digest_reg[dword] == 0) & (`SHA512_PATH.i_sha512_reg.decoded_reg_strb.SHA512_DIGEST[dword] == 0)
                                              )
                                  else $display("SVA ERROR: SHA512 digest zeroize mismatch!");                                
    end

    for(genvar dword = 0; dword < HMAC_KEY_NUM_DWORDS; dword++) begin
        hmac_key_zeroize:       assert property (
                                              @(posedge `HMAC_PATH.clk)
                                              `HMAC_PATH.hwif_out.HMAC384_CTRL.ZEROIZE.value |=> (`HMAC_PATH.hwif_out.HMAC384_KEY[dword].KEY.value == 0)
                                              )
                                  else $display("SVA ERROR: HMAC384 key zeroize mismatch!");
    end
    
    for(genvar dword = 0; dword < HMAC_BLOCK_NUM_DWORDS; dword++) begin
        hmac_block_zeroize:       assert property (
                                              @(posedge `HMAC_PATH.clk)
                                              `HMAC_PATH.hwif_out.HMAC384_CTRL.ZEROIZE.value |=> (`HMAC_PATH.hwif_out.HMAC384_BLOCK[dword].BLOCK.value == 0)
                                              )
                                  else $display("SVA ERROR: HMAC384 block zeroize mismatch!");
    end

    for(genvar dword = 0; dword < HMAC_TAG_NUM_DWORDS; dword++) begin
        hmac_tag_zeroize:       assert property (
                                              @(posedge `HMAC_PATH.clk)
                                              `HMAC_PATH.hwif_out.HMAC384_CTRL.ZEROIZE.value |=> (`HMAC_PATH.tag_reg[dword] == 0) & (`HMAC_PATH.i_hmac_reg.decoded_reg_strb.HMAC384_TAG[dword] == 0)
                                              )
                                  else $display("SVA ERROR: HMAC384 tag zeroize mismatch!");                      
    end


    for(genvar dword = 0; dword < ECC_REG_NUM_DWORDS; dword++) begin
        ecc_reg_zeroize:        assert property (
                                              @(posedge `ECC_PATH.clk)
                                              `ECC_PATH.hwif_out.ECC_CTRL.ZEROIZE.value |=> (`ECC_PATH.hwif_out.ECC_SEED[dword].SEED.value == 0) & (`ECC_PATH.hwif_out.ECC_NONCE[dword].NONCE.value == 0) & (`ECC_PATH.hwif_out.ECC_PRIVKEY_IN[dword].PRIVKEY_IN.value == 0) &
                                              (`ECC_PATH.hwif_out.ECC_MSG[dword].MSG.value == 0) & (`ECC_PATH.hwif_out.ECC_PUBKEY_X[dword].PUBKEY_X.value == 0) & (`ECC_PATH.hwif_out.ECC_PUBKEY_Y[dword].PUBKEY_Y.value == 0) &
                                              (`ECC_PATH.hwif_out.ECC_SIGN_R[dword].SIGN_R.value == 0) & (`ECC_PATH.hwif_out.ECC_SIGN_S[dword].SIGN_S.value == 0) & (`ECC_PATH.hwif_out.ECC_VERIFY_R[dword].VERIFY_R.value == 0) & (`ECC_PATH.hwif_out.ECC_IV[dword].IV.value == 0) &
                                              (`ECC_REG_PATH.decoded_reg_strb.ECC_PRIVKEY_OUT[dword] == 0)
                                              )
                                  else $display("SVA ERROR: ECC reg zeroize mismatch!"); 
      end
    
    for(genvar addr = 0; addr < ECC_MEM_ADDR; addr++) begin
        ecc_mem_zeroize:        assert property (
                                              @(posedge `ECC_PATH.clk)
                                              `ECC_PATH.hwif_out.ECC_CTRL.ZEROIZE.value |=> (`ECC_PATH.ecc_arith_unit_i.ram_tdp_file_i.mem[addr] == 0)
                                              )
                                  else $display("SVA ERROR: ECC mem zeroize mismatch!"); 
      end
  endgenerate

  sha512_masked_core_digest_zeroize:       assert property (
                                      @(posedge `ECC_PATH.clk)
                                      `ECC_PATH.hwif_out.ECC_CTRL.ZEROIZE.value |=> (`SHA512_MASKED_PATH.digest == 0) & (`SHA512_MASKED_PATH.a_reg == 0) & (`SHA512_MASKED_PATH.b_reg == 0) & (`SHA512_MASKED_PATH.c_reg == 0) & (`SHA512_MASKED_PATH.d_reg == 0) & (`SHA512_MASKED_PATH.e_reg == 0) & (`SHA512_MASKED_PATH.f_reg == 0) & (`SHA512_MASKED_PATH.g_reg == 0) & (`SHA512_MASKED_PATH.h_reg == 0)
                                      )
                          else $display("SVA ERROR: SHA512_masked_core digest zeroize mismatch!");  


  genvar client;
  generate
    for(client = 0; client < KV_NUM_WRITE; client++) begin
      KV_client_wrdata_not_unknown: assert property (
                                                    @(posedge `KEYVAULT_PATH.clk)
                                                    disable iff (!`KEYVAULT_PATH.kv_write[client].write_en || !`KEYVAULT_PATH.rst_b)
                                                    `KEYVAULT_PATH.kv_write[client].write_en |-> !$isunknown(`KEYVAULT_PATH.kv_write[client].write_data)
                                                  )
                                    else $display("SVA ERROR: KV client %0d data is unknown", client);
    end

    for(client = 0; client < KV_NUM_READ; client++) begin
      KV_client_rddata_not_unknown: assert property (
                                                    @(posedge `KEYVAULT_PATH.clk)
                                                    disable iff (!`KEYVAULT_PATH.rst_b)
                                                    !$isunknown(`KEYVAULT_PATH.kv_rd_resp[client].read_data)
                                                  )
                                    else $display("SVA ERROR: KV client %0d data is unknown", client);
    end
  endgenerate
  
  //WDT checks:
  cascade_wdt_t1_pet: assert property (
    @(posedge `WDT_PATH.clk)
    (`WDT_PATH.timer1_restart && !`WDT_PATH.timer2_en) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer1 did not restart on pet");

  cascade_wdt_t2_pet: assert property (
    @(posedge `WDT_PATH.clk)
    (`WDT_PATH.timer2_restart && !`WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer2 did not restart on pet");

  cascade_wdt_t1_service: assert property (
    @(posedge `WDT_PATH.clk)
    (`WDT_PATH.wdt_timer1_timeout_serviced && !`WDT_PATH.timer2_en && !`WDT_PATH.t2_timeout) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer1 did not restart after interrupt service");

  cascade_wdt_t2_service: assert property (
    @(posedge `WDT_PATH.clk)
    (`WDT_PATH.wdt_timer2_timeout_serviced && !`WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer2 did not restart after interrupt service");

  independent_wdt_t1_pet: assert property (
    @(posedge `WDT_PATH.clk)
    (`WDT_PATH.timer1_restart && `WDT_PATH.timer2_en) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer1 did not restart on pet");

  independent_wdt_t2_pet: assert property (
    @(posedge `WDT_PATH.clk)
    (`WDT_PATH.timer2_restart && `WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer2 did not restart on pet");

  independent_wdt_t1_service: assert property (
    @(posedge `WDT_PATH.clk)
    (`WDT_PATH.wdt_timer1_timeout_serviced && `WDT_PATH.timer2_en && !`WDT_PATH.t2_timeout) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer1 did not restart after interrupt service");

  independent_wdt_t2_service: assert property (
    @(posedge `WDT_PATH.clk)
    (`WDT_PATH.wdt_timer2_timeout_serviced && `WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer2 did not restart after interrupt service");



  //VALID flag SVA
  sha512_valid_flag:        assert property (
                                    @(posedge `SHA512_PATH.clk)
                                    `SHA512_PATH.digest_valid_reg |-> `SHA512_PATH.ready_reg
                                    )
                        else $display("SVA ERROR: SHA512 VALID flag mismatch!");
                          
  sha256_valid_flag:        assert property (
                                        @(posedge `SHA256_PATH.clk)
                                        `SHA256_PATH.digest_valid_reg |-> `SHA256_PATH.ready_reg
                                        )
                            else $display("SVA ERROR: SHA256 VALID flag mismatch!");

  HMAC_valid_flag:      assert property (
                                    @(posedge `HMAC_PATH.clk)
                                    `HMAC_PATH.tag_valid_reg |-> `HMAC_PATH.core_ready_reg
                                    )
                        else $display("SVA ERROR: HMAC VALID flag mismatch!"); 

  ECC_valid_flag:       assert property (
                                    @(posedge `ECC_PATH.clk)
                                    `ECC_PATH.dsa_valid_reg |-> `ECC_PATH.dsa_ready_reg 
                                    )
                        else $display("SVA ERROR: ECC VALID flag mismatch!");                         


endmodule

