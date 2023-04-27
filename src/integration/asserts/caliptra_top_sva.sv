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
`define KEYVAULT_PATH   caliptra_top_tb.caliptra_top_dut.key_vault1
`define DOE_PATH        caliptra_top_tb.caliptra_top_dut.doe.doe_inst.doe_fsm1
`define SERVICES_PATH   caliptra_top_tb.tb_services_i
`define SHA512_PATH     caliptra_top_tb.caliptra_top_dut.sha512.sha512_inst
`define HMAC_PATH       caliptra_top_tb.caliptra_top_dut.hmac.hmac_inst
`define ECC_PATH        caliptra_top_tb.caliptra_top_dut.ecc_top1.ecc_dsa_ctrl_i


module caliptra_top_sva
  import doe_defines_pkg::*;
  import kv_defines_pkg::*;
  ();

  //TODO: pass these parameters from their architecture into here
  localparam SHA512_DIG_NUM_DWORDS = 16; //`SHA512_PATH.DIG_NUM_DWORDS;
  localparam HMAC_KEY_NUM_DWORDS  = 12;  //`HMAC_PATH.KEY_NUM_DWORDS
  localparam HMAC_TAG_NUM_DWORDS = 12;   //`HMAC_PATH.TAG_NUM_DWORDS
  localparam ECC_REG_NUM_DWORDS = 12;   // 'ECC_PATH.REG_NUM_DWORDS

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
                                                  `KEYVAULT_PATH.flush_keyvault && (`KEYVAULT_PATH.kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value.value == 0) && `KEYVAULT_PATH.cptra_pwrgood |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[entry][dword] == CLP_DEBUG_MODE_KV_0)
                                                )
                                  else $display("SVA ERROR: KV not flushed with correct debug values");

        KV_debug_value1:         assert property (
                                                  @(posedge `KEYVAULT_PATH.clk)
                                                  disable iff(!`KEYVAULT_PATH.cptra_pwrgood)
                                                  `KEYVAULT_PATH.flush_keyvault && (`KEYVAULT_PATH.kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value.value == 1) && `KEYVAULT_PATH.cptra_pwrgood |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[entry][dword] == CLP_DEBUG_MODE_KV_1)
                                                )
                                  else $display("SVA ERROR: KV not flushed with correct debug values");
      end
    end
  endgenerate

  genvar dword;
  generate
    for(dword = 0; dword < KV_NUM_DWORDS; dword++) begin
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
      end

    end
  endgenerate


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
    

endmodule

