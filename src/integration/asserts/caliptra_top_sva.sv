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


module caliptra_top_sva
  import doe_defines_pkg::*;
  import kv_defines_pkg::*;
  ();

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


  KV_debug_value0:         assert property (
                                            @(posedge `KEYVAULT_PATH.clk)
                                            `KEYVAULT_PATH.flush_keyvault && (`KEYVAULT_PATH.kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value.value == 0) |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[0][0] == CLP_DEBUG_MODE_KV_0)
                                          )
                            else $display("SVA ERROR: KV not flushed with correct debug values");

  KV_debug_value1:         assert property (
                                            @(posedge `KEYVAULT_PATH.clk)
                                            `KEYVAULT_PATH.flush_keyvault && (`KEYVAULT_PATH.kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value.value == 1) |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[0][0] == CLP_DEBUG_MODE_KV_1)
                                          )
                            else $display("SVA ERROR: KV not flushed with correct debug values");

  //TODO: uncomment after fixing fuse_field_entropy bug
  // genvar client;
  // generate
  //   for(client = 0; client < KV_NUM_WRITE; client++) begin
  //     KV_client_wrdata_not_unknown: assert property (
  //                                                   @(posedge `KEYVAULT_PATH.clk)
  //                                                   disable iff (!`KEYVAULT_PATH.kv_write[client].write_en || !`KEYVAULT_PATH.rst_b)
  //                                                   `KEYVAULT_PATH.kv_write[client].write_en |-> !$isunknown(`KEYVAULT_PATH.kv_write[client].write_data)
  //                                                 )
  //                                   else $display("SVA ERROR: KV client %0d data is unknown", client);
  //   end
  // endgenerate
    

endmodule

