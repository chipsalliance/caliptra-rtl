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
//
// soc_ifc_axi_sha_acc_dis_test
// ----------
// Test to make sure SHA acc is not accessible over SoC AXI interface

module soc_ifc_axi_sha_acc_dis_test
    import soc_ifc_pkg::*;
    import axi_pkg::*;
    ();

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  parameter CLK_HALF_PERIOD = 5000;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;
  parameter MAX_CYCLES = 20_0000;

  parameter integer AW = 32;
  parameter integer DW = 32; 
  parameter integer IW = 8;
  parameter integer UW = 32;

  reg [63 : 0]  cycle_ctr;
  reg [63 : 0]  error_ctr;
  reg [63 : 0]  tc_ctr;
  reg [63 : 0]  temp_ctr;

  reg           clk_tb;
  reg           cptra_pwrgood_tb;
  reg           cptra_rst_b_tb;

  logic [31:0] rdata;

  // Component Signals
// logic dv;
// logic [AW-1:0] addr;
// logic [DW-1:0] wdata;
// logic [DW/8-1:0] wstrb;
// logic [DW-1:0] rdata;
// logic last;
// logic hld;
// logic err;
// logic [UW-1:0] user;
  
  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  axi_if #(.AW(18), .DW(32), .IW(8), .UW(32)) axi_sub_if(clk_tb, cptra_rst_b_tb);
  axi_if #(.AW(18), .DW(32), .IW(8), .UW(32)) axi_mgr_if(clk_tb, cptra_rst_b_tb);

  soc_ifc_top #(.AXI_ID_WIDTH(8)) dut (
    .clk(clk_tb),
    .clk_cg(clk_tb),
    .soc_ifc_clk_cg(clk_tb),
    .rdc_clk_cg(clk_tb),

    .cptra_pwrgood(cptra_pwrgood_tb),
    .cptra_rst_b(cptra_rst_b_tb),

    .ready_for_fuses(),
    .ready_for_mb_processing(),
    .ready_for_runtime(),

    .mailbox_data_avail(),
    .mailbox_flow_done(),

    .recovery_data_avail(0),
    .recovery_image_activated(0),

    .security_state({2'b11, 0}),

    .generic_input_wires(0),
    .BootFSM_BrkPoint(0),
    .generic_output_wires(),

    .s_axi_w_if(axi_sub_if.w_sub),
    .s_axi_r_if(axi_sub_if.r_sub),

    .haddr_i(),
    .hwdata_i(),
    .hsel_i(),
    .hwrite_i(),
    .hready_i(),
    .htrans_i(),
    .hsize_i(),

    .hresp_o(),
    .hreadyout_o(),
    .hrdata_o(),

    .m_axi_w_if(axi_mgr_if.w_mgr),
    .m_axi_r_if(axi_mgr_if.r_mgr),

    .cptra_error_fatal(),
    .cptra_error_non_fatal(),
    .trng_req(),

    .soc_ifc_error_intr(),
    .soc_ifc_notif_intr(),
    .sha_error_intr(),
    .sha_notif_intr(),
    .dma_error_intr(),
    .dma_notif_intr(),
    .timer_intr(),

    .mbox_sram_req(),
    .mbox_sram_resp(0),

    .rv_ecc_sts(rv_ecc_sts_t'{default:1'b0}),

    .clear_obf_secrets(0),
    .scan_mode(0),
    .cptra_obf_key(0),
    .cptra_obf_key_reg(),
    .obf_field_entropy(),
    .obf_uds_seed(),

    .strap_ss_caliptra_base_addr(0),
    .strap_ss_mci_base_addr(0),
    .strap_ss_recovery_ifc_base_addr(0),
    .strap_ss_otp_fc_base_addr(0),
    .strap_ss_uds_seed_base_addr(0),
    .strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset(0),
    .strap_ss_num_of_prod_debug_unlock_auth_pk_hashes(0),
    .strap_ss_strap_generic_0(0),
    .strap_ss_strap_generic_1(0),
    .strap_ss_strap_generic_2(0),
    .strap_ss_strap_generic_3(0),
    .ss_debug_intent(0),
    .cptra_ss_debug_intent(),

    .ss_dbg_manuf_enable(),
    .ss_soc_dbg_unlock_level(),
    .ss_generic_fw_exec_ctrl(),
    .nmi_vector(),
    .nmi_intr(),
    .iccm_lock(),
    .iccm_axs_blocked(0),

    .cptra_noncore_rst_b(),
    .cptra_uc_rst_b(),
    .clk_gating_en(),
    .rdc_clk_dis(),
    .fw_update_rst_window(),
    .crypto_error(0),
    
    .cptra_uncore_dmi_reg_en(0),
    .cptra_uncore_dmi_reg_wr_en(0),
    .cptra_uncore_dmi_reg_rdata(),
    .cptra_uncore_dmi_reg_addr(0),
    .cptra_uncore_dmi_reg_wdata(0) 
  );

  //----------------------------------------------------------------
  // clk_gen
  //
  // Always running clock generator process.
  //----------------------------------------------------------------
  always
    begin : clk_gen
      #CLK_HALF_PERIOD;
      clk_tb = !clk_tb;
    end // clk_gen

  //----------------------------------------------------------------
  // sys_monitor()
  //
  // An always running process that creates a cycle counter and
  // conditionally displays information about the DUT.
  //----------------------------------------------------------------
    always @(posedge clk_tb) begin : sys_monitor
      cycle_ctr = (!cptra_rst_b_tb) ? 32'h0 : cycle_ctr + 1;

      // Test timeout monitor
      if(cycle_ctr == MAX_CYCLES) begin
        $error("Hit max cycle count (%0d) .. stopping",cycle_ctr);
        $finish;
      end
    end

  //----------------------------------------------------------------
  // reset_dut()
  //
  // Toggle reset to put the DUT into a well known state.
  //----------------------------------------------------------------
  task reset_dut;
    begin
      $display("*** Toggle reset.");
      cptra_pwrgood_tb = '0;
      cptra_rst_b_tb = 0;
      repeat (5) @(posedge clk_tb);
      cptra_pwrgood_tb = 1;
      
      cptra_rst_b_tb = 1;
      repeat (10) @(posedge clk_tb);
      $display("");
    end
endtask // reset_dut

//----------------------------------------------------------------
  // display_test_results()
  //
  // Display the accumulated test results.
  //----------------------------------------------------------------
task display_test_results;
    begin
      if (error_ctr == 0)
        begin
          $display("*** All %02d test cases completed successfully", tc_ctr);
          $display("* TESTCASE PASSED");
        end
      else
        begin
          $display("*** %02d tests completed - %02d test cases did not complete successfully.",
                   tc_ctr, error_ctr);
          $display("* TESTCASE FAILED");
        end
    end
  endtask // display_test_results

  //----------------------------------------------------------------
  // init_sim()
  //
  // Initialize all counters and testbed functionality as well
  // as setting the DUT inputs to defined values.
  //----------------------------------------------------------------
  task init_sim;
    begin
      cycle_ctr     = 0;
      error_ctr     = 0;
      tc_ctr        = 0;
      temp_ctr      = 0;

      clk_tb        = 0;
      cptra_pwrgood_tb = 0;
      cptra_rst_b_tb    = 0;
    end
endtask // init_sim

task soc_ifc_axi_test;
  axi_resp_e read_resp;
  $display("Reading SHA ACC LOCK reg\n");
  //id = 0, user --> decoded in axi sub
  axi_sub_if.axi_read_single(
    .addr(`CLP_SHA512_ACC_CSR_LOCK),
    .user(0),
    .id(0),
    .lock(0), 
    .data(rdata), 
    .resp(read_resp)
  );
  $display("Return read data over axi = %h\n", rdata);
  $display("Test done\n");
endtask

initial begin
  $display("Starting soc ifc AXI test\n");
  init_sim();
  reset_dut();
  $display("Init and reset done\n");
  soc_ifc_axi_test();
  repeat(100) @(posedge clk_tb);
  $finish;
end
endmodule