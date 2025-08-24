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

`include "config_defines.svh"

module soc_ifc_axi_sha_acc_dis_tb
    import soc_ifc_pkg::*;
    import kv_defines_pkg::*;
    import axi_pkg::*;
    ();

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  parameter CLK_HALF_PERIOD = 5000;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;
  parameter MAX_CYCLES = 20_0000;

  parameter AHB_HTRANS_IDLE      = 0;
  parameter AHB_HTRANS_BUSY      = 1;
  parameter AHB_HTRANS_NONSEQ    = 2;
  parameter AHB_HTRANS_SEQ       = 3;

  parameter AHB_ADDR_WIDTH       = `CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC); // 19
  parameter AHB_DATA_WIDTH       = 32;

  parameter AXI_ADDR_WIDTH       = `CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC); // 19;


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

  logic [DW-1:0] rdata, wdata;
  logic [UW-1:0] strap_tb, random_user_tb;

  reg [AHB_ADDR_WIDTH-1:0]  haddr_i_tb;
  reg [AHB_DATA_WIDTH-1:0]  hwdata_i_tb;
  reg           hsel_i_tb;
  reg           hwrite_i_tb; 
  reg           hready_i_tb;
  reg [1:0]     htrans_i_tb;
  reg [2:0]     hsize_i_tb;

  wire          hresp_o_tb;
  wire          hreadyout_o_tb;
  wire [AHB_DATA_WIDTH-1:0] hrdata_o_tb;

  axi_resp_e resp;
  logic [UW-1:0] resp_user;
  logic access;

  typedef enum logic {
    read = 0,
    write = 1
  } rw_e;

 logic aes_input_ready;
 logic aes_output_valid;
 logic aes_status_idle;
 logic aes_req_dv;
 logic aes_req_hold;
 soc_ifc_req_t aes_req_data;
 logic [SOC_IFC_DATA_W-1:0] aes_rdata;
 logic aes_error;

 assign aes_input_ready = '0; // FIXME - when doing AES val either connect or remove fixme and keep unconnected
 assign aes_output_valid = '0; // FIXME - when doing AES val either connect or remove fixme and keep unconnected
 assign aes_status_idle = '0; // FIXME - when doing AES val either connect or remove fixme and keep unconnected
 assign aes_req_hold = '0; // FIXME - when doing AES val either connect or remove fixme and keep unconnected
 assign aes_rdata = '0; // FIXME - when doing AES val either connect or remove fixme and keep unconnected
 assign aes_error = '0; // FIXME - when doing AES val either connect or remove fixme and keep unconnected 

 // Not verified in this bench
 kv_read_t    kv_read;
 kv_rd_resp_t kv_rd_resp = '{error:1'b0,
                             last: 1'b0,
                             read_data: KV_DATA_W'(0)};



  
  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  axi_if #(.AW(AXI_ADDR_WIDTH), .DW(SOC_IFC_DATA_W), .IW(`CALIPTRA_AXI_ID_WIDTH), .UW(SOC_IFC_USER_W)) axi_sub_if(clk_tb, cptra_rst_b_tb);
  axi_if #(.AW(AXI_ADDR_WIDTH), .DW(SOC_IFC_DATA_W), .IW(`CALIPTRA_AXI_ID_WIDTH), .UW(SOC_IFC_USER_W)) axi_mgr_if(clk_tb, cptra_rst_b_tb);

  soc_ifc_top #(
    .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
    .AXI_ID_WIDTH  (8             ),
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH)
    ) dut (
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

    .aes_input_ready,
    .aes_output_valid,
    .aes_status_idle,
    .aes_req_dv,
    .aes_req_hold,
    .aes_req_data,
    .aes_rdata,
    .aes_error, 

    .recovery_data_avail(1'b0),
    .recovery_image_activated(1'b0),

    .security_state({2'b11, 1'b0}),

    .generic_input_wires(64'h0),
    .BootFSM_BrkPoint(1'b0),
    .generic_output_wires(),

    .s_axi_w_if(axi_sub_if.w_sub),
    .s_axi_r_if(axi_sub_if.r_sub),

    .haddr_i(haddr_i_tb),
    .hwdata_i(hwdata_i_tb),
    .hsel_i(hsel_i_tb),
    .hwrite_i(hwrite_i_tb),
    .hready_i(hready_i_tb),
    .htrans_i(htrans_i_tb),
    .hsize_i(hsize_i_tb),

    .hresp_o(hresp_o_tb),
    .hreadyout_o(hreadyout_o_tb),
    .hrdata_o(hrdata_o_tb),

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
    .mbox_sram_resp(39'h0),

    .rv_ecc_sts(rv_ecc_sts_t'{default:1'b0}),

    // Clear KeyVault secrets
    .debugUnlock_or_scan_mode_switch(1'b0),

    .clear_obf_secrets(1'b0),
    .scan_mode(1'b0),
    .cptra_obf_key(256'h0),
    .cptra_obf_key_reg(),
    .cptra_obf_field_entropy_vld(1'b0),
    .cptra_obf_field_entropy(256'h0),
    .obf_field_entropy(),
    .cptra_obf_uds_seed_vld(1'b0),
    .cptra_obf_uds_seed(512'h0),
    .obf_uds_seed(),
    .obf_hek_seed(),

    // kv interface
    .kv_read   (kv_read   ),
    .kv_rd_resp(kv_rd_resp),

    .strap_ss_caliptra_base_addr(64'h0),
    .strap_ss_mci_base_addr(64'h0),
    .strap_ss_recovery_ifc_base_addr(64'h0),
    .strap_ss_external_staging_area_base_addr(64'h0),
    .strap_ss_otp_fc_base_addr(64'h0),
    .strap_ss_uds_seed_base_addr(64'h0),
    .strap_ss_key_release_base_addr(64'h0),
    .strap_ss_key_release_key_size(16'h0),
    .strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset(0),
    .strap_ss_num_of_prod_debug_unlock_auth_pk_hashes(0),
    .strap_ss_strap_generic_0(0),
    .strap_ss_strap_generic_1(0),
    .strap_ss_strap_generic_2(0),
    .strap_ss_strap_generic_3(0),
    .strap_ss_caliptra_dma_axi_user(strap_tb),
    .ss_debug_intent(1'b0),
    .cptra_ss_debug_intent(),

    .ss_dbg_manuf_enable(),
    .ss_soc_dbg_unlock_level(),
    .ss_generic_fw_exec_ctrl(),

    // Subsystem mode OCP LOCK status
    .ss_ocp_lock_en(1'b0),
    .ss_ocp_lock_in_progress(),
    .ss_key_release_key_size(),

    .nmi_vector(),
    .nmi_intr(),
    .iccm_lock(),
    .iccm_axs_blocked(1'b0),

    .cptra_noncore_rst_b(),
    .cptra_uc_rst_b(),
    .clk_gating_en(),
    .rdc_clk_dis(),
    .fw_update_rst_window(),
    .crypto_error(1'b0),
    
    .cptra_uncore_dmi_reg_en(1'b0),
    .cptra_uncore_dmi_reg_wr_en(1'b0),
    .cptra_uncore_dmi_reg_rdata(),
    .cptra_uncore_dmi_reg_addr(7'h0),
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
      $display("*** Toggle pwrgood/reset.");
      cptra_pwrgood_tb = '0;
      cptra_rst_b_tb = 0;
      #(2*CLK_PERIOD);
      cptra_pwrgood_tb = 1;
      #(2*CLK_PERIOD);
      cptra_rst_b_tb = 1;
      // repeat (2) @(posedge clk_tb);
      $display("");
    end
endtask // reset_dut

//----------------------------------------------------------------
// warm_reset_dut()
//
// Toggle reset to put the DUT into a well known state.
//----------------------------------------------------------------
task warm_reset_dut;
  begin
    $display("*** Toggle reset.");
    cptra_rst_b_tb = 0;
    cptra_pwrgood_tb = 1;
    #(4*CLK_PERIOD);
    cptra_rst_b_tb = 1;
    // repeat (2) @(posedge clk_tb);
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

      haddr_i_tb      = 0;
      hwdata_i_tb     = 0;
      hsel_i_tb       = 0;
      hwrite_i_tb     = 0;
      hready_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hsize_i_tb      = 3'b011;

      //reset w_mgr
      axi_mgr_if.awready = 0;
      axi_mgr_if.wready = 0;
      axi_mgr_if.bvalid = 0;
      axi_mgr_if.bid = 0;
      axi_mgr_if.bresp = 0;

      //reset r_mgr
      axi_mgr_if.arready = 0;
      axi_mgr_if.rdata = 0;
      axi_mgr_if.rresp = 0;
      axi_mgr_if.rid = 0;
      axi_mgr_if.rlast = 0;
      axi_mgr_if.rvalid = 0;
      
      //reset w_sub
      axi_sub_if.awaddr = 0;
      axi_sub_if.awburst = 0;
      axi_sub_if.awsize = 0;
      axi_sub_if.awlen = 0;
      axi_sub_if.awuser = 0;
      axi_sub_if.awid = 0;
      axi_sub_if.awlock = 0;
      axi_sub_if.awvalid = 0;
      axi_sub_if.wdata = 0;
      axi_sub_if.wstrb = 0;
      axi_sub_if.wvalid = 0;
      axi_sub_if.wlast = 0;
      axi_sub_if.bready = 0;

      //reset r_sub
      axi_sub_if.araddr = 0;
      axi_sub_if.arburst = 0;
      axi_sub_if.arsize = 0;
      axi_sub_if.arlen = 0;
      axi_sub_if.aruser = 0;
      axi_sub_if.arid = 0;
      axi_sub_if.arlock = 0;
      axi_sub_if.arvalid = 0;
      axi_sub_if.rready = 0;

      random_user_tb = 0;
      access = 1;
    end
endtask // init_sim

task axi_txn_check(input axi_resp_e resp, input rw_e rw);
  logic error;
  if ((resp == AXI_RESP_SLVERR) | (resp == AXI_RESP_DECERR))
    error = 1;
  else 
    error = 0;

  if (error & (rw == read)) begin //read
    $error("AXI Read error");
  end
  else if (error & (rw == write)) begin //write
    $error("AXI Write error");
  end

endtask

//----------------------------------------------------------------
  // write_single_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
task write_single_word(input [31 : 0]  address,
  input [31 : 0] word);
begin
  hsel_i_tb       = 1;
  haddr_i_tb      = address;
  hwrite_i_tb     = 1;
  hready_i_tb     = 1;
  htrans_i_tb     = AHB_HTRANS_NONSEQ;
  hsize_i_tb      = 3'b010;
  #(CLK_PERIOD);

  haddr_i_tb      = 'Z;
  hwdata_i_tb     = word;
  hwrite_i_tb     = 0;
  htrans_i_tb     = AHB_HTRANS_IDLE;
end
endtask // write_single_word

//----------------------------------------------------------------
  // read_single_word()
  //
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
logic [63:0] read_data;
task read_single_word(input [31 : 0]  address);
  begin
    hsel_i_tb       = 1;
    haddr_i_tb      = address;
    hwrite_i_tb     = 0;
    hready_i_tb     = 1;
    htrans_i_tb     = AHB_HTRANS_NONSEQ;
    hsize_i_tb      = 3'b010;
    #(CLK_PERIOD);
    
    hwdata_i_tb     = 0;
    haddr_i_tb     = 'Z;
    htrans_i_tb     = AHB_HTRANS_IDLE;
    read_data = hrdata_o_tb;
  end
endtask // read_single_word
//-----------------------------------------
task axi_sha_access_test;

  access = $urandom_range(0,1);

  #(10*CLK_PERIOD);
  $display("Clearing SHA LOCK over AHB\n");
  write_single_word(`CLP_SHA512_ACC_CSR_LOCK, 32'h1);

  //wait for write to go through
  #(CLK_PERIOD);
  hsel_i_tb       = 0;

  #(2*CLK_PERIOD);

  //id = 0, user --> decoded in axi sub
  random_user_tb = access ? strap_tb : $urandom();
  
  $display("-----------------");
  $display("Testing access with user %h with strap set to user %h", random_user_tb, strap_tb);
  $display("-----------------\n");

  $display("Attempt to acquire SHA ACC LOCK reg over AXI\n");
  axi_sub_if.axi_read_single(
    .addr(`CLP_SHA512_ACC_CSR_LOCK),
    .user(random_user_tb),
    .id($urandom()),
    .lock(0), 
    .data(rdata), 
    .resp_user(resp_user),
    .resp(resp)
  );

  axi_sub_if.axi_read_single(
    .addr(`CLP_SHA512_ACC_CSR_LOCK),
    .user(random_user_tb),
    .id($urandom()),
    .lock(0), 
    .data(rdata), 
    .resp_user(resp_user),
    .resp(resp)
  );

  if (rdata == 1) begin
    $display("SHA Acc Lock acquired");
    if (random_user_tb != dut.i_sha512_acc_top.hwif_out.USER.USER.value) begin
      $error("AXI request USER was not correctly latched into the SHA USER reg!");
      $display("* TESTCASE FAILED");
      $finish;
    end
  end
  else
    $display("SHA Acc Lock not acquired");

  if ((rdata == 'h1) & (strap_tb != random_user_tb)) begin
    $error("SHA Acc Lock acquired over AXI unexpectedly!");
    $display("* TESTCASE FAILED");
    $finish;
  end
  else if ((rdata != 'h1) & (strap_tb == random_user_tb)) begin
    $error("SHA Acc Lock not acquired over AXI as expected for the allowed user!");
    $display("* TESTCASE FAILED");
    $finish;
  end

  //Add checks here to make sure these accesses below don't go through for random users
  axi_sub_if.axi_write_single(
    .addr(`CLP_SHA512_ACC_CSR_MODE),
    .user(random_user_tb),
    .id(0),
    .lock(0),
    .data('h1),
    .write_user(random_user_tb),
    .resp_user(resp_user),
    .resp(resp)
  );

  axi_sub_if.axi_read_single(
    .addr(`CLP_SHA512_ACC_CSR_MODE),
    .user(random_user_tb),
    .id(0),
    .lock(0), 
    .data(rdata),
    .resp_user(resp_user), 
    .resp(resp)
  );

  if ((rdata == 1) & (strap_tb == random_user_tb)) begin
    $display("SHA mode set to 1 over AXI");
  end
  else if ((rdata != 1) & (strap_tb == random_user_tb)) begin
    $error("SHA512 Mode not set to expected value for allowed user");
    $display("* TESTCASE FAILED");
    $finish;
  end
  else if ((rdata == 1) & (strap_tb != random_user_tb)) begin
    $error("SHA512 Mode set by invalid user!");
    $display("* TESTCASE FAILED");
    $finish;
  end

  axi_sub_if.axi_write_single(
    .addr(`CLP_SHA512_ACC_CSR_DLEN),
    .user(random_user_tb),
    .id(0),
    .lock(0),
    .data('h1),
    .resp_user(resp_user),
    .write_user(random_user_tb),
    .resp(resp)
  );

  axi_sub_if.axi_read_single(
    .addr(`CLP_SHA512_ACC_CSR_DLEN),
    .user(random_user_tb),
    .id(0),
    .lock(0), 
    .data(rdata),
    .resp_user(resp_user), 
    .resp(resp)
  );

  //TODO add dlen variable
  if ((rdata == 1) & (strap_tb == random_user_tb)) begin
    $display("SHA dlen set to 1 over AXI");
  end
  else if ((rdata != 1) & (strap_tb == random_user_tb)) begin
    $error("SHA512 dlen not set to expected value for allowed user");
    $display("* TESTCASE FAILED");
    $finish;
  end
  else if ((rdata == 1) & (strap_tb != random_user_tb)) begin
    $error("SHA512 dlen set by invalid user!");
    $display("* TESTCASE FAILED");
    $finish;
  end

  wdata = $urandom();
  axi_sub_if.axi_write_single(
    .addr(`CLP_SHA512_ACC_CSR_DATAIN),
    .user(random_user_tb),
    .id(0),
    .lock(0),
    .data(wdata),
    .write_user(random_user_tb),
    .resp_user(resp_user),
    .resp(resp)
  );

  axi_sub_if.axi_read_single(
    .addr(`CLP_SHA512_ACC_CSR_DATAIN),
    .user(random_user_tb),
    .id(0),
    .lock(0), 
    .data(rdata),
    .resp_user(resp_user), 
    .resp(resp)
  );

  if ((rdata == wdata) & (strap_tb == random_user_tb)) begin
    $display("SHA datain set to 1 over AXI");
  end
  else if ((rdata != wdata) & (strap_tb == random_user_tb)) begin
    $error("SHA512 datain not set to expected value for allowed user");
    $display("* TESTCASE FAILED");
    $finish;
  end
  else if ((rdata == wdata) & (strap_tb != random_user_tb)) begin
    $error("SHA512 datain set by invalid user!");
    $display("* TESTCASE FAILED");
    $finish;
  end
  

  axi_sub_if.axi_write_single(
    .addr(`CLP_SHA512_ACC_CSR_EXECUTE),
    .user(random_user_tb),
    .id(0),
    .lock(0),
    .data('h1),
    .write_user(random_user_tb),
    .resp_user(resp_user),
    .resp(resp)
  );

  axi_sub_if.axi_read_single(
    .addr(`CLP_SHA512_ACC_CSR_EXECUTE),
    .user(random_user_tb),
    .id(0),
    .lock(0), 
    .data(rdata),
    .resp_user(resp_user),
    .resp(resp)
  );

  if ((rdata == 1) & (strap_tb == random_user_tb)) begin
    $display("SHA execute set to 1 over AXI");
  end
  else if ((rdata != 1) & (strap_tb == random_user_tb)) begin
    $error("SHA512 execute not set to expected value for allowed user");
    $display("* TESTCASE FAILED");
    $finish;
  end
  else if ((rdata == 1) & (strap_tb != random_user_tb)) begin
    $error("SHA512 execute set by invalid user!");
    $display("* TESTCASE FAILED");
    $finish;
  end

if (strap_tb == random_user_tb) begin
  $display("Waiting for SHA status\n");
  while (rdata[1] != 1) begin
    axi_sub_if.axi_read_single(
      .addr(`CLP_SHA512_ACC_CSR_STATUS),
      .user(random_user_tb),
      .id(0),
      .lock(0), 
      .data(rdata),
      .resp_user(resp_user), 
      .resp(resp)
    );
  end
  $display("SHA status read over AXI = %h\n", rdata);
end

endtask

initial begin
  $display("Starting AXI sha access test\n");
  strap_tb = $urandom();
  init_sim();
  reset_dut();
  $display("Init and reset done\n");
  axi_sha_access_test();
  
  $display("Issuing cold reset\n");
  init_sim();
  reset_dut();
  #(CLK_PERIOD);
  
  $display("Restarting AXI sha access test\n");
  axi_sha_access_test();

  $display("Issuing warm reset\n");
  init_sim();
  warm_reset_dut();
  #(CLK_PERIOD);

  $display("Restarting AXI sha access test\n");
  axi_sha_access_test();

  repeat(100) @(posedge clk_tb);
  $display("* TESTCASE PASSED");
  $finish;
end
endmodule
