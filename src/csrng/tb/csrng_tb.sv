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
// csrng_tb.sv
// --------
// Integration test bench to ensure read/write through AHB is working
// with csrng ip.
//
//======================================================================

module csrng_tb
  import csrng_pkg::*;
  import csrng_reg_pkg::*;
  import entropy_src_pkg::*;
  import entropy_src_reg_pkg::*;
  import lc_ctrl_pkg::*;
  import caliptra_prim_mubi_pkg::mubi8_t;
(
`ifdef VERILATOR
  input bit clk_tb
`endif
  );

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;

  parameter CLK_HALF_PERIOD = 2;

  // Max number of poll_register_value() iterations (each iteration burns
  // ~12 clk_tb cycles) before giving up and $fatal'ing instead of hanging
  // the simulation forever.
  parameter POLL_TIMEOUT_ITERS = 5000;

  // The address map.
  parameter ADDR_INTR_STATE                   = 32'h0;
  parameter ADDR_INTR_ENABLE                  = 32'h4;
  parameter ADDR_INTR_TEST                    = 32'h8;
  parameter ADDR_ALERT_TEST                   = 32'hc;
  parameter ADDR_REGWEN                       = 32'h10;
  parameter ADDR_CTRL                         = 32'h14;
  parameter ADDR_CMD_REQ                      = 32'h18;
  parameter ADDR_RESEED_INTERVAL              = 32'h1c;
  parameter ADDR_RESEED_COUNTER_0             = 32'h20;
  parameter ADDR_RESEED_COUNTER_1             = 32'h24;
  parameter ADDR_RESEED_COUNTER_2             = 32'h28;
  parameter ADDR_SW_CMD_STS                   = 32'h2c;
  parameter ADDR_GENBITS_VLD                  = 32'h30;
  parameter ADDR_GENBITS                      = 32'h34;
  parameter ADDR_INT_STATE_READ_ENABLE        = 32'h38;
  parameter ADDR_INT_STATE_READ_ENABLE_REGWEN = 32'h3c;
  parameter ADDR_INT_STATE_NUM                = 32'h40;
  parameter ADDR_INT_STATE_VAL                = 32'h44;
  parameter ADDR_FIPS_FORCE                   = 32'h48;
  parameter ADDR_HW_EXC_STS                   = 32'h4c;
  parameter ADDR_RECOV_ALERT_STS              = 32'h50;
  parameter ADDR_ERR_CODE                     = 32'h54;
  parameter ADDR_ERR_CODE_TEST                = 32'h58;
  parameter ADDR_MAIN_SM_STATE                = 32'h5c;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  parameter AHB_ADDR_WIDTH = 32;
  parameter AHB_DATA_WIDTH = 32;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [31 : 0] cycle_ctr;
  reg [31 : 0] error_ctr;
  reg [31 : 0] tc_ctr;


`ifndef VERILATOR
  reg           clk_tb;
`endif
  reg           reset_n_tb;

  reg [AHB_ADDR_WIDTH-1:0]  haddr_i_tb;
  reg [AHB_DATA_WIDTH-1:0]  hwdata_i_tb;
  reg           hsel_i_tb;
  reg           hwrite_i_tb;
  reg           hready_i_tb;
  reg [1:0]     htrans_i_tb;
  reg [2:0]     hsize_i_tb;

  wire          hresp_o_tb;
  wire          hreadyout_o_tb;
  logic  [AHB_DATA_WIDTH-1:0] hrdata_o_tb;

  reg [31 : 0]  read_data;
  reg [255 : 0] digest_data;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  entropy_src_hw_if_req_t entropy_src_hw_if_req;
  entropy_src_hw_if_rsp_t entropy_src_hw_if_rsp;
  cs_aes_halt_req_t       csrng_cs_aes_halt_req;
  cs_aes_halt_rsp_t       csrng_cs_aes_halt_rsp;
  entropy_src_rng_rsp_t   entropy_src_rng_rsp;

  csrng #(
    .RndCnstCsKeymgrDivNonProduction('0),
    .RndCnstCsKeymgrDivProduction('0),
    .AHBDataWidth(AHB_DATA_WIDTH),
    .AHBAddrWidth(AHB_ADDR_WIDTH)
  ) dut (
      // Clock and reset connections
      .clk_i       (clk_tb),
      .rst_ni      (reset_n_tb),
      // AMBA AHB Lite Interface
      .haddr_i     (haddr_i_tb),
      .hwdata_i    (hwdata_i_tb),
      .hsel_i      (hsel_i_tb),
      .hwrite_i    (hwrite_i_tb),
      .hready_i    (hready_i_tb),
      .htrans_i    (htrans_i_tb),
      .hsize_i     (hsize_i_tb),
      .hresp_o     (hresp_o_tb),
      .hreadyout_o (hreadyout_o_tb),
      .hrdata_o    (hrdata_o_tb),
       // OTP Interface
      .otp_en_csrng_sw_app_read_i(caliptra_prim_mubi_pkg::MuBi8True),
      // Lifecycle broadcast inputs
      .lc_hw_debug_en_i(lc_ctrl_pkg::On),
      // Entropy Interface
      .entropy_src_hw_if_o(entropy_src_hw_if_req),
      .entropy_src_hw_if_i(entropy_src_hw_if_rsp),
      .cs_aes_halt_i      (csrng_cs_aes_halt_req),
      .cs_aes_halt_o      (csrng_cs_aes_halt_rsp),
      // Application Interfaces
      .csrng_cmd_i('0),
      .csrng_cmd_o(),
      // Alerts
      .alert_tx_o  (),
      .alert_rx_i  ('0),
      // Interrupt
      .intr_cs_cmd_req_done_o (),
      .intr_cs_entropy_req_o  (),
      .intr_cs_hw_inst_exc_o  (),
      .intr_cs_fatal_err_o    ()
  );

  //----------------------------------------------------------------
  // clk_gen
  //
  // Clock generator process.
  //----------------------------------------------------------------
`ifndef VERILATOR
  always
    begin : clk_gen
      #CLK_HALF_PERIOD
      clk_tb = !clk_tb;
    end // clk_gen
`endif

  //----------------------------------------------------------------
  // sys_monitor
  //
  // Generates a cycle counter and displays information about
  // the dut as needed.
  //----------------------------------------------------------------
  always @(posedge clk_tb) begin : sys_monitor
      cycle_ctr = (!reset_n_tb) ? 32'h0 : cycle_ctr + 1;
    end


  //----------------------------------------------------------------
  // reset_dut()
  //
  // Toggles reset to force the DUT into a well defined state.
  //----------------------------------------------------------------
    task reset_dut;
    begin
      $display("*** Toggle reset.");
      reset_n_tb = 0;

      repeat (2) @(posedge clk_tb);
      reset_n_tb = 1;

      repeat (2) @(posedge clk_tb);

      $display("");
    end
  endtask // reset_dut


  //----------------------------------------------------------------
  // init_sim()
  //
  // Initialize all counters and testbed functionality as well
  // as setting the DUT inputs to defined values.
  //----------------------------------------------------------------
  task init_sim;
    begin
      error_ctr = '0;
      tc_ctr    = '0;
`ifndef VERILATOR
      clk_tb        = 0;
`endif
      reset_n_tb    = 0;

      haddr_i_tb      = 0;
      hwdata_i_tb     = 0;
      hsel_i_tb       = 0;
      hwrite_i_tb     = 0;
      hready_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hsize_i_tb      = 3'b011;

      csrng_cs_aes_halt_req = '{default:'0};
      entropy_src_rng_rsp = '{default:'0};
      entropy_src_hw_if_rsp = '{default:'0};
    end
  endtask // init_dut


  //----------------------------------------------------------------
  // display_test_result()
  //
  // Display the accumulated test results.
  //----------------------------------------------------------------
  task display_test_result;
    begin
      if (error_ctr == 0)
        begin
          $display("*** All %02d test cases completed successfully.", tc_ctr);
          $display("* TESTCASE PASSED");
        end
      else
        begin
          $display("*** %02d test cases completed.", tc_ctr);
          $display("*** %02d errors detected during testing.", error_ctr);
          $display("* TESTCASE FAILED");
        end
    end
  endtask // display_test_result

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
      hwdata_i_tb     = word;
      hwrite_i_tb     = 1;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hsize_i_tb      = 3'b010;

      @(posedge clk_tb); #1;
      wait(hreadyout_o_tb == 1'b1);
      haddr_i_tb      = 'Z;
      hwrite_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hsel_i_tb       = 0;

      @(posedge clk_tb); #1;
    end
  endtask // write_single_word

  //----------------------------------------------------------------
  // read_single_word()
  //
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_single_word(input [31 : 0]  address);
    begin
      hsel_i_tb       = 1;
      haddr_i_tb      = address;
      hwrite_i_tb     = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hsize_i_tb      = 3'b010;

      @(posedge clk_tb); #1;
      wait(hreadyout_o_tb == 1'b1);
      read_data       = hrdata_o_tb;
      hwdata_i_tb     = 0;
      haddr_i_tb      = 'Z;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hsel_i_tb       = 0;

      @(posedge clk_tb); #1;

    end
  endtask // read_single_word

  //----------------------------------------------------------------
  // read_and_compare()
  //
  // Read a data word from the given address and compare against
  // an expected value.  Increment an error if there is a mismatch.
  //----------------------------------------------------------------
  task read_and_compare(
    input logic [31:0] addr,
    input logic [31:0] expected_data
  );
    read_single_word(addr);
    if (read_data != expected_data) begin
      error_ctr += 1;
      $display("Got: 0x%x Want: 0x%x", read_data, expected_data);
    end
  endtask : read_and_compare

  logic [31:0] test_vector_q[$];  // queue of random input

  //----------------------------------------------------------------
  // poll_register_value()
  //
  // Poll a register until a desired value has been hit.
  //----------------------------------------------------------------
  task poll_register_value(
      input logic [31:0] addr,
      input logic [31:0] value,
      input logic [31:0] mask = 32'hFFFF_FFFF
  );
    int poll_iters;
    begin
      poll_iters = 0;
      do begin
        read_single_word(addr);
        repeat(10) @(posedge clk_tb);
        poll_iters++;
        if (poll_iters >= POLL_TIMEOUT_ITERS) begin
          $display("[TB] ERROR: poll_register_value TIMEOUT @%0t: addr=0x%0h want=0x%0h (mask=0x%0h) got=0x%0h after %0d iterations",
                    $time, addr, value, mask, read_data, poll_iters);
          read_single_word(ADDR_MAIN_SM_STATE);
          $display("[TB]   ADDR_MAIN_SM_STATE   (0x5c) = 0x%0h", read_data);
          read_single_word(ADDR_ERR_CODE);
          $display("[TB]   ADDR_ERR_CODE        (0x54) = 0x%0h", read_data);
          read_single_word(ADDR_RECOV_ALERT_STS);
          $display("[TB]   ADDR_RECOV_ALERT_STS (0x50) = 0x%0h", read_data);
          read_single_word(ADDR_HW_EXC_STS);
          $display("[TB]   ADDR_HW_EXC_STS      (0x4c) = 0x%0h", read_data);
          $fatal(1, "poll_register_value timeout");
        end
      end while ((read_data & mask) != (value & mask));
    end
  endtask

  //----------------------------------------------------------------
  // enable_csrng()
  //
  // Configure the control register and enable csrng module
  //----------------------------------------------------------------
  task enable_csrng;

    // Configure Register
    // 3:0 ENABLE
    // 7:4 SW_APP_ENABLE
    // 11:8 READ_INT_STATE
    // 6 = True, 9 = False
    write_single_word(ADDR_CTRL, 32'h666);

  endtask

  //----------------------------------------------------------------
  // run_smoke_test()
  //
  // Configure and request a rng through the csrng_hw_if interface
  // Once a request is acked, validate against test vector provided
  //----------------------------------------------------------------
  task run_smoke_test;
    $display("Uninitiate Command");
    write_single_word(ADDR_CMD_REQ, 32'h0905);
    repeat (200) @(posedge clk_tb);
    poll_register_value(ADDR_SW_CMD_STS, 32'h6);

    $display("Initiate Command - Writing 48B of seed");
    write_single_word(ADDR_CMD_REQ, 32'h06C1);
    write_single_word(ADDR_CMD_REQ, 32'h73BEC010);
    write_single_word(ADDR_CMD_REQ, 32'h9262474c);
    write_single_word(ADDR_CMD_REQ, 32'h16a30f76);
    write_single_word(ADDR_CMD_REQ, 32'h531b51de);
    write_single_word(ADDR_CMD_REQ, 32'h2ee494e5);
    write_single_word(ADDR_CMD_REQ, 32'hdfec9db3);
    write_single_word(ADDR_CMD_REQ, 32'hcb7a879d);
    write_single_word(ADDR_CMD_REQ, 32'h5600419c);
    write_single_word(ADDR_CMD_REQ, 32'hca79b0b0);
    write_single_word(ADDR_CMD_REQ, 32'hdda33b5c);
    write_single_word(ADDR_CMD_REQ, 32'ha468649e);
    write_single_word(ADDR_CMD_REQ, 32'hdf5d73fa);

    poll_register_value(ADDR_SW_CMD_STS, 32'h6);

    $display("Generate Command - 512b");
    write_single_word(ADDR_CMD_REQ, 32'h4903);
    poll_register_value(ADDR_GENBITS_VLD, 32'h1);

    read_and_compare(ADDR_GENBITS, 32'h378FCA1E);
    read_and_compare(ADDR_GENBITS, 32'hcf763d08);
    read_and_compare(ADDR_GENBITS, 32'h17166e90);
    read_and_compare(ADDR_GENBITS, 32'h0b165308);

    poll_register_value(ADDR_GENBITS_VLD, 32'h1);
    read_and_compare(ADDR_GENBITS, 32'h359fbe3e);
    read_and_compare(ADDR_GENBITS, 32'ha69B1Bf1);
    read_and_compare(ADDR_GENBITS, 32'h14117211);
    read_and_compare(ADDR_GENBITS, 32'hc01a0839);


    poll_register_value(ADDR_GENBITS_VLD, 32'h1);
    read_and_compare(ADDR_GENBITS, 32'h58d7e45d);
    read_and_compare(ADDR_GENBITS, 32'hc5e00eb8);
    read_and_compare(ADDR_GENBITS, 32'hce7ab38f);
    read_and_compare(ADDR_GENBITS, 32'h6e48e546);

    poll_register_value(ADDR_GENBITS_VLD, 32'h1);
    read_and_compare(ADDR_GENBITS, 32'h49de93f9);
    read_and_compare(ADDR_GENBITS, 32'h88A65Ec7);
    read_and_compare(ADDR_GENBITS, 32'hc58a553e);
    read_and_compare(ADDR_GENBITS, 32'h5d6e1012);

    poll_register_value(ADDR_SW_CMD_STS, 32'h6);

    $display("Generate Command - 512b");
    write_single_word(ADDR_CMD_REQ, 32'h4903);
    poll_register_value(ADDR_GENBITS_VLD, 32'h1);

    read_and_compare(ADDR_GENBITS, 32'he48bb8cb);
    read_and_compare(ADDR_GENBITS, 32'h1012c84c);
    read_and_compare(ADDR_GENBITS, 32'h5af8a7f1);
    read_and_compare(ADDR_GENBITS, 32'hd1c07cd9);

    poll_register_value(ADDR_GENBITS_VLD, 32'h1);
    read_and_compare(ADDR_GENBITS, 32'hdf82ab22);
    read_and_compare(ADDR_GENBITS, 32'h771c619b);
    read_and_compare(ADDR_GENBITS, 32'hd40fccb1);
    read_and_compare(ADDR_GENBITS, 32'h87189e99);

    poll_register_value(ADDR_GENBITS_VLD, 32'h1);
    read_and_compare(ADDR_GENBITS, 32'h510494b3);
    read_and_compare(ADDR_GENBITS, 32'h64f7ac0c);
    read_and_compare(ADDR_GENBITS, 32'h2581f391);
    read_and_compare(ADDR_GENBITS, 32'h80b1dc2f);

    poll_register_value(ADDR_GENBITS_VLD, 32'h1);

    read_and_compare(ADDR_GENBITS, 32'h793e01c5);
    read_and_compare(ADDR_GENBITS, 32'h87b107ae);
    read_and_compare(ADDR_GENBITS, 32'hdb17514c);
    read_and_compare(ADDR_GENBITS, 32'ha43c41b7);

    poll_register_value(ADDR_SW_CMD_STS, 32'h6);

  endtask // run_smoke_test

  //----------------------------------------------------------------
  // run_entropy_source_seed_test()
  //
  // Instantiate a csrng and use entropy source seed
  //----------------------------------------------------------------
  task run_entropy_source_seed_test;

    // Reset es_fips: acvp_csrng_test() leaves this latched at 1 (it marks
    // its injected entropy as FIPS-qualifying) and never clears it. This
    // task's poll below expects GENBITS_VLD to read exactly 0x1; if
    // es_fips is still 1 from a prior test, GENBITS_VLD legitimately
    // reads 0x3 (valid+fips) and the unmasked poll never matches.
    entropy_src_hw_if_rsp.es_fips = 1'b0;

    // Uninstantiate first: this task assumes a fresh instance, but it may
    // now run after acvp_csrng_test(), which leaves the SW app instance
    // still instantiated. Without this, the INSTANTIATE below is rejected
    // as an invalid command sequence and never reaches es_req, hanging the
    // wait() below forever.
    $display("Uninitiate Command");
    write_single_word(ADDR_CMD_REQ, 32'h0905);
    repeat (200) @(posedge clk_tb);
    poll_register_value(ADDR_SW_CMD_STS, 32'h6);

    $display("Instantiate Command - Use entropy Source Seed");
    write_single_word(ADDR_CMD_REQ, 32'h901);

    $display("Wait for Request");
    fork
      begin
        wait (entropy_src_hw_if_req.es_req == 1'b1);
      end
      begin
        repeat (POLL_TIMEOUT_ITERS*12) @(posedge clk_tb);
        $display("[TB] ERROR: timeout waiting for entropy_src_hw_if_req.es_req @%0t", $time);
        $fatal(1, "es_req timeout");
      end
    join_any
    disable fork;
    repeat (5000) @(posedge clk_tb);

    entropy_src_hw_if_rsp.es_ack = 1'b1;
    entropy_src_hw_if_rsp.es_bits = 384'h33F63B65F57AD68765693560E743CC5010518E4BF4ECBEBA71DC56AAA08B394311731D9DF763FC5D27E4ED3E4B7DE947;
    repeat (1) @(posedge clk_tb);
    entropy_src_hw_if_rsp.es_ack = 1'b0;

    repeat (30) @(posedge clk_tb);

    $display("Generate Request");
    write_single_word(ADDR_CMD_REQ, 32'h1003);

    poll_register_value(ADDR_GENBITS_VLD, 32'h1);
    read_and_compare(ADDR_GENBITS, 32'h15eb2a44);
    read_and_compare(ADDR_GENBITS, 32'h310851dd);
    read_and_compare(ADDR_GENBITS, 32'hba1365ab);
    read_and_compare(ADDR_GENBITS, 32'h4c7322f4);

    repeat (1000) @(posedge clk_tb);

  endtask // run_entropy_source_seed_test

  //----------------------------------------------------------------
  // hexstr_to_32
  //
  // Extract a 32-bit value from 8 consecutive hex characters in
  // string s starting at character index 'start'.
  //----------------------------------------------------------------
  function automatic logic [31:0] hexstr_to_32(input string s, input int start);
    automatic logic [31:0] val;
    automatic string       sub;
    sub = s.substr(start, start + 7);
    if ($sscanf(sub, "%h", val) != 1) val = '0;
    return val;
  endfunction

  //----------------------------------------------------------------
  // acvp_csrng_test
  //
  // Runs ACVP CTR-DRBG (AES-256, no-df, PR=true) test vectors
  // against the CSRNG IP via the SW interface.
  //
  // Stimulus file: ../stimulus/acvp/ctrDRBG.txt (default; override with
  //   +CSRNG_ACVP_FILE=<path>, e.g. ${CALIPTRA_ROOT}/src/csrng/stimulus/acvp/ctrDRBG.txt)
  //   Format — one line per test case, 10 space-separated fields:
  //   AFT <tgid> <tcid> <predResistance> <ins_ent_96h> <perso_96h>
  //       <f7_96h> <f8_96h> <f9_96h> <f10_96h>
  //
  //   <predResistance> = true | false  (copied directly from JSON)
  //   For false lines: res1_ent_96h and res2_ent_96h are unused;
  //   fill with 96 zeros.  All other hex fields are zero-padded.
  //   perso_96h = 96 zeros when persoString is empty.
  //
  // Response file: ../stimulus/acvp/ctrDRBG_resp.txt (default; override with
  //   +CSRNG_ACVP_RESP_FILE=<path>)
  //   Format: AFT <tcid> <returnedBits_1024hex>
  //   (compare externally against the ACVP .rsp file; the TB does not
  //   embed or check expected results.)
  //
  // Stimulus field mapping (fields 7-10):
  //                    field7      field8      field9      field10
  //   PR=true:        gen1_adata  res1_ent    gen2_adata  res2_ent
  //   PR=false:       res_adata   res_ent     gen1_adata  gen2_adata
  //
  //   In the TB variables: adata1=f7, res1_entropy=f8, adata2=f9, res2_entropy=f10
  //   For PR=false res2_entropy_val holds gen2_adata (no entropy in GEN calls).
  //
  // Per-test sequence, PR=true (SP 800-90A §10.2.1.5.2):
  //   [UNI]  Uninstantiate previous state (skipped on first test)
  //    INS   clen=12  entropy(ins) XOR perso
  //    RES1  clen=12  res1_ent XOR adata1   → GEN1 clen=0  (discard)
  //    RES2  clen=12  res2_ent XOR adata2   → GEN2 clen=0  (capture)
  //
  // Per-test sequence, PR=false:
  //   [UNI]  Uninstantiate previous state (skipped on first test)
  //    INS   clen=12  entropy(ins) XOR perso
  //    RES   clen=12  res1_ent XOR adata1
  //    GEN1  clen=12  adata2                               (discard)
  //    GEN2  clen=12  res2_entropy (= gen2_adata in JSON)  (capture)
  //
  // Command header encoding (SP 800-90A / csrng_pkg.sv):
  //   [2:0]  acmd  INS=1  RES=2  GEN=3  UNI=5
  //   [3]    gap   always 0
  //   [7:4]  clen  number of 32-bit adata words (0-12)
  //   [11:8] flag0 MuBi4: 0x9=False (use entropy_src), 0x6=True
  //   [23:12] glen generate length in 128-bit blocks
  //
  //   INS clen=0  flag0=9 (perso discarded): 32'h0000_0901
  //   RES clen=12 flag0=9:                  32'h0000_09C2
  //   GEN clen=0  flag0=9 glen=32 (PR):     32'h0002_0903
  //   GEN clen=12 flag0=9 glen=32 (no-PR):  32'h0002_09C3
  //   UNI clen=0  flag0=9:                  32'h0000_0905
  //
  // Additional-data words are written to CMD_REQ in reverse chunk order
  // (LSB chunk first) because caliptra_prim_packer_fifo packs 32-bit
  // words LSB-first; GENBITS reads are reassembled the same way in
  // reverse for the same reason (see caliptra-sw's massage_seed()/Words
  // iterator for the reference convention).
  //----------------------------------------------------------------
  task automatic acvp_csrng_test;
    integer fin, fout;
    string  in_fname, out_fname;
    integer result;
    string  test_type;
    int     tgid, tcid;
    string  pr_str;
    string  entropy_str, perso_str;
    string  adata1_str, res1_entropy_str;
    string  adata2_str, res2_entropy_str;
    bit     pr_flag;

    logic [383:0] entropy_val;
    logic [383:0] adata1_val;
    logic [383:0] res1_entropy_val;
    logic [383:0] adata2_val;
    logic [383:0] res2_entropy_val;
    logic [4095:0] got_val;
    bit           is_instantiated;

    begin
      if (!$value$plusargs("CSRNG_ACVP_FILE=%s", in_fname))
        in_fname = "../stimulus/acvp/ctrDRBG.txt";
      if (!$value$plusargs("CSRNG_ACVP_RESP_FILE=%s", out_fname))
        out_fname = "../stimulus/acvp/ctrDRBG_resp.txt";
      is_instantiated = 1'b0;

      fin = $fopen(in_fname, "r");
      if (fin == 0) begin
        $display("[TB] acvp_csrng_test: input file not found, skipping.");
        return;
      end
      fout = $fopen(out_fname, "w");
      if (fout == 0) begin
        $display("[TB] acvp_csrng_test: cannot open output file.");
        $fclose(fin);
        return;
      end

      // Prevent reseed-interval errors across all test cases
      write_single_word(ADDR_RESEED_INTERVAL, 32'hFFFF_FFFF);

      // Prime sw_rdy_sts_q so cmd_rdy asserts before the first INS.
      // Without this, INS is dropped because sw_rdy_sts_q starts at 0.
      write_single_word(ADDR_CMD_REQ, 32'h0000_0905); // UNI
      repeat (200) @(posedge clk_tb);
      poll_register_value(ADDR_SW_CMD_STS, 32'h6);

      while (1) begin
        result = $fscanf(fin, "%s %d %d %s %s %s %s %s %s %s",
                         test_type, tgid, tcid,
                         pr_str,
                         entropy_str,   perso_str,
                         adata1_str,    res1_entropy_str,
                         adata2_str,    res2_entropy_str);
        if (result < 10) break;  // file has exactly 10 fields per line, no embedded expected data
        pr_flag       = (pr_str == "true");

        // Parse 96-hex-char (384-bit) fields, MSB-first (8 chars per word)
        for (int w = 0; w < 12; w++) begin
          entropy_val     [383 - w*32 -: 32] = hexstr_to_32(entropy_str,      w*8);
          adata1_val      [383 - w*32 -: 32] = hexstr_to_32(adata1_str,       w*8);
          res1_entropy_val[383 - w*32 -: 32] = hexstr_to_32(res1_entropy_str, w*8);
          adata2_val      [383 - w*32 -: 32] = hexstr_to_32(adata2_str,       w*8);
          res2_entropy_val[383 - w*32 -: 32] = hexstr_to_32(res2_entropy_str, w*8);
        end

        //------------------------------------------------------------
        // UNI — uninstantiate previous state (skip on first test case
        // because no instance exists after reset)
        //------------------------------------------------------------
        if (is_instantiated) begin
          write_single_word(ADDR_CMD_REQ, 32'h0000_0905); // UNI
          repeat (200) @(posedge clk_tb);
          poll_register_value(ADDR_SW_CMD_STS, 32'h6);
        end

        //------------------------------------------------------------
        // INS — instantiate with entropy XOR personalization string
        //
        // All 13 words (header + 12 adata) are written before we
        // wait for es_req.  The DUT cannot assert es_req until the
        // packer FIFO has accumulated all 12 adata words, so the
        // command write always completes before the entropy request.
        //------------------------------------------------------------
        write_single_word(ADDR_CMD_REQ, 32'h0000_0901); // INS clen=0 (perso always zero)

        // Respond to entropy request with test vector entropy
        wait (entropy_src_hw_if_req.es_req == 1'b1);
        entropy_src_hw_if_rsp.es_bits = entropy_val;
        entropy_src_hw_if_rsp.es_fips = 1'b1;
        entropy_src_hw_if_rsp.es_ack  = 1'b1;
        @(posedge clk_tb);
        entropy_src_hw_if_rsp.es_ack  = 1'b0;
        entropy_src_hw_if_rsp.es_bits = '0;

        poll_register_value(ADDR_SW_CMD_STS, 32'h6);
        is_instantiated = 1'b1;

        //------------------------------------------------------------
        // GEN 1 — PR=true: RES first, then GEN clen=0
        //         PR=false: GEN clen=12 directly
        //         discard all output
        //------------------------------------------------------------
        if (pr_flag) begin
          write_single_word(ADDR_CMD_REQ, 32'h0000_09C2); // RES clen=12
          for (int w = 11; w >= 0; w--)
            write_single_word(ADDR_CMD_REQ, adata1_val[383 - w*32 -: 32]);
          wait (entropy_src_hw_if_req.es_req == 1'b1);
          entropy_src_hw_if_rsp.es_bits = res1_entropy_val;
          entropy_src_hw_if_rsp.es_fips = 1'b1;
          entropy_src_hw_if_rsp.es_ack  = 1'b1;
          @(posedge clk_tb);
          entropy_src_hw_if_rsp.es_ack  = 1'b0;
          entropy_src_hw_if_rsp.es_bits = '0;
          poll_register_value(ADDR_SW_CMD_STS, 32'h6);
          write_single_word(ADDR_CMD_REQ, 32'h0002_0903); // GEN clen=0 glen=32
        end else begin
          // PR=false: one shared RES before GEN1
          write_single_word(ADDR_CMD_REQ, 32'h0000_09C2); // RES clen=12
          for (int w = 11; w >= 0; w--)
            write_single_word(ADDR_CMD_REQ, adata1_val[383 - w*32 -: 32]);
          wait (entropy_src_hw_if_req.es_req == 1'b1);
          entropy_src_hw_if_rsp.es_bits = res1_entropy_val;
          entropy_src_hw_if_rsp.es_fips = 1'b1;
          entropy_src_hw_if_rsp.es_ack  = 1'b1;
          @(posedge clk_tb);
          entropy_src_hw_if_rsp.es_ack  = 1'b0;
          entropy_src_hw_if_rsp.es_bits = '0;
          poll_register_value(ADDR_SW_CMD_STS, 32'h6);
          write_single_word(ADDR_CMD_REQ, 32'h0002_09C3); // GEN clen=12 glen=32
          for (int w = 11; w >= 0; w--)
            write_single_word(ADDR_CMD_REQ, adata2_val[383 - w*32 -: 32]);
        end

        // Drain 32 x 128-bit blocks (128 x 32-bit reads)
        // Mask to bit 0 only: genbits_fips (bit 1) is legitimately 1 here
        // since the injected entropy is marked FIPS-qualifying.
        for (int b = 0; b < 32; b++) begin
          poll_register_value(ADDR_GENBITS_VLD, 32'h1, 32'h1);
          for (int w = 0; w < 4; w++)
            read_single_word(ADDR_GENBITS); // discard
        end
        poll_register_value(ADDR_SW_CMD_STS, 32'h6);

        //------------------------------------------------------------
        // GEN 2 — PR=true: RES first, then GEN clen=0
        //         PR=false: GEN clen=12 directly
        //         capture output for comparison
        //------------------------------------------------------------
        if (pr_flag) begin
          write_single_word(ADDR_CMD_REQ, 32'h0000_09C2); // RES clen=12
          for (int w = 11; w >= 0; w--)
            write_single_word(ADDR_CMD_REQ, adata2_val[383 - w*32 -: 32]);
          wait (entropy_src_hw_if_req.es_req == 1'b1);
          entropy_src_hw_if_rsp.es_bits = res2_entropy_val;
          entropy_src_hw_if_rsp.es_fips = 1'b1;
          entropy_src_hw_if_rsp.es_ack  = 1'b1;
          @(posedge clk_tb);
          entropy_src_hw_if_rsp.es_ack  = 1'b0;
          entropy_src_hw_if_rsp.es_bits = '0;
          poll_register_value(ADDR_SW_CMD_STS, 32'h6);
          write_single_word(ADDR_CMD_REQ, 32'h0002_0903); // GEN clen=0 glen=32
        end else begin
          // PR=false: GEN2 adata is field10 (res2_entropy_val = gen2_adata from JSON)
          write_single_word(ADDR_CMD_REQ, 32'h0002_09C3); // GEN clen=12 glen=32
          for (int w = 11; w >= 0; w--)
            write_single_word(ADDR_CMD_REQ, res2_entropy_val[383 - w*32 -: 32]);
        end

        // Capture 32 x 128-bit blocks into got_val (MSB-first)
        // Mask to bit 0 only (see drain-loop comment above).
        for (int b = 0; b < 32; b++) begin
          poll_register_value(ADDR_GENBITS_VLD, 32'h1, 32'h1);
          for (int w = 0; w < 4; w++) begin
            read_single_word(ADDR_GENBITS);
            got_val[4095 - (b*4 + (3-w))*32 -: 32] = read_data;
          end
        end
        poll_register_value(ADDR_SW_CMD_STS, 32'h6);

        //------------------------------------------------------------
        // Write response file for external comparison against the ACVP
        // .rsp file (the TB does not embed or check expected results).
        //------------------------------------------------------------
        $fwrite(fout, "AFT %0d ", tcid);
        for (int w = 0; w < 128; w++)
          $fwrite(fout, "%08h", got_val[4095 - w*32 -: 32]);
        $fwrite(fout, "\n");
        $fflush(fout);

        $display("[TB] DONE tgid=%0d tcid=%0d", tgid, tcid);
        tc_ctr++;
      end

      $fclose(fin);
      $fclose(fout);
      $display("[TB] acvp_csrng_test complete. %0d tests, %0d errors.",
               tc_ctr, error_ctr);
    end
  endtask // acvp_csrng_test

  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -- Testbench for csrng started --");

      init_sim();
      reset_dut();


      repeat (1000) @(posedge clk_tb);
      enable_csrng();

      acvp_csrng_test();

      run_entropy_source_seed_test();
      run_smoke_test();

      display_test_result();

      $display("   -- Testbench for csrng done. --");
      $finish;
    end // main
endmodule // csrng_tb

//======================================================================
// EOF csrng_tb.sv
//======================================================================
