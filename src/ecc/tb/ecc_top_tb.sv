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
// ecc_arith_unit_tb.sv
// --------
// 
//
//
//======================================================================

`default_nettype none
`include "caliptra_reg_defines.svh"
`include "caliptra_reg_field_defines.svh"

module ecc_top_tb 
    import kv_defines_pkg::*;
#(
    parameter   TEST_VECTOR_NUM = 10
)
();

  string      ecc_test_vector_file; // Input test vector file
  string      ecc_p384_test_vector_file; // L5 dualcurve: optional P-384 sidecar KAT
  string      ecc_test_to_run;      // ECC tests - default, ECC_normal_test, ECC_otf_reset_test

  localparam ECC_CMD_KEYGEN              = 2'b01;
  localparam ECC_CMD_SIGNING             = 2'b10;
  localparam ECC_CMD_VERIFYING           = 2'b11;
  localparam ECC_CMD_DH_SHARED           = (1 << `ECC_REG_ECC_CTRL_DH_SHAREDKEY_LOW);
  
  parameter           R_WIDTH                   = 384;
  typedef bit         [R_WIDTH-1:0]             r_t;
  typedef bit         [383 : 0]                 operand_t;
  typedef struct packed {
      operand_t   x;
      operand_t   y;
  } affn_point_t;

  typedef struct packed {
      operand_t   X;
      operand_t   Y;
      operand_t   Z;
  } proj_point_t;

  typedef struct packed {
      operand_t     hashed_msg;
      operand_t     privkey;
      affn_point_t  pubkey;
      operand_t     R;
      operand_t     S;
      operand_t     seed;
      operand_t     nonce;
      operand_t     IV;
      operand_t     privkeyB;
      operand_t     DH_sharedkey;
  } test_vector_t;

  test_vector_t [TEST_VECTOR_NUM-1:0] test_vectors;
  // L5 dualcurve: parallel P-384 KAT array (when both curves run in one sim)
  test_vector_t [TEST_VECTOR_NUM-1:0] p384_test_vectors;
  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG           = 0;

  parameter CLK_HALF_PERIOD = 5;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  parameter REG_SIZE      = 384;
  parameter PRIME         = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff;
  parameter ADD_NUM_ADDS  = 1;
  parameter ADD_BASE_SZ   = 384;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  // Match caliptra_top SS-mode instantiation for coverage merge compatibility
  parameter AHB_ADDR_WIDTH       = 15;
  parameter AHB_DATA_WIDTH       = 64;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [31 : 0]  cycle_ctr;
  reg [31 : 0]  error_ctr;
  reg [31 : 0]  tc_ctr;

  reg           clk_tb;
  reg           reset_n_tb;
  reg           cptra_pwrgood_tb;

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

  kv_read_t [1:0] kv_read_tb;
  kv_write_t kv_write_tb;
  kv_rd_resp_t [1:0] kv_rd_resp_tb;
  kv_wr_resp_t kv_wr_resp_tb;
  pcr_signing_t pcr_signing_data_tb;

  wire error_intr_tb;
  wire notif_intr_tb;

  //reg [31 : 0]  read_data;
  reg [31 : 0]  read_data;
  reg [383: 0]  reg_read_data;

  int                   test_vector_cnt;

  // L2 P-256 validation: when set, OR CURVE_SEL bit into ECC_CTRL cmd writes
  bit                   curve_sel_g = 1'b0;

  initial begin
    if ($value$plusargs("ECC_TEST_VECTOR_FILE=%s", ecc_test_vector_file)) begin
      $display("%m: Using ECC test vectors from file specified via plusarg: %s", ecc_test_vector_file);
    end else begin
      $display("%m: Please re-run with a valid test vector file.");
      $finish;
    end

    if ($value$plusargs("ECC_TEST=%s", ecc_test_to_run)) begin
      $display("%m: Running with ECC_TEST = %s", ecc_test_to_run);
    end else begin
      ecc_test_to_run = "default";
      $display("%m: Running default test = %s", ecc_test_to_run);
    end

    if (ecc_test_to_run == "ECC_p256_verify_test"        ||
        ecc_test_to_run == "ECC_p256_keygen_test"        ||
        ecc_test_to_run == "ECC_p256_sign_test"          ||
        ecc_test_to_run == "ECC_p256_dualcurve_test"     ||
        ecc_test_to_run == "ECC_p256_keygen_blind_test"  ||
        ecc_test_to_run == "ECC_p256_sign_blind_test"    ||
        ecc_test_to_run == "ECC_p256_kv_illegal_test") begin
      curve_sel_g = 1'b1;
      $display("%m: CURVE_SEL=1 (P-256) enabled for this run");
    end
  end

  //bind coverage file
  ecc_top_cov_bind i_ecc_top_cov_bind();

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  ecc_top #(
             .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH)
            )
            dut (
             .clk(clk_tb),
             .reset_n(reset_n_tb),
             .cptra_pwrgood(cptra_pwrgood_tb),

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

             .kv_read(kv_read_tb),
             .kv_write(kv_write_tb),
             .kv_rd_resp(kv_rd_resp_tb),
             .kv_wr_resp(kv_wr_resp_tb),
             .pcr_signing_data(pcr_signing_data_tb),
             .busy_o(),
             .error_intr(error_intr_tb),
             .notif_intr(notif_intr_tb),
             .ocp_lock_in_progress(1'b0),
             .debugUnlock_or_scan_mode_switch('0)
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
  always
    begin : sys_monitor
      #(CLK_PERIOD);
      cycle_ctr = cycle_ctr + 1;
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
      reset_n_tb = 0;

      #(2 * CLK_PERIOD);
      cptra_pwrgood_tb = 1;

      #(2 * CLK_PERIOD);
      reset_n_tb = 1;

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
      cycle_ctr = 32'h00000000;
      error_ctr = 32'h00000000;
      tc_ctr    = 32'h00000000;

      clk_tb        = 0;
      reset_n_tb    = 0;
      cptra_pwrgood_tb = 0;

      haddr_i_tb      = 0;
      hwdata_i_tb     = 0;
      hsel_i_tb       = 0;
      hwrite_i_tb     = 0;
      hready_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hsize_i_tb      = 3'b011;

      kv_rd_resp_tb   = '0;
      kv_wr_resp_tb   = '0;
      pcr_signing_data_tb = '0;
    end
  endtask // init_dut


  //----------------------------------------------------------------
  // wait_ready()
  //
  // Wait for the ready flag in the dut to be set.
  // (Actually we wait for either ready or valid to be set.)
  //
  // Note: It is the callers responsibility to call the function
  // when the dut is actively processing and will in fact at some
  // point set the flag.
  //----------------------------------------------------------------
  task wait_ready;
    begin
      read_single_word(`ECC_REG_ECC_STATUS);
      while (read_data == 0)
        begin
          read_single_word(`ECC_REG_ECC_STATUS);
        end
    end
  endtask // wait_ready



  //----------------------------------------------------------------
  // write_single_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_word(input [31 : 0]  address,
                  input [31 : 0] word);
    begin
      hsel_i_tb       = 1;
      haddr_i_tb      = address[AHB_ADDR_WIDTH-1:0];
      hwrite_i_tb     = 1;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hsize_i_tb      = 3'b010;
      #(CLK_PERIOD);

      haddr_i_tb      = 'Z;
      hwdata_i_tb     = address[2] ? {word, 32'b0} : {32'b0, word};
      hwrite_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
    end
  endtask // write_single_word

  
  //----------------------------------------------------------------
  // write_block()
  //
  // Write the given block to the dut.
  //----------------------------------------------------------------
  task write_block(input [31 : 0] addr, input [383 : 0] block);
    begin
      write_single_word(addr,      block[383  : 352]);
      write_single_word(addr+4*1,  block[351  : 320]);
      write_single_word(addr+4*2,  block[319  : 288]);
      write_single_word(addr+4*3,  block[287  : 256]);
      write_single_word(addr+4*4,  block[255  : 224]);
      write_single_word(addr+4*5,  block[223  : 192]);
      write_single_word(addr+4*6,  block[191  : 160]);
      write_single_word(addr+4*7,  block[159  : 128]);
      write_single_word(addr+4*8,  block[127  :  96]);
      write_single_word(addr+4*9,  block[95   :  64]);
      write_single_word(addr+4*10, block[63   :  32]);
      write_single_word(addr+4*11, block[31   :   0]);
    end
  endtask // write_block


  //----------------------------------------------------------------
  // read_word()
  //
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_single_word(input [31 : 0]  address);
    begin
      hsel_i_tb       = 1;
      haddr_i_tb      = address[AHB_ADDR_WIDTH-1:0];
      hwrite_i_tb     = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hsize_i_tb      = 3'b010;
      #(CLK_PERIOD);
      
      hwdata_i_tb     = 0;
      haddr_i_tb      = 'Z;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      read_data       = address[2] ? hrdata_o_tb[63:32] : hrdata_o_tb[31:0];
    end
  endtask // read_word


  //----------------------------------------------------------------
  // read_block()
  //
  // Read the digest in the dut. The resulting digest will be
  // available in the global variable digest_data.
  //----------------------------------------------------------------
  task read_block(input [31 : 0] addr);
    begin
      read_single_word(addr);
      reg_read_data[383 : 352] = read_data;
      read_single_word(addr + 4*1);
      reg_read_data[351 : 320] = read_data;
      read_single_word(addr +  4*2);
      reg_read_data[319 : 288] = read_data;
      read_single_word(addr +  4*3);
      reg_read_data[287 : 256] = read_data;
      read_single_word(addr +  4*4);
      reg_read_data[255 : 224] = read_data;
      read_single_word(addr +  4*5);
      reg_read_data[223 : 192] = read_data;
      read_single_word(addr +  4*6);
      reg_read_data[191 : 160] = read_data;
      read_single_word(addr +  4*7);
      reg_read_data[159 : 128] = read_data;
      read_single_word(addr +  4*8);
      reg_read_data[127 :  96] = read_data;
      read_single_word(addr +  4*9);
      reg_read_data[95  :  64] = read_data;
      read_single_word(addr +  4*10);
      reg_read_data[63  :  32] = read_data;
      read_single_word(addr +  4*11);
      reg_read_data[31  :   0] = read_data;
    end
  endtask // read_digest

  //----------------------------------------------------------------
  // check_name_version()
  //
  // Read the name and version from the DUT.
  //----------------------------------------------------------------
  task check_name_version;
    reg [31 : 0] name0;
    reg [31 : 0] name1;
    reg [31 : 0] version0;
    reg [31 : 0] version1;
    begin

      read_single_word(`ECC_REG_ECC_NAME_0);
      name0 = read_data;
      read_single_word(`ECC_REG_ECC_NAME_1);
      name1 = read_data;
      read_single_word(`ECC_REG_ECC_VERSION_0);
      version0 = read_data;
      read_single_word(`ECC_REG_ECC_VERSION_1);
      version1 = read_data;

      $display("DUT name: %c%c%c%c%c%c%c%c",
               name0[15 :  8], name0[7  :  0],
               name0[31 : 24], name0[23 : 16], 
               name1[15 :  8], name1[7  :  0],
               name1[31 : 24], name1[23 : 16]);
      $display("DUT version: %c%c%c%c%c%c%c%c",
               version0[15 :  8], version0[7  :  0],
               version0[31 : 24], version0[23 : 16],
               version1[15 :  8], version1[7  :  0],
               version1[31 : 24], version1[23 : 16]);
    end
  endtask // check_name_version


  //----------------------------------------------------------------
  // trig_ECC()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task trig_ECC(input [31 : 0] cmd);
    begin
      write_single_word(`ECC_REG_ECC_CTRL,
                        cmd | (curve_sel_g ? `ECC_REG_ECC_CTRL_CURVE_SEL_MASK : 32'h0));
      #(CLK_PERIOD);
      hsel_i_tb       = 0;
      #(CLK_PERIOD);
    end
  endtask // trig_ECC


  //----------------------------------------------------------------
  // drbg_bypass_force / drbg_bypass_release
  //
  // L3/L4 helpers: drive the DSA-ctrl P-256 DRBG-placeholder nets via
  // SV `force` so deterministic privkey / k / blinding values from the
  // exe test-vector can be injected without requiring HMAC-DRBG-P256.
  // Forces:
  //   hmac_drbg_result_p256 <- {128'h0, drbg_val[255:0]}  (KEYGEN privkey
  //                                                       or SIGN k)
  //   lambda_p256, scalar_rnd_p256, masking_rnd_p256 <- '0  (disable all
  //                                                          randomization
  //                                                          for KAT-exact
  //                                                          determinism)
  // Release pairs with each force so subsequent ops re-take the placeholder
  // assigns. Only meaningful under CURVE_SEL=1 (P-256).
  //----------------------------------------------------------------
  task drbg_bypass_force(input bit [255:0] drbg_val);
    begin
      // Identity-blinding variant (L3/L4): hardwires lambda=1, rnds=0
      drbg_bypass_force_blind(drbg_val,
                              {{(384-1){1'b0}}, 1'b1},   // lambda = 1
                              '0,                         // scalar_rnd = 0
                              '0);                        // masking_rnd = 0
    end
  endtask

  // L6 variant: caller supplies non-identity blinding values to spot-check
  // that the engine still produces the KAT-matching public outputs even with
  // randomized internal state (proves blinding cancels at top level).
  task drbg_bypass_force_blind(input bit [255:0] drbg_val,
                               input bit [383:0] lambda_val,
                               input bit [383:0] scalar_rnd_val,
                               input bit [383:0] masking_rnd_val);
    begin
      force dut.ecc_dsa_ctrl_i.hmac_drbg_result_p256 = {128'h0, drbg_val};
      force dut.ecc_dsa_ctrl_i.lambda_p256           = lambda_val;
      force dut.ecc_dsa_ctrl_i.scalar_rnd_p256       = scalar_rnd_val;
      force dut.ecc_dsa_ctrl_i.masking_rnd_p256      = masking_rnd_val;
    end
  endtask

  task drbg_bypass_release();
    begin
      release dut.ecc_dsa_ctrl_i.hmac_drbg_result_p256;
      release dut.ecc_dsa_ctrl_i.lambda_p256;
      release dut.ecc_dsa_ctrl_i.scalar_rnd_p256;
      release dut.ecc_dsa_ctrl_i.masking_rnd_p256;
    end
  endtask

  //----------------------------------------------------------------
  // drbg_bypass_force_p384 / drbg_bypass_release_p384
  //
  // P-384 variant used only for DRBG-cost measurement experiments.
  // Forces the four real-DRBG output nets AND hmac_ready_p384=1 to
  // short-circuit the DRBG wait; the delta vs the unforced baseline
  // is exactly the cycles spent in HMAC-DRBG-P384.
  //----------------------------------------------------------------
  task drbg_bypass_force_p384(input bit [383:0] drbg_val);
    begin
      force dut.ecc_dsa_ctrl_i.hmac_drbg_result_p384 = drbg_val;
      force dut.ecc_dsa_ctrl_i.lambda_p384           = {{(384-1){1'b0}}, 1'b1};
      force dut.ecc_dsa_ctrl_i.scalar_rnd_p384       = '0;
      force dut.ecc_dsa_ctrl_i.masking_rnd_p384      = '0;
      force dut.ecc_dsa_ctrl_i.hmac_ready_p384       = 1'b1;
    end
  endtask

  task drbg_bypass_release_p384();
    begin
      release dut.ecc_dsa_ctrl_i.hmac_drbg_result_p384;
      release dut.ecc_dsa_ctrl_i.lambda_p384;
      release dut.ecc_dsa_ctrl_i.scalar_rnd_p384;
      release dut.ecc_dsa_ctrl_i.masking_rnd_p384;
      release dut.ecc_dsa_ctrl_i.hmac_ready_p384;
    end
  endtask

  //----------------------------------------------------------------
  // ecc_p384_keygen_bypass_test()
  //
  // P-384 KEYGEN with the real HMAC-DRBG-P384 short-circuited via
  // force. Cycle count vs P-384 baseline (ecc_normal_test KEYGEN =
  // 717,151 cycles) isolates the DRBG-P384 contribution.
  //----------------------------------------------------------------
  task ecc_p384_keygen_bypass_test(input [7:0] tc_number,
                                   input test_vector_t test_vector);
    reg [31:0]    start_time;
    reg [31:0]    end_time;
    operand_t     privkey;
    affn_point_t  pubkey;
    begin
      wait_ready();

      $display("*** TC %0d P-384 keygen-bypass test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      start_time = cycle_ctr;

      drbg_bypass_force_p384(test_vector.privkey);

      write_block(`ECC_REG_ECC_SEED_0,  test_vector.seed);
      write_block(`ECC_REG_ECC_NONCE_0, test_vector.nonce);
      write_block(`ECC_REG_ECC_IV_0,    test_vector.IV);

      trig_ECC(ECC_CMD_KEYGEN);

      wait_ready();

      read_block(`ECC_REG_ECC_PRIVKEY_OUT_0); privkey  = reg_read_data;
      read_block(`ECC_REG_ECC_PUBKEY_X_0);    pubkey.x = reg_read_data;
      read_block(`ECC_REG_ECC_PUBKEY_Y_0);    pubkey.y = reg_read_data;

      drbg_bypass_release_p384();

      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK);

      end_time = cycle_ctr - start_time;
      $display("*** P-384 keygen-bypass processing time = %01d cycles.", end_time);

      if ((privkey == test_vector.privkey) &&
          (pubkey.x == test_vector.pubkey.x) &&
          (pubkey.y == test_vector.pubkey.y)) begin
        $display("*** TC %0d P-384 keygen-bypass successful.", tc_number);
        $display("");
      end
      else begin
        $display("*** ERROR: TC %0d P-384 keygen-bypass NOT successful.", tc_number);
        $display("Expected_priv: 0x%96x", test_vector.privkey);
        $display("Got_priv:      0x%96x", privkey);
        $display("Expected_x:    0x%96x", test_vector.pubkey.x);
        $display("Got_x:         0x%96x", pubkey.x);
        $display("Expected_y:    0x%96x", test_vector.pubkey.y);
        $display("Got_y:         0x%96x", pubkey.y);
        $display("");
        error_ctr = error_ctr + 1;
      end
    end
  endtask // ecc_p384_keygen_bypass_test


  //----------------------------------------------------------------
  // ecc_p256_keygen_bypass_test()
  //
  // L3: P-256 KEYGEN with DRBG bypassed via SV force. The exe-generated
  // privkey is force-injected through hmac_drbg_result_p256 so that the
  // engine's KEYGEN scalar = privkey. Lambda/scalar_rnd/masking_rnd
  // forced to 0 makes the blinded scalar = privkey · 1 = privkey, giving
  // a fully deterministic privkey · G computation that must match the
  // exe-generated public key.
  //
  // Pass criterion: read-back PUBKEY_X/Y (and the engine-returned privkey)
  // equal the test_vector on the lower 256 bits (upper 128 bits already
  // masked to 0 by the curve-aware readback).
  //----------------------------------------------------------------
  task ecc_p256_keygen_bypass_test(input [7:0] tc_number,
                                   input test_vector_t test_vector);
    reg [31:0]    start_time;
    reg [31:0]    end_time;
    operand_t     privkey;
    affn_point_t  pubkey;
    begin
      wait_ready();

      $display("*** TC %0d P-256 keygen-bypass test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      start_time = cycle_ctr;

      drbg_bypass_force(test_vector.privkey[255:0]);

      $display("*** TC %0d writing seed value %0h", tc_number, test_vector.seed);
      write_block(`ECC_REG_ECC_SEED_0,  test_vector.seed);
      $display("*** TC %0d writing nonce value %0h", tc_number, test_vector.nonce);
      write_block(`ECC_REG_ECC_NONCE_0, test_vector.nonce);
      $display("*** TC %0d writing IV value %0h",    tc_number, test_vector.IV);
      write_block(`ECC_REG_ECC_IV_0,    test_vector.IV);

      $display("*** TC %0d starting P-256 KEYGEN flow (DRBG bypassed)", tc_number);
      trig_ECC(ECC_CMD_KEYGEN);

      wait_ready();

      read_block(`ECC_REG_ECC_PRIVKEY_OUT_0); privkey  = reg_read_data;
      read_block(`ECC_REG_ECC_PUBKEY_X_0);    pubkey.x = reg_read_data;
      read_block(`ECC_REG_ECC_PUBKEY_Y_0);    pubkey.y = reg_read_data;

      drbg_bypass_release();

      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK);

      end_time = cycle_ctr - start_time;
      $display("*** P-256 keygen-bypass processing time = %01d cycles.", end_time);
      $display("privkey    : 0x%64x", privkey[255:0]);
      $display("pubkeyx    : 0x%64x", pubkey.x[255:0]);
      $display("pubkeyy    : 0x%64x", pubkey.y[255:0]);

      if ((privkey[255:0]  == test_vector.privkey[255:0]) &&
          (pubkey.x[255:0] == test_vector.pubkey.x[255:0]) &&
          (pubkey.y[255:0] == test_vector.pubkey.y[255:0])) begin
        $display("*** TC %0d P-256 keygen-bypass successful.", tc_number);
        $display("");
      end
      else begin
        $display("*** ERROR: TC %0d P-256 keygen-bypass NOT successful.", tc_number);
        $display("Expected_priv: 0x%64x", test_vector.privkey[255:0]);
        $display("Got_priv:      0x%64x", privkey[255:0]);
        $display("Expected_x:    0x%64x", test_vector.pubkey.x[255:0]);
        $display("Got_x:         0x%64x", pubkey.x[255:0]);
        $display("Expected_y:    0x%64x", test_vector.pubkey.y[255:0]);
        $display("Got_y:         0x%64x", pubkey.y[255:0]);
        $display("");
        error_ctr = error_ctr + 1;
      end
    end
  endtask // ecc_p256_keygen_bypass_test


  //----------------------------------------------------------------
  // ecc_p256_sign_bypass_test()
  //
  // L4: P-256 SIGN with DRBG bypassed via SV force. The pre-computed
  // k = (h + r*priv) * s^-1 mod n_p256 (embedded in test_vector.privkeyB
  // by gen_secp256r1_kat.py) is forced through hmac_drbg_result_p256 so
  // the engine's nonce = k. privkey is written via CSR (normal SIGN
  // input path). Result R,S must match exe-generated KAT on lower 256b.
  //----------------------------------------------------------------
  task ecc_p256_sign_bypass_test(input [7:0] tc_number,
                                 input test_vector_t test_vector);
    reg [31:0]    start_time;
    reg [31:0]    end_time;
    operand_t     R;
    operand_t     S;
    begin
      wait_ready();

      $display("*** TC %0d P-256 sign-bypass test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      start_time = cycle_ctr;

      // privkeyB slot in the P-256 KAT carries k (the SIGN nonce).
      drbg_bypass_force(test_vector.privkeyB[255:0]);

      $display("*** TC %0d writing message value %0h", tc_number, test_vector.hashed_msg);
      write_block(`ECC_REG_ECC_MSG_0,        test_vector.hashed_msg);
      $display("*** TC %0d writing private key value %0h", tc_number, test_vector.privkey);
      write_block(`ECC_REG_ECC_PRIVKEY_IN_0, test_vector.privkey);
      $display("*** TC %0d writing seed value %0h",   tc_number, test_vector.seed);
      write_block(`ECC_REG_ECC_SEED_0,       test_vector.seed);
      $display("*** TC %0d writing nonce value %0h",  tc_number, test_vector.nonce);
      write_block(`ECC_REG_ECC_NONCE_0,      test_vector.nonce);
      $display("*** TC %0d writing IV value %0h",     tc_number, test_vector.IV);
      write_block(`ECC_REG_ECC_IV_0,         test_vector.IV);

      $display("*** TC %0d starting P-256 SIGN flow (DRBG bypassed)", tc_number);
      trig_ECC(ECC_CMD_SIGNING);

      wait_ready();

      read_block(`ECC_REG_ECC_SIGN_R_0); R = reg_read_data;
      read_block(`ECC_REG_ECC_SIGN_S_0); S = reg_read_data;

      drbg_bypass_release();

      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK);

      end_time = cycle_ctr - start_time;
      $display("*** P-256 sign-bypass processing time = %01d cycles.", end_time);
      $display("R          : 0x%64x", R[255:0]);
      $display("S          : 0x%64x", S[255:0]);

      if ((R[255:0] == test_vector.R[255:0]) &&
          (S[255:0] == test_vector.S[255:0])) begin
        $display("*** TC %0d P-256 sign-bypass successful.", tc_number);
        $display("");
      end
      else begin
        $display("*** ERROR: TC %0d P-256 sign-bypass NOT successful.", tc_number);
        $display("Expected_R: 0x%64x", test_vector.R[255:0]);
        $display("Got_R:      0x%64x", R[255:0]);
        $display("Expected_S: 0x%64x", test_vector.S[255:0]);
        $display("Got_S:      0x%64x", S[255:0]);
        $display("");
        error_ctr = error_ctr + 1;
      end
    end
  endtask // ecc_p256_sign_bypass_test


  //----------------------------------------------------------------
  // ecc_p256_dualcurve_test()
  //
  // L5: dual-curve interleave in a single sim with no reset between ops.
  // Validates the runtime CURVE_SEL flip handling (ECC_INIT_LAST re-init
  // sequence) introduced to fix the stale-PM-RAM-constants bug.
  //
  // Pattern per TC i (i=0..N-1):
  //   1. curve_sel_g=0 ; P-384 VERIFY  (uses p384_test_vectors[i])
  //   2. curve_sel_g=1 ; P-256 VERIFY  (uses test_vectors[i])
  //   3. curve_sel_g=0 ; P-384 VERIFY  again on same TC
  //   4. curve_sel_g=1 ; P-256 KEYGEN-bypass (uses test_vectors[i])
  //   5. curve_sel_g=0 ; P-384 VERIFY  again
  //   6. curve_sel_g=1 ; P-256 SIGN-bypass   (uses test_vectors[i])
  //
  // Pass: every sub-op matches its KAT. Failure here means the curve
  // switch isn't fully re-initializing engine state.
  //----------------------------------------------------------------
  task ecc_p256_dualcurve_test(input [7:0] tc_number,
                               input test_vector_t p256_vec,
                               input test_vector_t p384_vec);
    begin
      $display("\n*** [DUAL] TC %0d : P-384 VERIFY #A", tc_number);
      curve_sel_g = 1'b0;
      ecc_verifying_test(tc_number, p384_vec);

      $display("\n*** [DUAL] TC %0d : P-256 VERIFY",   tc_number);
      curve_sel_g = 1'b1;
      ecc_verifying_test(tc_number, p256_vec);

      $display("\n*** [DUAL] TC %0d : P-384 VERIFY #B", tc_number);
      curve_sel_g = 1'b0;
      ecc_verifying_test(tc_number, p384_vec);

      $display("\n*** [DUAL] TC %0d : P-256 KEYGEN-bypass", tc_number);
      curve_sel_g = 1'b1;
      ecc_p256_keygen_bypass_test(tc_number, p256_vec);

      $display("\n*** [DUAL] TC %0d : P-384 VERIFY #C", tc_number);
      curve_sel_g = 1'b0;
      ecc_verifying_test(tc_number, p384_vec);

      $display("\n*** [DUAL] TC %0d : P-256 SIGN-bypass",   tc_number);
      curve_sel_g = 1'b1;
      ecc_p256_sign_bypass_test(tc_number, p256_vec);

      // leave curve_sel_g asserted matching ecc_test() loop default
    end
  endtask // ecc_p256_dualcurve_test


  //----------------------------------------------------------------
  // ecc_p256_keygen_blind_test() / ecc_p256_sign_blind_test()
  //
  // L6: non-zero blinding spot-check. Same flows as the L3/L4 bypass
  // tasks but with random non-identity values forced onto lambda /
  // scalar_rnd / masking_rnd. Output (pubkey or R,S) must STILL match
  // the KAT — proves blinding cancels at the top level (the engine is
  // math-correct under randomized internal state).
  //
  // Constraints picked for the forced values:
  //   lambda      : random nonzero, 256b (always < p_p256, never 0)
  //   scalar_rnd  : random nonzero, lower 192b (matches RND_SIZE)
  //   masking_rnd : random nonzero, 256b
  // $urandom seed is deterministic so failures are reproducible.
  //----------------------------------------------------------------
  task ecc_p256_keygen_blind_test(input [7:0] tc_number,
                                  input test_vector_t test_vector);
    reg [31:0]    start_time, end_time;
    operand_t     privkey;
    affn_point_t  pubkey;
    bit [255:0]   lam;
    bit [191:0]   scal_rnd;
    bit [255:0]   msk;
    begin
      wait_ready();
      $display("*** TC %0d P-256 KEYGEN-blind test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      // Pseudo-random blinding values, deterministic per TC.
      lam      = {$urandom(tc_number+32'h1), $urandom, $urandom, $urandom,
                  $urandom, $urandom, $urandom, $urandom};
      if (lam == '0) lam = 256'h1;
      scal_rnd = {$urandom, $urandom, $urandom, $urandom, $urandom, $urandom};
      msk      = {$urandom, $urandom, $urandom, $urandom,
                  $urandom, $urandom, $urandom, $urandom};

      start_time = cycle_ctr;
      drbg_bypass_force_blind(test_vector.privkey[255:0],
                              {128'h0, lam},
                              {192'h0, scal_rnd},
                              {128'h0, msk});

      write_block(`ECC_REG_ECC_SEED_0,  test_vector.seed);
      write_block(`ECC_REG_ECC_NONCE_0, test_vector.nonce);
      write_block(`ECC_REG_ECC_IV_0,    test_vector.IV);

      $display("*** TC %0d KEYGEN-blind lambda=%h scalar_rnd=%h",
               tc_number, lam, scal_rnd);
      trig_ECC(ECC_CMD_KEYGEN);
      wait_ready();

      read_block(`ECC_REG_ECC_PRIVKEY_OUT_0); privkey  = reg_read_data;
      read_block(`ECC_REG_ECC_PUBKEY_X_0);    pubkey.x = reg_read_data;
      read_block(`ECC_REG_ECC_PUBKEY_Y_0);    pubkey.y = reg_read_data;

      drbg_bypass_release();
      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK);

      end_time = cycle_ctr - start_time;
      $display("*** P-256 KEYGEN-blind processing time = %01d cycles.", end_time);

      if ((privkey[255:0]  == test_vector.privkey[255:0]) &&
          (pubkey.x[255:0] == test_vector.pubkey.x[255:0]) &&
          (pubkey.y[255:0] == test_vector.pubkey.y[255:0])) begin
        $display("*** TC %0d P-256 KEYGEN-blind successful.", tc_number);
      end
      else begin
        $display("*** ERROR: TC %0d P-256 KEYGEN-blind NOT successful.", tc_number);
        $display("Expected_x: 0x%64x  Got_x: 0x%64x",
                 test_vector.pubkey.x[255:0], pubkey.x[255:0]);
        $display("Expected_y: 0x%64x  Got_y: 0x%64x",
                 test_vector.pubkey.y[255:0], pubkey.y[255:0]);
        error_ctr = error_ctr + 1;
      end
      $display("");
    end
  endtask // ecc_p256_keygen_blind_test


  task ecc_p256_sign_blind_test(input [7:0] tc_number,
                                input test_vector_t test_vector);
    reg [31:0]   start_time, end_time;
    operand_t    R, S;
    bit [255:0]  lam;
    bit [191:0]  scal_rnd;
    bit [255:0]  msk;
    begin
      wait_ready();
      $display("*** TC %0d P-256 SIGN-blind test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      lam      = {$urandom(tc_number+32'h2), $urandom, $urandom, $urandom,
                  $urandom, $urandom, $urandom, $urandom};
      if (lam == '0) lam = 256'h1;
      scal_rnd = {$urandom, $urandom, $urandom, $urandom, $urandom, $urandom};
      msk      = {$urandom, $urandom, $urandom, $urandom,
                  $urandom, $urandom, $urandom, $urandom};

      start_time = cycle_ctr;
      drbg_bypass_force_blind(test_vector.privkeyB[255:0],   // k
                              {128'h0, lam},
                              {192'h0, scal_rnd},
                              {128'h0, msk});

      write_block(`ECC_REG_ECC_MSG_0,        test_vector.hashed_msg);
      write_block(`ECC_REG_ECC_PRIVKEY_IN_0, test_vector.privkey);
      write_block(`ECC_REG_ECC_SEED_0,       test_vector.seed);
      write_block(`ECC_REG_ECC_NONCE_0,      test_vector.nonce);
      write_block(`ECC_REG_ECC_IV_0,         test_vector.IV);

      $display("*** TC %0d SIGN-blind lambda=%h scalar_rnd=%h",
               tc_number, lam, scal_rnd);
      trig_ECC(ECC_CMD_SIGNING);
      wait_ready();

      read_block(`ECC_REG_ECC_SIGN_R_0); R = reg_read_data;
      read_block(`ECC_REG_ECC_SIGN_S_0); S = reg_read_data;

      drbg_bypass_release();
      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK);

      end_time = cycle_ctr - start_time;
      $display("*** P-256 SIGN-blind processing time = %01d cycles.", end_time);

      if ((R[255:0] == test_vector.R[255:0]) &&
          (S[255:0] == test_vector.S[255:0])) begin
        $display("*** TC %0d P-256 SIGN-blind successful.", tc_number);
      end
      else begin
        $display("*** ERROR: TC %0d P-256 SIGN-blind NOT successful.", tc_number);
        $display("Expected_R: 0x%64x  Got_R: 0x%64x",
                 test_vector.R[255:0], R[255:0]);
        $display("Expected_S: 0x%64x  Got_S: 0x%64x",
                 test_vector.S[255:0], S[255:0]);
        error_ctr = error_ctr + 1;
      end
      $display("");
    end
  endtask // ecc_p256_sign_blind_test


  //----------------------------------------------------------------
  // ecc_p256_kv_illegal_test() - helpers
  //
  // DV for `a-kv-p256-lockout` (RTL committed in 84e01515).
  //
  // The KV path is illegal whenever CURVE_SEL=P256. ecc_dsa_ctrl.sv
  // implements two layers of defense:
  //   1. Field-level swwe = !curve_sel on every ecc_kv_{rd,wr}_*
  //      CTRL field (L563-588) -> SW writes to KV CTRL while
  //      CURVE_SEL=1 are silently dropped.
  //   2. error_flag := kv_under_p256_invalid (L787-791) when
  //      curve_sel_reg=1 AND any KV ctrl flag is asserted.
  //
  // Sequencing: KV CTRL fields gate on the LIVE CURVE_SEL.value, so
  // they must be armed while CURVE_SEL=0, then the dispatch write
  // that asserts CURVE_SEL=1 follows. curve_sel_reg latches at
  // dispatch (prog_cntr==ECC_NOP && cmd_reg!=0, L819-820); next
  // cycle the FSM sees curve_sel_reg=1 with a non-zero KV ctrl
  // flag -> error_flag -> FSM aborts to ECC_NOP.
  //----------------------------------------------------------------
  task kvp256_enable_err_intr();
    begin
      write_single_word(`ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R,
                        `ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK);
      write_single_word(`ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R,
                        `ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_MASK);
    end
  endtask

  // Common per-subtest harness: reset, ready, enable intr, force CURVE_SEL=0
  // (the arming window). Each subtest then writes its KV CTRL register and
  // calls kvp256_dispatch_check_p256().
  task kvp256_subtest_arm();
    begin
      reset_dut();
      wait_ready();
      kvp256_enable_err_intr();
      curve_sel_g = 1'b0;
    end
  endtask

  // Dispatch <cmd> with CURVE_SEL=P256, expect error_flag asserted, then
  // zeroize and confirm error_flag_reg clears. Tag <name> shows up in logs.
  task kvp256_dispatch_check_p256(input string name, input [31:0] cmd);
    begin
      curve_sel_g = 1'b1;
      trig_ECC(cmd);
      #(4 * CLK_PERIOD);

      if (!error_intr_tb || (dut.ecc_dsa_ctrl_i.error_flag_reg !== 1'b1)) begin
        $display("*** ERROR: [KV-P256 %s] expected error_flag asserted (error_intr=%0b error_flag_reg=%0b).",
                 name, error_intr_tb, dut.ecc_dsa_ctrl_i.error_flag_reg);
        error_ctr = error_ctr + 1;
      end else begin
        $display("*** [KV-P256 %s] error_flag fired as expected.", name);
      end

      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK);
      #(4 * CLK_PERIOD);
      if (dut.ecc_dsa_ctrl_i.error_flag_reg !== 1'b0) begin
        $display("*** ERROR: [KV-P256 %s] zeroize did not clear error_flag_reg.", name);
        error_ctr = error_ctr + 1;
      end
    end
  endtask

  // Readback an arming write and check the gating-sensitive low bit is set
  // (i.e. the swwe gate let the write land while CURVE_SEL=0).
  task kvp256_check_armed(input string name, input [31:0] addr, input [31:0] en_mask);
    begin
      read_single_word(addr); 
      if ((read_data & en_mask) == 0) begin
        $display("*** ERROR: [KV-P256 %s] arming write failed; en bit not captured.", name);
        error_ctr = error_ctr + 1;
      end
    end
  endtask


  //----------------------------------------------------------------
  // ecc_p256_kv_illegal_test()
  //
  // Exercises all five OR-terms feeding kv_under_p256_invalid:
  //   A: SIGN  + kv_privkey_read_ctrl_reg.read_en
  //   B: KEYGEN+ kv_seed_read_ctrl_reg.read_en
  //               (also drives kv_seed_data_present, L596)
  //   C: KEYGEN+ kv_write_ctrl_reg.write_en
  //               (also drives dest_keyvault, kv_write_client.sv:98)
  //   D: ECDH  + read_pkey & write_pkey both armed (multi-source)
  //   E: positive control - CURVE_SEL=0 arming must still succeed
  //      and must NOT raise error_flag.
  // Subtest A also asserts the layer-1 swwe drop: a follow-up SW
  // write to KV RD PKEY CTRL while CURVE_SEL=1 must not change the
  // captured entry.
  //----------------------------------------------------------------
  task ecc_p256_kv_illegal_test();
    reg [31:0] rd_pkey_ctrl_val;
    reg [31:0] rd_seed_ctrl_val;
    reg [31:0] wr_pkey_ctrl_val;
    reg [31:0] readback;

    // Auto-complete KV reads (kv_fsm.sv:95): unblocks cmd_reg gating at
    // ecc_dsa_ctrl.sv:361 so the engine dispatches and error_flag can fire.
    kv_rd_resp_tb[0].last = 1'b1;
    kv_rd_resp_tb[1].last = 1'b1;

    rd_pkey_ctrl_val = `ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_MASK |
                       ((32'd5 << `ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_LOW) &
                        `ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_MASK);
    rd_seed_ctrl_val = `ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK |
                       ((32'd7 << `ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_LOW) &
                        `ECC_REG_ECC_KV_RD_SEED_CTRL_READ_ENTRY_MASK);
    wr_pkey_ctrl_val = `ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK |
                       ((32'd9 << `ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_LOW) &
                        `ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_ENTRY_MASK) |
                       `ECC_REG_ECC_KV_WR_PKEY_CTRL_ECC_PKEY_DEST_VALID_MASK;

    // Subtest A: SIGN + read_pkey
    $display("\n*** [KV-P256] subtest A: SIGN + read_pkey armed");
    tc_ctr = tc_ctr + 1;
    kvp256_subtest_arm();
    write_single_word(`ECC_REG_ECC_KV_RD_PKEY_CTRL, rd_pkey_ctrl_val);
    kvp256_check_armed("A", `ECC_REG_ECC_KV_RD_PKEY_CTRL,
                       `ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_MASK);
    kvp256_dispatch_check_p256("A SIGN", ECC_CMD_SIGNING);
    // Layer-1 (swwe) verification: write while CURVE_SEL still =1.
    curve_sel_g = 1'b1;
    write_single_word(`ECC_REG_ECC_KV_RD_PKEY_CTRL,
                      `ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_MASK |
                      ((32'd17 << `ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_LOW) &
                       `ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_MASK));
    read_single_word(`ECC_REG_ECC_KV_RD_PKEY_CTRL); readback = read_data;
    if (((readback >> `ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_ENTRY_LOW) & 5'h1F) == 5'd17) begin
      $display("*** ERROR: [KV-P256 A] swwe gate failed; write under CURVE_SEL=P256 landed.");
      error_ctr = error_ctr + 1;
    end else begin
      $display("*** [KV-P256 A] swwe gate dropped post-dispatch write as expected.");
    end

    // Subtest B: KEYGEN + read_seed (+ kv_seed_data_present)
    $display("\n*** [KV-P256] subtest B: KEYGEN + read_seed armed");
    tc_ctr = tc_ctr + 1;
    kvp256_subtest_arm();
    write_single_word(`ECC_REG_ECC_KV_RD_SEED_CTRL, rd_seed_ctrl_val);
    kvp256_check_armed("B", `ECC_REG_ECC_KV_RD_SEED_CTRL,
                       `ECC_REG_ECC_KV_RD_SEED_CTRL_READ_EN_MASK);
    kvp256_dispatch_check_p256("B KEYGEN", ECC_CMD_KEYGEN);

    // Subtest C: KEYGEN + write_pkey (+ dest_keyvault)
    $display("\n*** [KV-P256] subtest C: KEYGEN + write_pkey armed");
    tc_ctr = tc_ctr + 1;
    kvp256_subtest_arm();
    write_single_word(`ECC_REG_ECC_KV_WR_PKEY_CTRL, wr_pkey_ctrl_val);
    kvp256_check_armed("C", `ECC_REG_ECC_KV_WR_PKEY_CTRL,
                       `ECC_REG_ECC_KV_WR_PKEY_CTRL_WRITE_EN_MASK);
    kvp256_dispatch_check_p256("C KEYGEN", ECC_CMD_KEYGEN);

    // Subtest D: ECDH + read_pkey & write_pkey
    $display("\n*** [KV-P256] subtest D: ECDH + read_pkey & write_pkey armed");
    tc_ctr = tc_ctr + 1;
    kvp256_subtest_arm();
    write_single_word(`ECC_REG_ECC_KV_RD_PKEY_CTRL, rd_pkey_ctrl_val);
    write_single_word(`ECC_REG_ECC_KV_WR_PKEY_CTRL, wr_pkey_ctrl_val);
    kvp256_dispatch_check_p256("D ECDH", ECC_CMD_DH_SHARED);

    // Subtest E (positive control): CURVE_SEL=0 -> arming must work, no error.
    $display("\n*** [KV-P256] subtest E: positive control under CURVE_SEL=P384");
    tc_ctr = tc_ctr + 1;
    reset_dut();
    wait_ready();
    curve_sel_g = 1'b0;
    write_single_word(`ECC_REG_ECC_KV_RD_PKEY_CTRL, rd_pkey_ctrl_val);
    kvp256_check_armed("E", `ECC_REG_ECC_KV_RD_PKEY_CTRL,
                       `ECC_REG_ECC_KV_RD_PKEY_CTRL_READ_EN_MASK);
    if (dut.ecc_dsa_ctrl_i.error_flag_reg !== 1'b0) begin
      $display("*** ERROR: [KV-P256 E] unexpected error_flag under CURVE_SEL=P384.");
      error_ctr = error_ctr + 1;
    end else begin
      $display("*** [KV-P256 E] clean run under CURVE_SEL=P384 as expected.");
    end

    // Leave curve_sel_g asserted to match ecc_test() loop default.
    curve_sel_g = 1'b1;
    reset_dut();
  endtask // ecc_p256_kv_illegal_test


  //----------------------------------------------------------------
  // ecc_keygen_test()
  //
  // Perform a single point multiplication block test.
  //----------------------------------------------------------------
  task ecc_keygen_test(input [7 : 0]  tc_number,
                       input test_vector_t test_vector);
    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    operand_t       privkey;
    affn_point_t    pubkey;
    begin
      wait_ready();

      $display("*** TC %0d keygen test started.", tc_number);
      tc_ctr = tc_ctr + 1;
    
      start_time = cycle_ctr;

      $display("*** TC %0d writing seed value %0h", tc_number, test_vector.seed);
      write_block(`ECC_REG_ECC_SEED_0, test_vector.seed);
      $display("*** TC %0d writing nonce value %0h", tc_number, test_vector.nonce);
      write_block(`ECC_REG_ECC_NONCE_0, test_vector.nonce);
      $display("*** TC %0d writing IV value %0h", tc_number, test_vector.IV);
      write_block(`ECC_REG_ECC_IV_0, test_vector.IV);

      $display("*** TC %0d starting ECC keygen flow", tc_number);
      trig_ECC(ECC_CMD_KEYGEN);
      
      wait_ready();

      $display("*** TC %0d reading PRIVATE KEY", tc_number);
      read_block(`ECC_REG_ECC_PRIVKEY_OUT_0);
      privkey = reg_read_data;

      $display("*** TC %0d reading PUBLIC KEY X", tc_number);
      read_block(`ECC_REG_ECC_PUBKEY_X_0);
      pubkey.x = reg_read_data;

      $display("*** TC %0d reading PUBLIC KEY Y", tc_number);
      read_block(`ECC_REG_ECC_PUBKEY_Y_0);
      pubkey.y = reg_read_data;
      
      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize

      end_time = cycle_ctr - start_time;
      $display("*** keygen test processing time = %01d cycles.", end_time);
      $display("privkey    : 0x%96x", privkey);
      $display("pubkeyx    : 0x%96x", pubkey.x);
      $display("pubkeyy    : 0x%96x", pubkey.y);

      if ((privkey == test_vector.privkey) & (pubkey == test_vector.pubkey))
        begin
          $display("*** TC %0d keygen successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d keygen NOT successful.", tc_number);
          $display("Expected_x: 0x%96x", test_vector.pubkey.x);
          $display("Got:        0x%96x", pubkey.x);
          $display("Expected_y: 0x%96x", test_vector.pubkey.y);
          $display("Got:        0x%96x", pubkey.y);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // ecc_keygen_test


  //----------------------------------------------------------------
  // ecc_signing_test()
  //
  // Perform a single signing operation test.
  //----------------------------------------------------------------
  task ecc_signing_test(input [7 : 0]  tc_number,
                        input test_vector_t test_vector);
    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    operand_t       R;
    operand_t       S;
    
    begin
      wait_ready();

      $display("*** TC %0d signing test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      start_time = cycle_ctr;

      $display("*** TC %0d writing message value %0h", tc_number, test_vector.hashed_msg);
      write_block(`ECC_REG_ECC_MSG_0, test_vector.hashed_msg);
      $display("*** TC %0d writing private key value %0h", tc_number, test_vector.privkey);
      write_block(`ECC_REG_ECC_PRIVKEY_IN_0, test_vector.privkey);
      $display("*** TC %0d writing IV value %0h", tc_number, test_vector.IV);
      write_block(`ECC_REG_ECC_IV_0, test_vector.IV);

      $display("*** TC %0d starting ECC signing flow", tc_number);
      trig_ECC(ECC_CMD_SIGNING);

      wait_ready();

      $display("*** TC %0d reading R value", tc_number);
      read_block(`ECC_REG_ECC_SIGN_R_0);
      R = reg_read_data;

      $display("*** TC %0d reading S value", tc_number);
      read_block(`ECC_REG_ECC_SIGN_S_0);
      S = reg_read_data;
      
      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize

      end_time = cycle_ctr - start_time;
      $display("*** signing test processing time = %01d cycles.", end_time);
      $display("privkey    : 0x%96x", test_vector.privkey);

      if (R == test_vector.R & S == test_vector.S)
        begin
          $display("*** TC %0d signing successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d signing NOT successful.", tc_number);
          $display("Expected_R: 0x%96x", test_vector.R);
          $display("Got:        0x%96x", R);
          $display("Expected_S: 0x%96x", test_vector.S);
          $display("Got:        0x%96x", S);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // ecc_signing_test


  //----------------------------------------------------------------
  // ecc_verifying_test()
  //
  // Perform a single verifying operation test.
  //----------------------------------------------------------------
  task ecc_verifying_test(input [7 : 0]  tc_number,
                        input test_vector_t test_vector);
    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    operand_t       verify_r;
    
    begin
      wait_ready();

      $display("*** TC %0d verifying test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      start_time = cycle_ctr;

      $display("*** TC %0d writing message value %0h", tc_number, test_vector.hashed_msg);
      write_block(`ECC_REG_ECC_MSG_0, test_vector.hashed_msg);
      $display("*** TC %0d writing PUBLIC KEY X value %0h", tc_number, test_vector.pubkey.x);
      write_block(`ECC_REG_ECC_PUBKEY_X_0, test_vector.pubkey.x);
      $display("*** TC %0d writing PUBLIC KEY Y value %0h", tc_number, test_vector.pubkey.y);
      write_block(`ECC_REG_ECC_PUBKEY_Y_0, test_vector.pubkey.y);
      $display("*** TC %0d writing R value %0h", tc_number, test_vector.R);
      write_block(`ECC_REG_ECC_SIGN_R_0, test_vector.R);
      $display("*** TC %0d writing S value %0h", tc_number, test_vector.S);
      write_block(`ECC_REG_ECC_SIGN_S_0, test_vector.S);

      $display("*** TC %0d starting ECC verify flow", tc_number);
      trig_ECC(ECC_CMD_VERIFYING);

      wait_ready();

      $display("*** TC %0d reading ECC_CMD_VERIFYING R value", tc_number);
      read_block(`ECC_REG_ECC_VERIFY_R_0);
      verify_r = reg_read_data;
      
      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize

      end_time = cycle_ctr - start_time;
      $display("*** verifying test processing time = %01d cycles.", end_time);
      $display("privkey    : 0x%96x", test_vector.privkey);

      if (verify_r == test_vector.R)
        begin
          $display("*** TC %0d verifying successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d verifying NOT successful.", tc_number);
          $display("Expected_R: 0x%96x", test_vector.R);
          $display("Got:        0x%96x", verify_r);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // ecc_verifying_test



  //----------------------------------------------------------------
  // continuous_cmd_test()
  //
  //
  // Perform test of chaning the command during the process.
  //----------------------------------------------------------------
  task continuous_cmd_test(input test_vector_t test_vector);
    operand_t     privkey;
    affn_point_t  pubkey;
    operand_t     R;
    operand_t     S;
    operand_t     verify_r;

    begin

      $display("*** continuous_cmd_test started.");

      $display("*** starting ECC keygen flow");
      wait_ready();
      tc_ctr = tc_ctr + 1;
    
      write_block(`ECC_REG_ECC_SEED_0, test_vector.seed);
      write_block(`ECC_REG_ECC_NONCE_0, test_vector.nonce);
      write_block(`ECC_REG_ECC_IV_0, test_vector.IV);

      trig_ECC(ECC_CMD_KEYGEN);
      
      for (int i=0; i<10; i++)
        begin
          trig_ECC(ECC_CMD_SIGNING);
          #(10*CLK_PERIOD);
          trig_ECC(ECC_CMD_KEYGEN);
          #(10*CLK_PERIOD);
          trig_ECC(ECC_CMD_VERIFYING);
          #(10*CLK_PERIOD);
          trig_ECC(ECC_CMD_SIGNING | `ECC_REG_ECC_CTRL_PCR_SIGN_MASK);
          #(10*CLK_PERIOD);
        end

      wait_ready();

      read_block(`ECC_REG_ECC_PRIVKEY_OUT_0);
      privkey = reg_read_data;
      read_block(`ECC_REG_ECC_PUBKEY_X_0);
      pubkey.x = reg_read_data;
      read_block(`ECC_REG_ECC_PUBKEY_Y_0);
      pubkey.y = reg_read_data;
      
      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize

      if ((privkey == test_vector.privkey) & (pubkey == test_vector.pubkey))
        begin
          $display("*** TC %0d keygen successful.", tc_ctr);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d keygen NOT successful.", tc_ctr);
          $display("Expected_x: 0x%96x", test_vector.pubkey.x);
          $display("Got:        0x%96x", pubkey.x);
          $display("Expected_y: 0x%96x", test_vector.pubkey.y);
          $display("Got:        0x%96x", pubkey.y);
          $display("");

          error_ctr = error_ctr + 1;
        end


      $display("*** signing test started.");
      wait_ready();
      tc_ctr = tc_ctr + 1;

      write_block(`ECC_REG_ECC_MSG_0, test_vector.hashed_msg);
      write_block(`ECC_REG_ECC_PRIVKEY_IN_0, test_vector.privkey);
      write_block(`ECC_REG_ECC_IV_0, test_vector.IV);

      trig_ECC(ECC_CMD_SIGNING);

      for (int i=0; i<10; i++)
        begin
          trig_ECC(ECC_CMD_SIGNING);
          #(10*CLK_PERIOD);
          trig_ECC(ECC_CMD_KEYGEN);
          #(10*CLK_PERIOD);
          trig_ECC(ECC_CMD_VERIFYING);
          #(10*CLK_PERIOD);
        end

      wait_ready();

      read_block(`ECC_REG_ECC_SIGN_R_0);
      R = reg_read_data;
      read_block(`ECC_REG_ECC_SIGN_S_0);
      S = reg_read_data;
      
      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize

      if (R == test_vector.R & S == test_vector.S)
        begin
          $display("*** TC %0d signing successful.", tc_ctr);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d signing NOT successful.", tc_ctr);
          $display("Expected_R: 0x%96x", test_vector.R);
          $display("Got:        0x%96x", R);
          $display("Expected_S: 0x%96x", test_vector.S);
          $display("Got:        0x%96x", S);
          $display("");

          error_ctr = error_ctr + 1;
        end

      
      $display("*** verifying test started.");
      wait_ready();
      tc_ctr = tc_ctr + 1;

      write_block(`ECC_REG_ECC_MSG_0, test_vector.hashed_msg);
      write_block(`ECC_REG_ECC_PUBKEY_X_0, test_vector.pubkey.x);
      write_block(`ECC_REG_ECC_PUBKEY_Y_0, test_vector.pubkey.y);
      write_block(`ECC_REG_ECC_SIGN_R_0, test_vector.R);
      write_block(`ECC_REG_ECC_SIGN_S_0, test_vector.S);

      trig_ECC(ECC_CMD_VERIFYING);

      for (int i=0; i<10; i++)
        begin
          trig_ECC(ECC_CMD_SIGNING);
          #(10*CLK_PERIOD);
          trig_ECC(ECC_CMD_KEYGEN);
          #(10*CLK_PERIOD);
          trig_ECC(ECC_CMD_VERIFYING);
          #(10*CLK_PERIOD);
        end

      wait_ready();

      read_block(`ECC_REG_ECC_VERIFY_R_0);
      verify_r = reg_read_data;
      
      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize

      if (verify_r == test_vector.R)
        begin
          $display("*** TC %0d verifying successful.", tc_ctr);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d verifying NOT successful.", tc_ctr);
          $display("Expected_R: 0x%96x", test_vector.R);
          $display("Got:        0x%96x", verify_r);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // continuous_cmd_test


  //----------------------------------------------------------------
  // zeroize_test()
  //
  //----------------------------------------------------------------
  task zeroize_test(input test_vector_t test_vector);
    operand_t     privkey;
    affn_point_t  pubkey;
    operand_t     R;
    operand_t     S;
    operand_t     verify_r;

    begin

      $display("*** zeroize test started.");
      
      for (int i=0; i<2; i++) begin
        // First test: assert zeroize with KEYGEN
        wait_ready();
        write_block(`ECC_REG_ECC_SEED_0, test_vector.seed);
        write_block(`ECC_REG_ECC_NONCE_0, test_vector.nonce);
        write_block(`ECC_REG_ECC_IV_0, test_vector.IV);

        if (i==0) begin
          trig_ECC(ECC_CMD_KEYGEN);
          #(100 * CLK_PERIOD);
          trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize
          #(CLK_PERIOD);
        end
        else begin
          trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK | ECC_CMD_KEYGEN); //zeroize
        end

        wait_ready();

        read_block(`ECC_REG_ECC_PRIVKEY_OUT_0);
        privkey = reg_read_data;
        read_block(`ECC_REG_ECC_PUBKEY_X_0);
        pubkey.x = reg_read_data;
        read_block(`ECC_REG_ECC_PUBKEY_Y_0);
        pubkey.y = reg_read_data;
        
        if ((privkey == 0) & (pubkey == 0))
          begin
            $display("*** TC %0d keygen successful.", tc_ctr);
            $display("");
          end
        else
          begin
            $display("*** ERROR: TC %0d keygen NOT successful.", tc_ctr);
            $display("Got:        0x%96x", pubkey.x);
            $display("Got:        0x%96x", pubkey.y);
            $display("");

            error_ctr = error_ctr + 1;
          end
        tc_ctr = tc_ctr + 1;

        // Second test: assert zeroize with Signing
        wait_ready();
        write_block(`ECC_REG_ECC_MSG_0, test_vector.hashed_msg);
        write_block(`ECC_REG_ECC_PRIVKEY_IN_0, test_vector.privkey);
        write_block(`ECC_REG_ECC_IV_0, test_vector.IV);

        if (i==0) begin
          trig_ECC(ECC_CMD_SIGNING);
          #(100 * CLK_PERIOD);
          trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize
        end
        else begin
          trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK | ECC_CMD_SIGNING); //zeroize
        end

        wait_ready();

        read_block(`ECC_REG_ECC_SIGN_R_0);
        R = reg_read_data;
        read_block(`ECC_REG_ECC_SIGN_S_0);
        S = reg_read_data;
        
        if (R == 0 & S == 0)
          begin
            $display("*** TC %0d signing successful.", tc_ctr);
            $display("");
          end
        else
          begin
            $display("*** ERROR: TC %0d signing NOT successful.", tc_ctr);
            $display("Got:        0x%96x", R);
            $display("Got:        0x%96x", S);
            $display("");

            error_ctr = error_ctr + 1;
          end
        tc_ctr = tc_ctr + 1;

        // Third test: assert zeroize when Verifying is working
        wait_ready();
        write_block(`ECC_REG_ECC_MSG_0, test_vector.hashed_msg);
        write_block(`ECC_REG_ECC_PUBKEY_X_0, test_vector.pubkey.x);
        write_block(`ECC_REG_ECC_PUBKEY_Y_0, test_vector.pubkey.y);
        write_block(`ECC_REG_ECC_SIGN_R_0, test_vector.R);
        write_block(`ECC_REG_ECC_SIGN_S_0, test_vector.S);

        if (i==0) begin
          trig_ECC(ECC_CMD_VERIFYING);
          #(100 * CLK_PERIOD);
          trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize
        end
        else begin
          trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK | ECC_CMD_VERIFYING); //zeroize
        end

        wait_ready();

        read_block(`ECC_REG_ECC_VERIFY_R_0);
        verify_r = reg_read_data;
        
        if (verify_r == 0)
          begin
            $display("*** TC %0d verifying successful.", tc_ctr);
            $display("");
          end
        else
          begin
            $display("*** ERROR: TC %0d verifying NOT successful.", tc_ctr);
            $display("Got:        0x%96x", verify_r);
            $display("");

            error_ctr = error_ctr + 1;
          end
        tc_ctr = tc_ctr + 1;
      end

      $display("*** TC%01d - zeroize test done.", tc_ctr);
    end
  endtask // zeroize_test


  //----------------------------------------------------------------
  // ecc_fault_test()
  //
  //----------------------------------------------------------------
  task ecc_fault_test();
    operand_t       privKey_faulty;
    
    begin
      privKey_faulty = '0;
      wait_ready();

      $display("*** fault test started.");
      tc_ctr = tc_ctr + 1;

      //enable the interrupt
      write_single_word(`ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R, `ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK);
      write_single_word(`ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R, `ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_MASK);

      write_block(`ECC_REG_ECC_PRIVKEY_IN_0, privKey_faulty);
      trig_ECC(ECC_CMD_SIGNING);
      wait_ready();

      #(2 * CLK_PERIOD);  //there are 2 cycles latency to set error_intr

      if (error_intr_tb)
        begin
          $display("*** fault test successful.");
          $display("");
        end
      else
        begin
          $display("*** ERROR: fault test NOT successful.");
          $display("");

          error_ctr = error_ctr + 1;
        end

      trig_ECC(ECC_CMD_SIGNING);
      
      wait_ready();

      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize

      #(2 * CLK_PERIOD);

      if (dut.ecc_dsa_ctrl_i.error_flag_reg == 0) 
        begin
          $display("*** fault test successful.");
          $display("");
        end
      else
        begin
          $display("*** ERROR: fault test NOT successful.");
          $display("");

          error_ctr = error_ctr + 1;
        end

      reset_dut();
    end
  endtask // ecc_fault_test

  //----------------------------------------------------------------
  // ecc_openssl_keygen_test()
  //
  // Perform a single point multiplication block test without hmac-drbg.
  //----------------------------------------------------------------
  task ecc_openssl_keygen_test(input [7 : 0]  tc_number,
                       input test_vector_t test_vector);
    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    reg [383 : 0]   privkey;
    affn_point_t    pubkey;
    begin
      wait_ready();

      $display("*** TC %0d openssl keygen test without hmac-drbg started.", tc_number);
      tc_ctr = tc_ctr + 1;
    
      start_time = cycle_ctr;

      write_block(`ECC_REG_ECC_SEED_0, test_vector.privkey);
      write_block(`ECC_REG_ECC_IV_0, test_vector.IV);

      trig_ECC(ECC_CMD_KEYGEN);
      #(CLK_PERIOD);
      
      wait_ready();

      read_block(`ECC_REG_ECC_PRIVKEY_OUT_0);
      privkey = reg_read_data;

      read_block(`ECC_REG_ECC_PUBKEY_X_0);
      pubkey.x = reg_read_data;

      read_block(`ECC_REG_ECC_PUBKEY_Y_0);
      pubkey.y = reg_read_data;
      
      end_time = cycle_ctr - start_time;
      $display("*** keygen test processing time = %01d cycles.", end_time);
      $display("privkey    : 0x%96x", test_vector.privkey);

      if ((privkey == test_vector.privkey) & (pubkey == test_vector.pubkey))
        begin
          $display("*** TC %0d keygen successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d keygen NOT successful.", tc_number);
          $display("Expected_x: 0x%96x", test_vector.pubkey.x);
          $display("Got:        0x%96x", pubkey.x);
          $display("Expected_y: 0x%96x", test_vector.pubkey.y);
          $display("Got:        0x%96x", pubkey.y);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // ecc_keygen_test

  //----------------------------------------------------------------
  // ecc_test()
  //
  //----------------------------------------------------------------
  task ecc_test();
    begin  
      for (int i = 0; i < 10; i++) begin: test_vector_loop
        if ((ecc_test_to_run == "ECC_normal_test") || (ecc_test_to_run == "default")) begin
          ecc_keygen_test(i, test_vectors[i]);
          ecc_signing_test(i, test_vectors[i]);
          ecc_verifying_test(i, test_vectors[i]);
          ecc_DH_sharedkey_test(i, test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_otf_reset_test") begin
          ecc_onthefly_reset_test(i, test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_p256_verify_test") begin
          ecc_verifying_test(i, test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_p256_keygen_test") begin
          ecc_p256_keygen_bypass_test(i, test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_p256_sign_test") begin
          ecc_p256_sign_bypass_test(i, test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_p256_dualcurve_test") begin
          ecc_p256_dualcurve_test(i, test_vectors[i], p384_test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_p256_keygen_blind_test") begin
          ecc_p256_keygen_blind_test(i, test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_p256_sign_blind_test") begin
          ecc_p256_sign_blind_test(i, test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_p384_keygen_bypass_test") begin
          ecc_p384_keygen_bypass_test(i, test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_p256_kv_illegal_test") begin
          // KV-under-P256 lockout DV: vector-independent, run once on i==0.
          if (i == 0)
            ecc_p256_kv_illegal_test();
        end
      end
      
      if ((ecc_test_to_run != "ECC_p256_verify_test")        &&
          (ecc_test_to_run != "ECC_p256_keygen_test")        &&
          (ecc_test_to_run != "ECC_p256_sign_test")          &&
          (ecc_test_to_run != "ECC_p256_dualcurve_test")     &&
          (ecc_test_to_run != "ECC_p256_keygen_blind_test")  &&
          (ecc_test_to_run != "ECC_p256_sign_blind_test")    &&
          (ecc_test_to_run != "ECC_p256_kv_illegal_test")    &&
          (ecc_test_to_run != "ECC_p384_keygen_bypass_test")) begin
        continuous_cmd_test(test_vectors[0]);
        zeroize_test(test_vectors[1]);
        ecc_fault_test();
      end
    end
  endtask // ecc_test


  //----------------------------------------------------------------
  // ecc_openssl_test()
  //
  //----------------------------------------------------------------
  task ecc_openssl_test();
    begin   
      // The first 6-set test vectors work for keygen, 
      for (int i = 0; i < 6; i++) begin: test_vector_loop
        ecc_onthefly_reset_test(i, test_vectors[i]);
        ecc_openssl_keygen_test(i, test_vectors[i]);
      end
    end
  endtask // ecc_openssl_test

  //----------------------------------------------------------------
  // read_test_vectors()
  //
  //----------------------------------------------------------------
  task read_test_vectors(input string fname);
      integer values_per_test_vector;
      integer line_cnt;
      integer fin;
      integer rv;
      r_t val;    // must be the largest width of any possible value
      test_vector_t test_vector;

      // ATTN: Must match the number of fields generated by gen_mm_test_vectors.py script
      values_per_test_vector = 12;
      line_cnt = 0;
      test_vector_cnt = 0;

      fin = $fopen(fname, "r");
      if (fin == 0)
          $error("Can't open file %s", fname);
      while (!$feof(fin)) begin
          rv = $fscanf(fin, "%h\n", val);
          if (rv != 1) begin
              $error("Failed to read a matching string");
              $fclose(fin);
              $finish;
          end
          // ATTN: the number of cases must be equal to 'values_per_test_vector'.
          // ATTN: the order of values must be the same as in gen_mm_test_vectors.py script.
          case (line_cnt % values_per_test_vector)
              0: test_vector.hashed_msg  = val;
              1: test_vector.privkey     = val;
              2: test_vector.pubkey.x    = val;
              3: test_vector.pubkey.y    = val;
              4: test_vector.seed        = val;
              5: test_vector.nonce       = val;
              6: test_vector.R           = val;
              7: test_vector.S           = val;
              8: test_vector.IV          = val;
              9: test_vector.privkeyB    = val;
              10:begin
                 test_vector.DH_sharedkey   = val;
                 test_vectors[test_vector_cnt] = test_vector;
              end
              11 : test_vector_cnt++;
          endcase
          
          line_cnt++;
      end
      $fclose(fin);

      $display("Read %0d test vectors from %s", test_vector_cnt, fname);
  endtask


  //----------------------------------------------------------------
  // ecc_onthefly_reset_test()
  //
  // Perform a single on the fly reset test.
  //----------------------------------------------------------------
  task ecc_onthefly_reset_test(input [7 : 0]  tc_number,
                        input test_vector_t test_vector);
    reg [383 : 0]   R;
    reg [383 : 0]   S;
    reg [383 : 0]   privkey;
    reg [383 : 0]   pubkey_x;
    reg [383 : 0]   pubkey_y;

    begin
      wait_ready();

      $display("*** TC %0d on the fly reset test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      write_block(`ECC_REG_ECC_MSG_0, test_vector.hashed_msg);
      write_block(`ECC_REG_ECC_PRIVKEY_IN_0, test_vector.privkey);
      write_block(`ECC_REG_ECC_IV_0, test_vector.IV);

      trig_ECC(ECC_CMD_SIGNING);
      #(500 * CLK_PERIOD);

      reset_dut();
      wait_ready();

      read_block(`ECC_REG_ECC_SIGN_R_0);
      R = reg_read_data;

      read_block(`ECC_REG_ECC_SIGN_S_0);
      S = reg_read_data;

      read_block(`ECC_REG_ECC_PRIVKEY_OUT_0);
      privkey = reg_read_data;

      read_block(`ECC_REG_ECC_PUBKEY_X_0);
      pubkey_x = reg_read_data;

      read_block(`ECC_REG_ECC_PUBKEY_Y_0);
      pubkey_y = reg_read_data;
      
      if (R == 0 & S == 0 & privkey == 0 & pubkey_x ==0 & pubkey_y == 0)
        begin
          $display("*** TC %0d on the fly reset test successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d on the fly reset test NOT successful.", tc_number);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // ecc_onthefly_reset_test



  //----------------------------------------------------------------
  // ecc_DH_sharedkey_test()
  //
  // Perform a single DH shared key operation test.
  //----------------------------------------------------------------
  task ecc_DH_sharedkey_test(input [7 : 0]  tc_number,
                        input test_vector_t test_vector);
    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    operand_t       DH_sharedkey;
    
    begin
      wait_ready();

      $display("*** TC %0d DH shared key test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      start_time = cycle_ctr;

      $display("*** TC %0d writing PRIVKEY value %0h", tc_number, test_vector.privkeyB);
      write_block(`ECC_REG_ECC_PRIVKEY_IN_0, test_vector.privkeyB);
      $display("*** TC %0d writing PUBLIC KEY X value %0h", tc_number, test_vector.pubkey.x);
      write_block(`ECC_REG_ECC_PUBKEY_X_0, test_vector.pubkey.x);
      $display("*** TC %0d writing PUBLIC KEY Y value %0h", tc_number, test_vector.pubkey.y);
      write_block(`ECC_REG_ECC_PUBKEY_Y_0, test_vector.pubkey.y);
      $display("*** TC %0d writing IV value %0h", tc_number, test_vector.IV);
      write_block(`ECC_REG_ECC_IV_0, test_vector.IV);

      $display("*** TC %0d starting ECC DH shared key flow", tc_number);
      trig_ECC(ECC_CMD_DH_SHARED);

      wait_ready();

      $display("*** TC %0d reading SHARED KEY", tc_number);
      read_block(`ECC_REG_ECC_DH_SHARED_KEY_0);
      DH_sharedkey = reg_read_data;
      
      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize

      end_time = cycle_ctr - start_time;
      $display("*** DH shared key test processing time = %01d cycles.", end_time);
      $display("privkey    : 0x%96x", test_vector.privkeyB);

      if (DH_sharedkey == test_vector.DH_sharedkey)
        begin
          $display("*** TC %0d DH shared key successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d DH shared key NOT successful.", tc_number);
          $display("Expected_x: 0x%96x", test_vector.DH_sharedkey);
          $display("Got:        0x%96x", DH_sharedkey);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // ecc_DH_sharedkey_test

  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      
      string fname;

      $display("   -= Testbench for ecc started =-");
      $display("    ==============================");
      $display("");

      //fname = "/home/mojtabab/workspace_aha_poc/ws1/Caliptra/src/ecc/tb/test_vectors/ecc_drbg_mbedtls.hex";
      // L5 dualcurve: when a P-384 sidecar KAT is also provided, load it
      // FIRST into the global test_vectors[] (legacy parser), then snapshot
      // into p384_test_vectors[], so the second (P-256) load can repopulate
      // test_vectors[] for the normal P-256 op iteration.
      if ($value$plusargs("ECC_P384_TEST_VECTOR_FILE=%s", ecc_p384_test_vector_file)) begin
        $display("%m: Using P-384 sidecar KAT: %s", ecc_p384_test_vector_file);
        read_test_vectors(ecc_p384_test_vector_file);
        p384_test_vectors = test_vectors;
      end
      read_test_vectors(ecc_test_vector_file);

      init_sim();
      reset_dut();
      check_name_version();

      //ecc_openssl_test();

      
      ecc_test(); 

      display_test_results();
      
      $display("");
      $display("*** ecc simulation done. ***");
      $finish;
    end // main

endmodule // ecc_top_tb
