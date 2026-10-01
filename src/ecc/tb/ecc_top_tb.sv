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
    parameter   TEST_VECTOR_NUM = 100
)
();

  string      ecc_test_vector_file; // Input test vector file
  string      ecc_test_to_run;      // ECC tests - default, ECC_normal_test, ECC_otf_reset_test
  integer     ecc_test_vector_limit;

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
  wire ecc_busy_tb;
  int max_operation_cycles = 1000000;
  int max_total_cycles = 50000000;
  int unsigned operation_cycles = 0;
  int unsigned total_cycles = 0;
  int unsigned protected_ladder_steps = 0;
  int unsigned last_operation_cycles = 0;
  int unsigned last_ready_wait_cycles = 0;
  int unsigned point_formula_issues = 0;
  int reset_mm_phase = -1;
  int reset_mm_mode = 0;
  localparam MM_FULL_CYCLES =
      3 * ((REG_SIZE + ecc_params_pkg::MULT_RADIX - 1) / ecc_params_pkg::MULT_RADIX + 1);
  wire reset_mm_launch = dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.mult_start_s;
  wire reset_mm_reduce = dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_MULTIPLIER.reduce_i;
  wire [REG_SIZE-1:0] reset_mm_modulus =
      dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_MULTIPLIER.n_i;
  wire reset_mm_inflight = |dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_MULTIPLIER.push_reg;
  wire reset_mm_full_ready = dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.mult_accept_s;
  wire reset_mm_result_ready = dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.mult_ready_s;

  function automatic int unsigned read_reset_decimal(
      input string arg_name, input int unsigned maximum);
    string text;
    int unsigned value, digit;
    if (!$value$plusargs({arg_name, "=%s"}, text) || (text.len() == 0))
      $fatal(1, "%s requires an unsigned decimal value", arg_name);
    value = 0;
    for (int i = 0; i < text.len(); i++) begin
      if ((text[i] < 8'h30) || (text[i] > 8'h39))
        $fatal(1, "%s requires decimal digits only, got '%s'", arg_name, text);
      digit = text[i] - 8'h30;
      if ((value > maximum / 10) ||
          ((value == maximum / 10) && (digit > maximum % 10)))
        $fatal(1, "%s must be in [0,%0d]", arg_name, maximum);
      value = value * 10 + digit;
    end
    return value;
  endfunction

  initial begin
    if ($test$plusargs("ECC_RESET_MM_PHASE"))
      reset_mm_phase = read_reset_decimal("ECC_RESET_MM_PHASE", MM_FULL_CYCLES - 1);
    if ($test$plusargs("ECC_RESET_MM_MODE")) begin
      reset_mm_mode = read_reset_decimal("ECC_RESET_MM_MODE", 2);
      if (reset_mm_phase < 0)
        $fatal(1, "ECC_RESET_MM_MODE requires ECC_RESET_MM_PHASE");
    end
    if ($value$plusargs("ECC_MAX_OP_CYCLES=%d", max_operation_cycles) &&
        (max_operation_cycles <= 0))
      $fatal(1, "ECC_MAX_OP_CYCLES must be positive");
    if ($value$plusargs("ECC_MAX_CYCLES=%d", max_total_cycles) &&
        (max_total_cycles <= 0))
      $fatal(1, "ECC_MAX_CYCLES must be positive");
    $display("ECC watchdog: operation limit %0d cycles, total limit %0d cycles",
             max_operation_cycles, max_total_cycles);
  end

  always @(posedge clk_tb) begin
    total_cycles++;
    if (reset_n_tb && dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.req_digit)
      protected_ladder_steps++;
    if (reset_n_tb &&
        dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.instruction_issue &&
        (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_instr_pipe2_addr inside {
          [ecc_pm_uop_pkg::PA_S:ecc_pm_uop_pkg::PA_E],
          [ecc_pm_uop_pkg::PD_S:ecc_pm_uop_pkg::PD_E],
          [ecc_pm_uop_pkg::PD_PA_S:ecc_pm_uop_pkg::PD_PA_E],
          [ecc_pm_uop_pkg::VER2_PA_S:ecc_pm_uop_pkg::VER2_PA_E]}))
      point_formula_issues++;
    if (!reset_n_tb || !ecc_busy_tb)
      operation_cycles = 0;
    else
      operation_cycles++;
    if (operation_cycles >= max_operation_cycles)
      $fatal(1, "* TESTCASE FAILED: ECC operation exceeded %0d cycles",
             max_operation_cycles);
    if (total_cycles >= max_total_cycles)
      $fatal(1, "* TESTCASE FAILED: ECC simulation exceeded %0d cycles",
             max_total_cycles);
  end

  //reg [31 : 0]  read_data;
  reg [31 : 0]  read_data;
  reg [383: 0]  reg_read_data;

  int                   test_vector_cnt;

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
    case (ecc_test_to_run)
      "default", "ECC_normal_test", "ECC_otf_reset_test",
      "ECC_verify_only_test", "ECC_sca_config_test", "ECC_invalid_point_test": ;
      default: $fatal(1, "* TESTCASE FAILED: unknown ECC_TEST=%s", ecc_test_to_run);
    endcase

    ecc_test_vector_limit = (ecc_test_to_run == "ECC_verify_only_test") ? TEST_VECTOR_NUM : 10;
    if (ecc_test_to_run == "ECC_invalid_point_test")
      ecc_test_vector_limit = 1;
    if ($value$plusargs("ECC_TEST_VECTOR_LIMIT=%d", ecc_test_vector_limit)) begin
      if (ecc_test_vector_limit > TEST_VECTOR_NUM) begin
        ecc_test_vector_limit = TEST_VECTOR_NUM;
      end
      else if (ecc_test_vector_limit < 0) begin
        ecc_test_vector_limit = 0;
      end
      $display("%m: Running with ECC_TEST_VECTOR_LIMIT = %0d", ecc_test_vector_limit);
    end
    if ((ecc_test_to_run == "ECC_invalid_point_test") && (ecc_test_vector_limit == 0))
      $fatal(1, "* TESTCASE FAILED: invalid-point test requires a positive control vector");
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
             .busy_o(ecc_busy_tb),
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
      write_single_word(`ECC_REG_ECC_CTRL, cmd);
      #(CLK_PERIOD);
      hsel_i_tb       = 0;
      #(CLK_PERIOD);
    end
  endtask // trig_ECC


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
      start_time = cycle_ctr;
      wait_ready();
      last_ready_wait_cycles = cycle_ctr - start_time;

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
      last_operation_cycles = end_time;
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
      start_time = cycle_ctr;
      wait_ready();
      last_ready_wait_cycles = cycle_ctr - start_time;

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
      last_operation_cycles = end_time;
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
    reg             hw_verify_pass;
    reg             fw_verify_pass;
    
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

      // Explicit hardware verification result must be read before zeroize clears it
      read_single_word(`ECC_REG_ECC_STATUS);
      hw_verify_pass = read_data[`ECC_REG_ECC_STATUS_VERIFY_PASS_LOW];

      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize

      end_time = cycle_ctr - start_time;
      $display("*** verifying test processing time = %01d cycles.", end_time);
      $display("privkey    : 0x%96x", test_vector.privkey);

      fw_verify_pass = (verify_r == test_vector.R);

      if (fw_verify_pass)
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

      // ECC_STATUS.VERIFY_PASS must always agree with the returned ECC_VERIFY_R data
      if (hw_verify_pass !== fw_verify_pass)
        begin
          $display("*** ERROR: TC %0d ECC_STATUS.VERIFY_PASS = %0b but ECC_VERIFY_R comparison = %0b",
                   tc_number, hw_verify_pass, fw_verify_pass);
          error_ctr = error_ctr + 1;
        end
    end
  endtask // ecc_verifying_test

  //----------------------------------------------------------------
  // ecc_verify_negative_test()
  //
  // Perform a single negative verification with a public-data mutation.
  //----------------------------------------------------------------
  task ecc_verify_negative_test(input test_vector_t test_vector);
    operand_t       verify_r;
    reg             hw_verify_pass;

    begin
      wait_ready();

      $display("*** verify negative test started.");
      tc_ctr = tc_ctr + 1;

      write_block(`ECC_REG_ECC_MSG_0, test_vector.hashed_msg ^ operand_t'(1));
      write_block(`ECC_REG_ECC_PUBKEY_X_0, test_vector.pubkey.x);
      write_block(`ECC_REG_ECC_PUBKEY_Y_0, test_vector.pubkey.y);
      write_block(`ECC_REG_ECC_SIGN_R_0, test_vector.R);
      write_block(`ECC_REG_ECC_SIGN_S_0, test_vector.S);

      trig_ECC(ECC_CMD_VERIFYING);
      wait_ready();

      read_block(`ECC_REG_ECC_VERIFY_R_0);
      verify_r = reg_read_data;

      read_single_word(`ECC_REG_ECC_STATUS);
      hw_verify_pass = read_data[`ECC_REG_ECC_STATUS_VERIFY_PASS_LOW];

      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize

      if ((verify_r != test_vector.R) && !hw_verify_pass)
        begin
          $display("*** TC %0d verify negative successful.", tc_ctr);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d verify negative NOT successful.", tc_ctr);
          $display("Expected mismatch from R: 0x%96x", test_vector.R);
          $display("Got:                      0x%96x", verify_r);
          $display("ECC_STATUS.VERIFY_PASS:   %0b", hw_verify_pass);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // ecc_verify_negative_test

  task ecc_invalid_point_test(input test_vector_t test_vector);
    reg [31:0] status;
    reg [REG_SIZE-1:0] result;
    int unsigned start_issues;
    int unsigned start_cycle;
    bit rejected;
    begin
      if ((test_vector.pubkey.x >= PRIME) || (test_vector.pubkey.y >= PRIME) ||
          (test_vector.pubkey.y == '0) || (point_formula_issues == 0))
        $fatal(1, "* TESTCASE FAILED: invalid-point test requires a valid canonical KAT and an exercised formula monitor");

      for (int shared = 0; shared < 2; shared++) begin
        for (int point_case = 0; point_case < 2; point_case++) begin
          reset_dut();
          wait_ready();
          tc_ctr++;
          write_single_word(`ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R,
                            `ECC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK);
          write_single_word(`ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R,
                            `ECC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_INTERNAL_EN_MASK);
          write_block(`ECC_REG_ECC_MSG_0, test_vector.hashed_msg);
          // With valid nonzero Y, (X,0) is off-curve; (0,0) is also off-curve.
          write_block(`ECC_REG_ECC_PUBKEY_X_0,
                      point_case == 0 ? test_vector.pubkey.x : operand_t'('0));
          write_block(`ECC_REG_ECC_PUBKEY_Y_0, '0);
          write_block(`ECC_REG_ECC_SIGN_R_0, test_vector.R);
          write_block(`ECC_REG_ECC_SIGN_S_0, test_vector.S);
          write_block(`ECC_REG_ECC_PRIVKEY_IN_0, test_vector.privkeyB);
          write_block(`ECC_REG_ECC_IV_0, test_vector.IV);

          start_issues = point_formula_issues;
          start_cycle = cycle_ctr;
          trig_ECC(shared ? ECC_CMD_DH_SHARED : ECC_CMD_VERIFYING);
          read_single_word(`ECC_REG_ECC_STATUS);
          while (read_data[`ECC_REG_ECC_STATUS_READY_LOW] !== 1'b1)
            read_single_word(`ECC_REG_ECC_STATUS);
          #(2 * CLK_PERIOD);
          read_single_word(`ECC_REG_ECC_STATUS);
          status = read_data;
          read_block(shared ? `ECC_REG_ECC_DH_SHARED_KEY_0 : `ECC_REG_ECC_VERIFY_R_0);
          result = reg_read_data;

          rejected = (error_intr_tb === 1'b1) &&
                     (dut.ecc_dsa_ctrl_i.error_flag_reg === 1'b1) &&
                     !$isunknown(dut.ecc_dsa_ctrl_i.pk_chk_reg) &&
                     (dut.ecc_dsa_ctrl_i.pk_chk_reg != '0) &&
                     (status[`ECC_REG_ECC_STATUS_READY_LOW] === 1'b1) &&
                     (status[`ECC_REG_ECC_STATUS_VALID_LOW] === 1'b0) &&
                     (status[`ECC_REG_ECC_STATUS_VERIFY_PASS_LOW] === 1'b0) &&
                     (point_formula_issues == start_issues) &&
                     (shared ? (result === '0) : (result === ~test_vector.R));
          if (rejected) begin
            $display("*** invalid point rejected: shared=%0d case=%0d cycles=%0d formula_issues=%0d",
                     shared, point_case, cycle_ctr - start_cycle,
                     point_formula_issues - start_issues);
          end
          else begin
            error_ctr++;
            $display("*** ERROR: invalid point not safely rejected: shared=%0d case=%0d status=%h error_intr=%b error_flag=%b pk_check_nonzero=%b formula_issues=%0d",
                     shared, point_case, status, error_intr_tb,
                     dut.ecc_dsa_ctrl_i.error_flag_reg,
                     (dut.ecc_dsa_ctrl_i.pk_chk_reg != '0),
                     point_formula_issues - start_issues);
          end
        end
      end
      reset_dut();
    end
  endtask



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
    reg           hw_verify_pass;
    reg           fw_verify_pass;

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

      // Explicit hardware verification result must be read before zeroize clears it
      read_single_word(`ECC_REG_ECC_STATUS);
      hw_verify_pass = read_data[`ECC_REG_ECC_STATUS_VERIFY_PASS_LOW];

      trig_ECC(`ECC_REG_ECC_CTRL_ZEROIZE_MASK); //zeroize

      fw_verify_pass = (verify_r == test_vector.R);

      if (fw_verify_pass)
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

      // ECC_STATUS.VERIFY_PASS must always agree with the returned ECC_VERIFY_R data
      if (hw_verify_pass !== fw_verify_pass)
        begin
          $display("*** ERROR: TC %0d ECC_STATUS.VERIFY_PASS = %0b but ECC_VERIFY_R comparison = %0b",
                   tc_ctr, hw_verify_pass, fw_verify_pass);
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

        // Zeroize must also clear the explicit hardware verification result
        read_single_word(`ECC_REG_ECC_STATUS);
        if (read_data[`ECC_REG_ECC_STATUS_VERIFY_PASS_LOW] !== 1'b0)
          begin
            $display("*** ERROR: TC %0d ECC_STATUS.VERIFY_PASS is set after zeroize.", tc_ctr);
            error_ctr = error_ctr + 1;
          end

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

  // IV controls countermeasure randomness, not the golden key/signature.
  task ecc_sca_test(input int vector_index, input test_vector_t test_vector);
    test_vector_t masked_vector;
    int unsigned reference_cycles[3];
    int unsigned start_cycle;
    int unsigned start_steps;
    int unsigned elapsed;
    int unsigned steps;
    begin
      if (ecc_params_pkg::RND_SIZE != 192)
        $fatal(1, "* TESTCASE FAILED: expected 192-bit scalar blinding");
      masked_vector = test_vector;
      for (int variation = 0; variation < 3; variation++) begin
        case (variation)
          0: masked_vector.IV = test_vector.IV;
          1: masked_vector.IV = '0;
          2: masked_vector.IV = '1;
        endcase
        for (int operation = 0; operation < 3; operation++) begin
          start_cycle = cycle_ctr;
          start_steps = protected_ladder_steps;
          case (operation)
            0: ecc_keygen_test(vector_index, masked_vector);
            1: ecc_signing_test(vector_index, masked_vector);
            2: ecc_DH_sharedkey_test(vector_index, masked_vector);
          endcase
          // Entry wait drains prior reset/zeroize, not the measured operation.
          elapsed = last_operation_cycles;
          if (cycle_ctr - start_cycle != elapsed + last_ready_wait_cycles) begin
            $display("*** ERROR: SCA operation/entry-wait timing accounting mismatch.");
            error_ctr++;
          end
          steps = protected_ladder_steps - start_steps;
          if (steps != REG_SIZE + ecc_params_pkg::RND_SIZE) begin
            $display("*** ERROR: SCA protected ladder has %0d steps, expected %0d.",
                     steps, REG_SIZE + ecc_params_pkg::RND_SIZE);
            error_ctr++;
          end
          if (variation == 0)
            reference_cycles[operation] = elapsed;
          else if (elapsed != reference_cycles[operation]) begin
            $display("*** ERROR: SCA IV changed operation %0d timing: %0d vs %0d.",
                     operation, elapsed, reference_cycles[operation]);
            error_ctr++;
          end
          $display("*** SCA invariant vector=%0d iv=%0d op=%0d steps=%0d cycles=%0d entry_wait=%0d total_cycles=%0d",
                   vector_index, variation, operation, steps, elapsed,
                   last_ready_wait_cycles, cycle_ctr - start_cycle);
        end
      end
    end
  endtask

  //----------------------------------------------------------------
  // ecc_test()
  //
  //----------------------------------------------------------------
  task ecc_test();
    begin  
      if ((reset_mm_phase >= 0) &&
          ((ecc_test_to_run != "ECC_otf_reset_test") || (ecc_test_vector_limit <= 0)))
        $fatal(1, "Active-MM reset requires ECC_otf_reset_test with at least one vector");
      for (int i = 0; i < ecc_test_vector_limit; i++) begin: test_vector_loop
        if ((ecc_test_to_run == "ECC_normal_test") || (ecc_test_to_run == "default")) begin
          ecc_keygen_test(i, test_vectors[i]);
          ecc_signing_test(i, test_vectors[i]);
          ecc_verifying_test(i, test_vectors[i]);
          ecc_DH_sharedkey_test(i, test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_otf_reset_test") begin
          ecc_onthefly_reset_test(i, test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_verify_only_test") begin
          ecc_verifying_test(i, test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_sca_config_test") begin
          ecc_sca_test(i, test_vectors[i]);
        end
        else if (ecc_test_to_run == "ECC_invalid_point_test") begin
          ecc_verifying_test(i, test_vectors[i]);
          ecc_DH_sharedkey_test(i, test_vectors[i]);
          ecc_invalid_point_test(test_vectors[i]);
        end
      end

      if ((ecc_test_to_run != "ECC_verify_only_test") &&
          (ecc_test_to_run != "ECC_invalid_point_test")) begin
        continuous_cmd_test(test_vectors[0]);
        zeroize_test(test_vectors[1]);
        ecc_verify_negative_test(test_vectors[2]);
        ecc_fault_test();
      end
      if ((ecc_test_to_run == "ECC_normal_test") || (ecc_test_to_run == "default"))
        ecc_invalid_point_test(test_vectors[0]);
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

      if ((reset_mm_phase >= 0) && (reset_mm_mode == 1)) begin
        write_block(`ECC_REG_ECC_PUBKEY_X_0, test_vector.pubkey.x);
        write_block(`ECC_REG_ECC_PUBKEY_Y_0, test_vector.pubkey.y);
        write_block(`ECC_REG_ECC_SIGN_R_0, test_vector.R);
        write_block(`ECC_REG_ECC_SIGN_S_0, test_vector.S);
        trig_ECC(ECC_CMD_VERIFYING);
      end
      else
        trig_ECC(ECC_CMD_SIGNING);
      if (reset_mm_phase >= 0)
        wait_for_active_mm_reset();
      else
        #(500 * CLK_PERIOD);

      reset_dut();
      if (reset_mm_phase >= 0)
        check_canceled_mm();
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
      if (reset_mm_phase >= 0) begin
        ecc_signing_test(tc_number, test_vector);
        $display("ECC_MM_RESET_RECOVERY mode=%0d phase=%0d", reset_mm_mode, reset_mm_phase);
      end
    end
  endtask // ecc_onthefly_reset_test

  task wait_for_active_mm_reset;
    bit found;
    int unsigned waited;
    begin
      found = 0;
      waited = 0;
      while (!found && (waited < max_operation_cycles)) begin
        @(posedge clk_tb);
        waited++;
        if (reset_mm_launch === 1'b1) begin
          case (reset_mm_mode)
            0: found = (reset_mm_reduce === 1'b0) &&
                       (reset_mm_modulus === ecc_params_pkg::PRIME);
            1: found = (reset_mm_reduce === 1'b1) &&
                       (reset_mm_modulus === ecc_params_pkg::PRIME);
            2: found = (reset_mm_reduce === 1'b0) &&
                       (reset_mm_modulus === ecc_params_pkg::GROUP_ORDER);
            default: $fatal(1, "* TESTCASE FAILED: invalid active-MM reset mode");
          endcase
        end
      end
      if (!found)
        $fatal(1, "* TESTCASE FAILED: no selected MM launch within %0d cycles", waited);
      @(negedge clk_tb);
      repeat (reset_mm_phase) @(negedge clk_tb);
      if ((reset_mm_inflight !== 1'b1) || (reset_mm_full_ready !== 1'b0))
        $fatal(1, "* TESTCASE FAILED: selected MM is not active at reset phase %0d", reset_mm_phase);
      // Assert away from either clock edge, including just before full completion.
      #1;
      $display("ECC_MM_RESET_ACTIVE mode=%0d phase=%0d result_ready=%0b full_ready=%0b",
               reset_mm_mode, reset_mm_phase, reset_mm_result_ready, reset_mm_full_ready);
    end
  endtask

  task check_canceled_mm;
    begin
      if ((reset_mm_inflight !== 1'b0) ||
          (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mult_pending !== 1'b0) ||
          (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mult_busy !== 1'b0) ||
          (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mult_launch_pending !== 1'b0))
        $fatal(1, "* TESTCASE FAILED: reset did not cancel multiplier ownership/timing state");
      // The legacy full-ready detector settles after reset release.
      repeat (2) @(negedge clk_tb);
      repeat (MM_FULL_CYCLES + 2) begin
        @(negedge clk_tb);
        if ((reset_mm_launch !== 1'b0) || (reset_mm_inflight !== 1'b0) ||
            (reset_mm_full_ready !== 1'b0) || (reset_mm_result_ready !== 1'b0) ||
            (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_instr_s.opcode.mult_we !== 1'b0))
          $fatal(1, "* TESTCASE FAILED: canceled MM produced a stale launch/result/store");
      end
      $display("ECC_MM_RESET_CANCELED mode=%0d phase=%0d", reset_mm_mode, reset_mm_phase);
    end
  endtask



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
      start_time = cycle_ctr;
      wait_ready();
      last_ready_wait_cycles = cycle_ctr - start_time;

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
      last_operation_cycles = end_time;
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
