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

module ecc_top_tb 
    import kv_defines_pkg::*;
#(
    parameter   TEST_VECTOR_NUM = 10
)
();

  string      ecc_test_vector_file; // Input test vector file
  string      ecc_test_to_run;      // ECC tests - default, ECC_normal_test, ECC_otf_reset_test, ECC_sca_config_test

  localparam BASE_ADDR        = 32'h00000000;

  localparam ADDR_NAME0       = BASE_ADDR + 32'h00000000;
  localparam ADDR_NAME1       = BASE_ADDR + 32'h00000004;
  localparam ADDR_VERSION0    = BASE_ADDR + 32'h00000008;
  localparam ADDR_VERSION1    = BASE_ADDR + 32'h0000000C;

  localparam ADDR_CTRL        = BASE_ADDR + 32'h00000010;
  localparam KEYGEN           = 2'b01;
  localparam SIGN             = 2'b10;
  localparam VERIFY           = 2'b11;

  localparam ADDR_STATUS          = BASE_ADDR + 32'h00000018;
  localparam STATUS_READY_BIT = 0;
  localparam STATUS_VALID_BIT = 1;

  localparam ADDR_SCACONFIG       = BASE_ADDR + 32'h00000020;

  localparam ADDR_SEED_START      = BASE_ADDR + 32'h00000080;
  localparam ADDR_SEED_END        = BASE_ADDR + 32'h000000AC;

  localparam ADDR_MSG_START       = BASE_ADDR + 32'h00000100;
  localparam ADDR_MSG_END         = BASE_ADDR + 32'h0000012C;

  localparam ADDR_PRIVKEY_START   = BASE_ADDR + 32'h00000180;
  localparam ADDR_PRIVKEY_END     = BASE_ADDR + 32'h000001AC;

  localparam ADDR_PUBKEYX_START   = BASE_ADDR + 32'h00000200;
  localparam ADDR_PUBKEYX_END     = BASE_ADDR + 32'h0000022C;

  localparam ADDR_PUBKEYY_START   = BASE_ADDR + 32'h00000280;
  localparam ADDR_PUBKEYY_END     = BASE_ADDR + 32'h000002AC;

  localparam ADDR_SIGNR_START     = BASE_ADDR + 32'h00000300;
  localparam ADDR_SIGNR_END       = BASE_ADDR + 32'h0000032C;

  localparam ADDR_SIGNS_START     = BASE_ADDR + 32'h00000380;
  localparam ADDR_SIGNS_END       = BASE_ADDR + 32'h000003AC;

  localparam ADDR_VERIFY_R_START  = BASE_ADDR + 32'h00000400;
  localparam ADDR_VERIFY_R_END    = BASE_ADDR + 32'h0000042C;

  localparam ADDR_IV_START        = BASE_ADDR + 32'h00000480;
  localparam ADDR_IV_END          = BASE_ADDR + 32'h000004AC;
  
  localparam ADDR_NONCE_START     = BASE_ADDR + 32'h00000500;
  localparam ADDR_NONCE_END       = BASE_ADDR + 32'h0000052C;
  
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

  parameter AHB_ADDR_WIDTH       = 32;
  parameter AHB_DATA_WIDTH       = 32;

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

  kv_read_t [2:0] kv_read_tb;
  kv_write_t kv_write_tb;
  kv_rd_resp_t [2:0] kv_rd_resp_tb;
  kv_wr_resp_t kv_wr_resp_tb;
  pcr_signing_t pcr_signing_data_tb;

  wire error_intr_tb;
  wire notif_intr_tb;

  //reg [31 : 0]  read_data;
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
  end

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  ecc_top #(
             .AHB_DATA_WIDTH(32),
             .AHB_ADDR_WIDTH(32)
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

             .error_intr(error_intr_tb),
             .notif_intr(notif_intr_tb)
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
      reset_n_tb = 0;
      cptra_pwrgood_tb = 0;

      #(2 * CLK_PERIOD);

      @(posedge clk_tb);
      reset_n_tb = 1;
      cptra_pwrgood_tb = 1;

      #(2 * CLK_PERIOD);

      @(posedge clk_tb);
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
      read_single_word(ADDR_STATUS);
      while (hrdata_o_tb == 0)
        begin
          read_single_word(ADDR_STATUS);
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
      hsel_i_tb       <= 1;
      haddr_i_tb      <= address;
      hwrite_i_tb     <= 1;
      hready_i_tb     <= 1;
      htrans_i_tb     <= AHB_HTRANS_NONSEQ;
      hsize_i_tb      <= 3'b010;
      
      @(posedge clk_tb);
      haddr_i_tb      <= 'Z;
      hwdata_i_tb     <= word;
      hwrite_i_tb     <= 0;
      htrans_i_tb     <= AHB_HTRANS_IDLE;
      wait(hreadyout_o_tb == 1'b1);

      @(posedge clk_tb);
      hsel_i_tb       <= 0;
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
      hsel_i_tb       <= 1;
      haddr_i_tb      <= address;
      hwrite_i_tb     <= 0;
      hready_i_tb     <= 1;
      htrans_i_tb     <= AHB_HTRANS_NONSEQ;
      hsize_i_tb      <= 3'b010;
      
      @(posedge clk_tb);
      hwdata_i_tb     <= 0;
      haddr_i_tb      <= 'Z;
      htrans_i_tb     <= AHB_HTRANS_IDLE;
      wait(hreadyout_o_tb == 1'b1);

      @(posedge clk_tb);
      hsel_i_tb       <= 0;      
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
      reg_read_data[383 : 352] = hrdata_o_tb;
      read_single_word(addr + 4*1);
      reg_read_data[351 : 320] = hrdata_o_tb;
      read_single_word(addr +  4*2);
      reg_read_data[319 : 288] = hrdata_o_tb;
      read_single_word(addr +  4*3);
      reg_read_data[287 : 256] = hrdata_o_tb;
      read_single_word(addr +  4*4);
      reg_read_data[255 : 224] = hrdata_o_tb;
      read_single_word(addr +  4*5);
      reg_read_data[223 : 192] = hrdata_o_tb;
      read_single_word(addr +  4*6);
      reg_read_data[191 : 160] = hrdata_o_tb;
      read_single_word(addr +  4*7);
      reg_read_data[159 : 128] = hrdata_o_tb;
      read_single_word(addr +  4*8);
      reg_read_data[127 :  96] = hrdata_o_tb;
      read_single_word(addr +  4*9);
      reg_read_data[95  :  64] = hrdata_o_tb;
      read_single_word(addr +  4*10);
      reg_read_data[63  :  32] = hrdata_o_tb;
      read_single_word(addr +  4*11);
      reg_read_data[31  :   0] = hrdata_o_tb;
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

      read_single_word(ADDR_NAME0);
      name0 = hrdata_o_tb;
      read_single_word(ADDR_NAME1);
      name1 = hrdata_o_tb;
      read_single_word(ADDR_VERSION0);
      version0 = hrdata_o_tb;
      read_single_word(ADDR_VERSION1);
      version1 = hrdata_o_tb;

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
  task trig_ECC(input [2 : 0] cmd);
    begin
      write_single_word(ADDR_CTRL  , cmd);
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
    reg [383 : 0]   privkey;
    affn_point_t    pubkey;
    begin
      wait_ready();

      $display("*** TC %0d keygen test started.", tc_number);
      tc_ctr = tc_ctr + 1;
    
      start_time = cycle_ctr;

      $display("*** TC %0d writing seed value %0h", tc_number, test_vector.seed);
      write_block(ADDR_SEED_START, test_vector.seed);
      $display("*** TC %0d writing nonce value %0h", tc_number, test_vector.nonce);
      write_block(ADDR_NONCE_START, test_vector.nonce);
      $display("*** TC %0d writing IV value %0h", tc_number, test_vector.IV);
      write_block(ADDR_IV_START, test_vector.IV);

      $display("*** TC %0d starting ECC keygen flow", tc_number);
      trig_ECC(KEYGEN);
      #(CLK_PERIOD);
      
      wait_ready();

      $display("*** TC %0d reading PRIVATE KEY", tc_number);
      read_block(ADDR_PRIVKEY_START);
      privkey = reg_read_data;

      $display("*** TC %0d reading PUBLIC KEY X", tc_number);
      read_block(ADDR_PUBKEYX_START);
      pubkey.x = reg_read_data;

      $display("*** TC %0d reading PUBLIC KEY Y", tc_number);
      read_block(ADDR_PUBKEYY_START);
      pubkey.y = reg_read_data;
      
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
    reg [383 : 0]   R;
    reg [383 : 0]   S;
    
    begin
      wait_ready();

      $display("*** TC %0d signing test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      start_time = cycle_ctr;

      $display("*** TC %0d writing message value %0h", tc_number, test_vector.hashed_msg);
      write_block(ADDR_MSG_START, test_vector.hashed_msg);
      $display("*** TC %0d writing private key value %0h", tc_number, test_vector.privkey);
      write_block(ADDR_PRIVKEY_START, test_vector.privkey);
      $display("*** TC %0d writing IV value %0h", tc_number, test_vector.IV);
      write_block(ADDR_IV_START, test_vector.IV);

      $display("*** TC %0d starting ECC signing flow", tc_number);
      trig_ECC(SIGN);
      #(CLK_PERIOD);

      wait_ready();

      $display("*** TC %0d reading R value", tc_number);
      read_block(ADDR_SIGNR_START);
      R = reg_read_data;

      $display("*** TC %0d reading S value", tc_number);
      read_block(ADDR_SIGNS_START);
      S = reg_read_data;
      
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
    reg [383 : 0]   verify_r;
    
    begin
      wait_ready();

      $display("*** TC %0d verifying test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      start_time = cycle_ctr;

      $display("*** TC %0d writing message value %0h", tc_number, test_vector.hashed_msg);
      write_block(ADDR_MSG_START, test_vector.hashed_msg);
      $display("*** TC %0d writing PUBLIC KEY X value %0h", tc_number, test_vector.pubkey.x);
      write_block(ADDR_PUBKEYX_START, test_vector.pubkey.x);
      $display("*** TC %0d writing PUBLIC KEY Y value %0h", tc_number, test_vector.pubkey.y);
      write_block(ADDR_PUBKEYY_START, test_vector.pubkey.y);
      $display("*** TC %0d writing R value %0h", tc_number, test_vector.R);
      write_block(ADDR_SIGNR_START, test_vector.R);
      $display("*** TC %0d writing S value %0h", tc_number, test_vector.S);
      write_block(ADDR_SIGNS_START, test_vector.S);

      $display("*** TC %0d starting ECC verify flow", tc_number);
      trig_ECC(VERIFY);
      #(CLK_PERIOD);

      wait_ready();

      $display("*** TC %0d reading VERIFY R value", tc_number);
      read_block(ADDR_VERIFY_R_START);
      verify_r = reg_read_data;
      
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
  // ecc_sca_config_test()
  //
  // Perform different sca configuration tests.
  //----------------------------------------------------------------
  task ecc_sca_config_test();
    
    begin
      wait_ready();

      $display("*** ECC SCA configuration test started.");
      
      // with all countermeasures by default
      $display("\ntest with all countermeasures by default");
      ecc_keygen_test(1, test_vectors[1]);
      ecc_signing_test(8, test_vectors[8]);
      ecc_verifying_test(8, test_vectors[8]);

      // without any protection
      $display("\ntest without any protection");
      write_block(ADDR_SCACONFIG, 3'b000);  
      ecc_keygen_test(1, test_vectors[1]);
      ecc_signing_test(8, test_vectors[8]);
      ecc_verifying_test(8, test_vectors[8]);

      // with only point randomization
      $display("\ntest with only point randomization");
      write_block(ADDR_SCACONFIG, 3'b001);  
      ecc_keygen_test(1, test_vectors[1]);
      ecc_signing_test(8, test_vectors[8]);
      ecc_verifying_test(8, test_vectors[8]);

      // with only masking sign
      $display("\ntest with only masking sign");
      write_block(ADDR_SCACONFIG, 3'b010);  
      ecc_keygen_test(1, test_vectors[1]);
      ecc_signing_test(8, test_vectors[8]);
      ecc_verifying_test(8, test_vectors[8]);

      // with only scalar blinding
      $display("\ntest with only scalar blinding");
      write_block(ADDR_SCACONFIG, 3'b100);  
      ecc_keygen_test(1, test_vectors[1]);
      ecc_signing_test(8, test_vectors[8]);
      ecc_verifying_test(8, test_vectors[8]);

      // with point randomization and masking sign
      $display("\ntest with point randomization and masking sign");
      write_block(ADDR_SCACONFIG, 3'b011);  
      ecc_keygen_test(1, test_vectors[1]);
      ecc_signing_test(8, test_vectors[8]);
      ecc_verifying_test(8, test_vectors[8]);

      // with point randomization and scalar blinding
      $display("\ntest with point randomization and scalar blinding");
      write_block(ADDR_SCACONFIG, 3'b101);  
      ecc_keygen_test(1, test_vectors[1]);
      ecc_signing_test(8, test_vectors[8]);
      ecc_verifying_test(8, test_vectors[8]);

      // with masking sign and scalar blinding
      $display("\ntest with masking sign and scalar blinding");
      write_block(ADDR_SCACONFIG, 3'b110);  
      ecc_keygen_test(1, test_vectors[1]);
      ecc_signing_test(8, test_vectors[8]);
      ecc_verifying_test(8, test_vectors[8]);

      // with all countermeasures
      $display("\ntest with all countermeasures");
      write_block(ADDR_SCACONFIG, 3'b111);  
      ecc_keygen_test(1, test_vectors[1]);
      ecc_signing_test(8, test_vectors[8]);
      ecc_verifying_test(8, test_vectors[8]);

    end
  endtask // ecc_signing_test


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

      write_block(ADDR_SCACONFIG, 4'b1111); // disabled hmac-drbg
      write_block(ADDR_SEED_START, test_vector.privkey);
      write_block(ADDR_IV_START, test_vector.IV);

      trig_ECC(KEYGEN);
      #(CLK_PERIOD);
      
      wait_ready();

      read_block(ADDR_PRIVKEY_START);
      privkey = reg_read_data;

      read_block(ADDR_PUBKEYX_START);
      pubkey.x = reg_read_data;

      read_block(ADDR_PUBKEYY_START);
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
        end
        else if (ecc_test_to_run == "ECC_otf_reset_test") begin
          ecc_onthefly_reset_test(i, test_vectors[i]);
        end
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
      write_block(ADDR_SCACONFIG, 4'b0111); // enabled hmac-drbg
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
      values_per_test_vector = 10;
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
              8: begin
                 test_vector.IV          = val;
                 test_vectors[test_vector_cnt] = test_vector;
              end
              9 : test_vector_cnt++;
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

      write_block(ADDR_MSG_START, test_vector.hashed_msg);
      write_block(ADDR_PRIVKEY_START, test_vector.privkey);
      write_block(ADDR_IV_START, test_vector.IV);

      trig_ECC(SIGN);
      #(500 * CLK_PERIOD);

      reset_dut();
      wait_ready();

      read_block(ADDR_SIGNR_START);
      R = reg_read_data;

      read_block(ADDR_SIGNS_START);
      S = reg_read_data;

      read_block(ADDR_PRIVKEY_START);
      privkey = reg_read_data;

      read_block(ADDR_PUBKEYX_START);
      pubkey_x = reg_read_data;

      read_block(ADDR_PUBKEYY_START);
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

      if ((ecc_test_to_run == "default") || (ecc_test_to_run == "ECC_normal_test") || (ecc_test_to_run == "ECC_otf_reset_test")) begin
        ecc_test(); 
      end
      else if (ecc_test_to_run == "ECC_sca_config_test") begin
        ecc_sca_config_test();
      end

      display_test_results();
      
      $display("");
      $display("*** ecc simulation done. ***");
      $finish;
    end // main

endmodule // ecc_top_tb
