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
// hmac256_ctrl_tb.sv
// --------
// HMAC256 testbench for the hmac256 AHb-Lite interface controller.
//
//======================================================================

module hmac256_ctrl_tb
  import hmac256_param_pkg::*;
  ();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;

  parameter CLK_HALF_PERIOD = 2;
  parameter CLK_PERIOD = 2 * CLK_HALF_PERIOD;

  // HMAC256_CTRL bit positions per hmac256_reg.rdl
  parameter CTRL_INIT_VALUE    = 32'h00000001;  // bit 0
  parameter CTRL_NEXT_VALUE    = 32'h00000002;  // bit 1
  parameter CTRL_ZEROIZE       = 32'h00000004;  // bit 2
  parameter CTRL_MODE_VALUE    = 32'h00000008;  // bit 3
  parameter CTRL_LAST_VALUE    = 32'h00000010;  // bit 4
  parameter CTRL_RESTORE_VALUE = 32'h00000020;  // bit 5

  parameter HMAC256_MODE_VALUE = CTRL_MODE_VALUE;  // mode=1 → HMAC-SHA-256
  parameter HMAC224_MODE_VALUE = 32'h00000000;     // mode=0 → HMAC-SHA-224

  // Register offsets from generated hmac256_reg.sv
  parameter ADDR_NAME0     = 32'h00000000;
  parameter ADDR_VERSION0  = 32'h00000008;
  parameter ADDR_CTRL      = 32'h00000010;
  parameter ADDR_STATUS    = 32'h00000018;
  parameter ADDR_KEY_BASE  = 32'h00000040;
  parameter ADDR_BLOCK_BASE = 32'h00000080;
  parameter ADDR_TAG_BASE  = 32'h000000C0;
  parameter ADDR_LFSR_SEED_BASE = 32'h000000E0;
  parameter ADDR_ERROR_INTERNAL_INTR_R = 32'h00000814;

  parameter STATUS_READY_MASK = 32'h00000001;
  parameter ERROR0_STS_MASK   = 32'h00000001;  // bit 0 in error_internal_intr_r: invalid_cmd_error

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  parameter AHB_ADDR_WIDTH = 12;
  parameter AHB_DATA_WIDTH = 64;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0] cycle_ctr;
  reg [63 : 0] error_ctr;
  reg [63 : 0] tc_ctr;

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

  reg [31 : 0]          read_data;
  reg [TAG_SIZE-1 : 0]  digest_data;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  hmac256_ctrl #(
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

             .busy_o(),
             .error_intr(),
             .notif_intr(),
             .debugUnlock_or_scan_mode_switch('0)
            );


  //----------------------------------------------------------------
  // clk_gen
  //----------------------------------------------------------------
  always
    begin : clk_gen
      #CLK_HALF_PERIOD clk_tb = !clk_tb;
    end // clk_gen


  //----------------------------------------------------------------
  // sys_monitor
  //----------------------------------------------------------------
  always
    begin : sys_monitor
      #(CLK_PERIOD);
      cycle_ctr = cycle_ctr + 1;
    end

  //----------------------------------------------------------------
  // Randomize function
  //----------------------------------------------------------------
  function logic [LFSR_SEED_SIZE-1 : 0] random_gen();
    return { $random, $random, $random, $random, $random, $random };
  endfunction

  //----------------------------------------------------------------
  // reset_dut()
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
    end
  endtask // reset_dut


  //----------------------------------------------------------------
  // init_sim()
  //----------------------------------------------------------------
  task init_sim;
    begin
      cycle_ctr = '0;
      error_ctr = '0;
      tc_ctr    = '0;

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
    end
  endtask // init_dut


  //----------------------------------------------------------------
  // display_test_result()
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
  // read_single_word()
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
      read_data = address[2] ? hrdata_o_tb[63:32] : hrdata_o_tb[31:0];
    end
  endtask // read_single_word


  //----------------------------------------------------------------
  // wait_ready()
  //----------------------------------------------------------------
  task wait_ready;
    begin
      read_data = 0;
      #(CLK_PERIOD);

      while (read_data == 0)
        begin
          read_single_word(ADDR_STATUS);
        end
    end
  endtask // wait_ready


  //----------------------------------------------------------------
  // write_block()
  //----------------------------------------------------------------
  task write_block(input [BLOCK_SIZE-1 : 0] block);
    integer i;
    begin
      for (i = 0; i < BLOCK_SIZE/32; i++) begin
        // dword 0 (i=0) gets the MSB-end 32 bits of block; dword 15 gets the LSB-end.
        write_single_word(ADDR_BLOCK_BASE + i*4,
                          block[(BLOCK_SIZE - 1 - i*32) -: 32]);
      end
    end
  endtask // write_block


  //----------------------------------------------------------------
  // hmac_write_key()
  //----------------------------------------------------------------
  task hmac_write_key(input [KEY_SIZE-1 : 0] key);
    integer i;
    begin
      for (i = 0; i < KEY_SIZE/32; i++) begin
        write_single_word(ADDR_KEY_BASE + i*4,
                          key[(KEY_SIZE - 1 - i*32) -: 32]);
      end
    end
  endtask // hmac_write_key


  //----------------------------------------------------------------
  // write_seed()
  //----------------------------------------------------------------
  task write_seed(input [LFSR_SEED_SIZE-1 : 0] seed);
    integer i;
    begin
      for (i = 0; i < LFSR_SEED_SIZE/32; i++) begin
        write_single_word(ADDR_LFSR_SEED_BASE + i*4,
                          seed[(LFSR_SEED_SIZE - 1 - i*32) -: 32]);
      end
    end
  endtask // write_seed


  //----------------------------------------------------------------
  // hmac_read_digest()
  //----------------------------------------------------------------
  task hmac_read_digest;
    integer i;
    begin
      for (i = 0; i < TAG_SIZE/32; i++) begin
        read_single_word(ADDR_TAG_BASE + i*4);
        digest_data[(TAG_SIZE - 1 - i*32) -: 32] = read_data;
      end
    end
  endtask // hmac_read_digest


  //----------------------------------------------------------------
  // write_tag()
  //----------------------------------------------------------------
  task write_tag(input [TAG_SIZE-1 : 0] tag);
    integer i;
    begin
      for (i = 0; i < TAG_SIZE/32; i++) begin
        write_single_word(ADDR_TAG_BASE + i*4,
                          tag[(TAG_SIZE - 1 - i*32) -: 32]);
      end
    end
  endtask // write_tag


  //----------------------------------------------------------------
  // check_name_version()
  //----------------------------------------------------------------
  task check_name_version;
    begin
      read_single_word(ADDR_NAME0);
      $display("DUT NAME[0]    = 0x%08x", read_data);
      read_single_word(ADDR_VERSION0);
      $display("DUT VERSION[0] = 0x%08x", read_data);
    end
  endtask // check_name_version


  //----------------------------------------------------------------
  // hmac_single_block_test()
  //----------------------------------------------------------------
  task hmac_single_block_test(input [31:0] mode,
                         input [KEY_SIZE-1 : 0] key,
                         input [BLOCK_SIZE-1: 0] block,
                         input [LFSR_SEED_SIZE-1 : 0] seed,
                         input [TAG_SIZE-1 : 0] expected
                        );
    reg [31:0] start_time;
    reg [31:0] end_time;
    begin
      start_time = cycle_ctr;
      $display("*** TC%01d - Single block test started.", tc_ctr);

      hmac_write_key(key);
      write_block(block);
      write_seed(seed);

      write_single_word(ADDR_CTRL, mode | CTRL_INIT_VALUE | CTRL_LAST_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;

      #(CLK_PERIOD);
      wait_ready();
      hmac_read_digest();

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);

      write_single_word(ADDR_CTRL, CTRL_ZEROIZE);

      if (digest_data == expected)
        begin
          $display("TC%01d: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR.", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - Single block test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // hmac_single_block_test


  //----------------------------------------------------------------
  // hmac_double_block_test()
  //----------------------------------------------------------------
  task hmac_double_block_test(input [31:0] mode,
                         input [KEY_SIZE-1 : 0] key,
                         input [BLOCK_SIZE-1: 0] block0,
                         input [BLOCK_SIZE-1: 0] block1,
                         input [LFSR_SEED_SIZE-1 : 0] seed,
                         input [TAG_SIZE-1 : 0] expected
                        );
    reg [31:0] start_time;
    reg [31:0] end_time;
    begin
      start_time = cycle_ctr;
      $display("*** TC%01d - Double block test started.", tc_ctr);

      hmac_write_key(key);
      write_block(block0);
      write_seed(seed);

      write_single_word(ADDR_CTRL, mode | CTRL_INIT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;
      #(CLK_PERIOD);
      wait_ready();

      // Final block — finalize via NEXT|LAST.
      write_block(block1);

      write_single_word(ADDR_CTRL, mode | CTRL_NEXT_VALUE | CTRL_LAST_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;
      #(CLK_PERIOD);
      wait_ready();
      hmac_read_digest();

      write_single_word(ADDR_CTRL, CTRL_ZEROIZE);

      end_time = cycle_ctr - start_time;
      $display("*** Double block test processing time = %01d cycles", end_time);

      if (digest_data == expected)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - Double block test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // hmac_double_block_test


  //----------------------------------------------------------------
  // hmac_save_restore_test()
  //----------------------------------------------------------------
  task hmac_save_restore_test(
        input [31:0]                 mode,
        input [KEY_SIZE-1   : 0]     keyA,
        input [BLOCK_SIZE-1 : 0]     blockA0,
        input [BLOCK_SIZE-1 : 0]     blockA1,
        input [LFSR_SEED_SIZE-1 : 0] seedA,
        input [TAG_SIZE-1   : 0]     expectedA,
        input [KEY_SIZE-1   : 0]     keyB,
        input [BLOCK_SIZE-1 : 0]     blockB,
        input [LFSR_SEED_SIZE-1 : 0] seedB);
    reg [TAG_SIZE-1 : 0] saved_tag;
    begin
      $display("*** TC%01d - Restore with unrelated op test started.", tc_ctr);

      // Operation A, session 1: INIT blockA0 (no LAST)
      hmac_write_key(keyA);
      write_block(blockA0);
      write_seed(seedA);
      write_single_word(ADDR_CTRL, mode | CTRL_INIT_VALUE);
      #CLK_PERIOD;
      hsel_i_tb = 0;
      #(CLK_PERIOD);
      wait_ready();
      hmac_read_digest();
      saved_tag = digest_data;

      write_single_word(ADDR_CTRL, CTRL_ZEROIZE);
      #(4*CLK_PERIOD);

      // Unrelated operation B: single block with LAST
      hmac_write_key(keyB);
      write_block(blockB);
      write_seed(seedB);
      write_single_word(ADDR_CTRL, mode | CTRL_INIT_VALUE | CTRL_LAST_VALUE);
      #CLK_PERIOD;
      hsel_i_tb = 0;
      #(CLK_PERIOD);
      wait_ready();

      write_single_word(ADDR_CTRL, CTRL_ZEROIZE);
      #(4*CLK_PERIOD);

      // Operation A, session 2: restore saved state + finalize
      hmac_write_key(keyA);
      write_block(blockA1);
      write_seed(seedA);
      write_tag(saved_tag);
      write_single_word(ADDR_CTRL,
                        mode | CTRL_RESTORE_VALUE | CTRL_NEXT_VALUE | CTRL_LAST_VALUE);
      #CLK_PERIOD;
      hsel_i_tb = 0;
      #(CLK_PERIOD);
      wait_ready();
      hmac_read_digest();

      write_single_word(ADDR_CTRL, CTRL_ZEROIZE);

      if (digest_data == expectedA)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest after unrelated-op restore", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expectedA);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - Restore with unrelated op test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // hmac_save_restore_test


  //----------------------------------------------------------------
  // last_alone_error_test()
  //----------------------------------------------------------------
  task last_alone_error_test(input [31:0]  mode,
                             input [KEY_SIZE-1:0] key,
                             input [BLOCK_SIZE-1:0] block,
                             input [LFSR_SEED_SIZE-1:0]  seed,
                             input [TAG_SIZE-1:0]  expected);
    begin
      $display("*** TC%01d - LAST-alone error0_sts test started.", tc_ctr);

      hmac_write_key(key);
      write_block(block);
      write_seed(seed);

      // Bogus write: LAST alone, no INIT or NEXT companion.
      write_single_word(ADDR_CTRL, mode | CTRL_LAST_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;
      #(CLK_PERIOD * 4);

      // Engine must still be IDLE/READY.
      read_single_word(ADDR_STATUS);
      if ((read_data & STATUS_READY_MASK) !== STATUS_READY_MASK)
        begin
          $display("TC%01d: ERROR - STATUS.READY dropped after LAST-alone write.", tc_ctr);
          error_ctr = error_ctr + 1;
        end

      // error0_sts must be set.
      read_single_word(ADDR_ERROR_INTERNAL_INTR_R);
      if ((read_data & ERROR0_STS_MASK) == 0) begin
        $display("TC%01d: ERROR - error0_sts not set after LAST-alone write.", tc_ctr);
        error_ctr = error_ctr + 1;
      end
      // W1C error0_sts so subsequent invalid-CTRL tests measure a fresh edge.
      write_single_word(ADDR_ERROR_INTERNAL_INTR_R, ERROR0_STS_MASK);

      // Now drive a valid single-block op and confirm the digest.
      write_single_word(ADDR_CTRL, mode | CTRL_INIT_VALUE | CTRL_LAST_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;
      #(CLK_PERIOD);
      wait_ready();
      hmac_read_digest();

      write_single_word(ADDR_CTRL, CTRL_ZEROIZE);

      if (digest_data == expected)
        begin
          $display("TC%01d: OK (LAST alone raised error0_sts; follow-up op produced expected digest).", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR - state corruption after LAST-alone write.", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - LAST-alone error0_sts test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // last_alone_error_test


  //----------------------------------------------------------------
  // restore_alone_error_test()
  //----------------------------------------------------------------
  task restore_alone_error_test(input [31:0]  mode,
                                input [KEY_SIZE-1:0] key,
                                input [BLOCK_SIZE-1:0] block,
                                input [LFSR_SEED_SIZE-1:0]  seed,
                                input [TAG_SIZE-1:0]  expected);
    begin
      $display("*** TC%01d - RESTORE-alone reject test started.", tc_ctr);

      hmac_write_key(key);
      write_block(block);
      write_seed(seed);

      // Bogus write: RESTORE alone, no NEXT companion.
      write_single_word(ADDR_CTRL, mode | CTRL_RESTORE_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;
      #(CLK_PERIOD * 4);

      // Engine must still be IDLE/READY.
      read_single_word(ADDR_STATUS);
      if ((read_data & STATUS_READY_MASK) !== STATUS_READY_MASK)
        begin
          $display("TC%01d: ERROR - STATUS.READY dropped after RESTORE-alone write.", tc_ctr);
          error_ctr = error_ctr + 1;
        end

      read_single_word(ADDR_ERROR_INTERNAL_INTR_R);
      if ((read_data & ERROR0_STS_MASK) == 0) begin
        $display("TC%01d: ERROR - error0_sts not set after RESTORE-alone write.", tc_ctr);
        error_ctr = error_ctr + 1;
      end
      // W1C error0_sts so subsequent invalid-CTRL tests measure a fresh edge.
      write_single_word(ADDR_ERROR_INTERNAL_INTR_R, ERROR0_STS_MASK);

      write_single_word(ADDR_CTRL, mode | CTRL_INIT_VALUE | CTRL_LAST_VALUE);
      #CLK_PERIOD;
      hsel_i_tb       = 0;
      #(CLK_PERIOD);
      wait_ready();
      hmac_read_digest();

      write_single_word(ADDR_CTRL, CTRL_ZEROIZE);

      if (digest_data == expected)
        begin
          $display("TC%01d: OK (RESTORE alone rejected; follow-up op produced expected digest).", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR - state corruption after RESTORE-alone write.", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_data);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - RESTORE-alone reject test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // restore_alone_error_test


  //----------------------------------------------------------------
  // hmac256_tests()
  //
  // Test cases from RFC 4231.
  //----------------------------------------------------------------
  task hmac256_tests;
    begin : hmac256_tests_block
      reg [KEY_SIZE-1   : 0] key1, key2, key4;
      reg [BLOCK_SIZE-1 : 0] data1, data2;
      reg [BLOCK_SIZE-1 : 0] data4_0, data4_1;
      reg [LFSR_SEED_SIZE-1 : 0] seed1, seed2, seed4;
      reg [TAG_SIZE-1   : 0] expected1, expected2, expected4;

      $display("\n\n*** Testcases for PRF-HMAC-SHA-256 functionality started.");

      // RFC 4231 #1: K = 20*0x0b, msg = "Hi There"
      key1      = 512'h0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
      data1     = 512'h48692054686572658000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000240;
      expected1 = 256'hb0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7;
      seed1     = random_gen();

      // RFC 4231 #2: K = "Jefe", msg = "what do you want for nothing?"
      key2      = 512'h4a656665000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
      data2     = 512'h7768617420646f20796f752077616e7420666f72206e6f7468696e673f80000000000000000000000000000000000000000000000000000000000000000002e8;
      expected2 = 256'h69b8522176ad44097a64ef3a923be45843ebde060f0bfb674bfbaf27092055e2;
      seed2     = random_gen();

      // Custom 2-block: K = 20*0x0b, msg = 56-byte alphabet
      key4      = 512'h0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
      data4_0   = 512'h6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f70718000000000000000;
      data4_1   = 512'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c0;
      expected4 = 256'hcf86b015af9fadf1ec439642be2458fc7da3c8e4effce404a32ce41fd0e213d3;
      seed4     = random_gen();

      hmac_single_block_test(HMAC256_MODE_VALUE, key1, data1, seed1, expected1);
      hmac_single_block_test(HMAC256_MODE_VALUE, key2, data2, seed2, expected2);
      hmac_double_block_test(HMAC256_MODE_VALUE, key4, data4_0, data4_1, seed4, expected4);

      // Save state, run an unrelated complete op (clobbers TAG), then restore + finalize.
      hmac_save_restore_test(HMAC256_MODE_VALUE,
                             key4, data4_0, data4_1, seed4, expected4,
                             key1, data1, seed1);

      // Modifier-only LAST must be ignored when written alone.
      last_alone_error_test(HMAC256_MODE_VALUE, key1, data1, seed1, expected1);

      // RESTORE without NEXT must not start the engine.
      restore_alone_error_test(HMAC256_MODE_VALUE, key1, data1, seed1, expected1);

      $display("*** Testcases for PRF-HMAC-SHA-256 functionality completed.");
    end
  endtask // hmac256_tests


  //----------------------------------------------------------------
  // hmac224_tests()
  //----------------------------------------------------------------
  task hmac224_tests;
    begin : hmac224_tests_block
      reg [KEY_SIZE-1   : 0] key1, key2, key4;
      reg [BLOCK_SIZE-1 : 0] data1, data2;
      reg [BLOCK_SIZE-1 : 0] data4_0, data4_1;
      reg [LFSR_SEED_SIZE-1 : 0] seed1, seed2, seed4;
      reg [HMAC224_TAG_SIZE-1 : 0] expected1_224, expected2_224, expected4_224;

      $display("\n\n*** Testcases for PRF-HMAC-SHA-224 functionality started.");

      key1          = 512'h0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
      data1         = 512'h48692054686572658000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000240;
      expected1_224 = 224'h896fb1128abbdf196832107cd49df33f47b4b1169912ba4f53684b22;
      seed1         = random_gen();

      key2          = 512'h4a656665000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
      data2         = 512'h7768617420646f20796f752077616e7420666f72206e6f7468696e673f80000000000000000000000000000000000000000000000000000000000000000002e8;
      expected2_224 = 224'h1f03a69580f5b55fdcc43fe58a6d135b5fe1449ee09908ed59df9eea;
      seed2         = random_gen();

      key4          = 512'h0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
      data4_0       = 512'h6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f70718000000000000000;
      data4_1       = 512'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c0;
      expected4_224 = 224'h2f1b0d0c449f8b673657684becd7e519523286402f3aa9b8379d63ef;
      seed4         = random_gen();

      hmac_single_block_test(HMAC224_MODE_VALUE, key1, data1, seed1,
                             {expected1_224, {HMAC224_TAG_PAD{1'b0}}});
      hmac_single_block_test(HMAC224_MODE_VALUE, key2, data2, seed2,
                             {expected2_224, {HMAC224_TAG_PAD{1'b0}}});
      hmac_double_block_test(HMAC224_MODE_VALUE, key4, data4_0, data4_1, seed4,
                             {expected4_224, {HMAC224_TAG_PAD{1'b0}}});

      hmac_save_restore_test(HMAC224_MODE_VALUE,
                             key4, data4_0, data4_1, seed4,
                             {expected4_224, {HMAC224_TAG_PAD{1'b0}}},
                             key1, data1, seed1);

      last_alone_error_test(HMAC224_MODE_VALUE, key1, data1, seed1,
                            {expected1_224, {HMAC224_TAG_PAD{1'b0}}});

      restore_alone_error_test(HMAC224_MODE_VALUE, key1, data1, seed1,
                               {expected1_224, {HMAC224_TAG_PAD{1'b0}}});

      $display("*** Testcases for PRF-HMAC-SHA-224 functionality completed.");
    end
  endtask // hmac224_tests


  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -- Testbench for HMAC256 started --");

      init_sim();
      reset_dut();

      check_name_version();
      hmac256_tests();
      hmac224_tests();

      display_test_result();

      $display("   -- Testbench for HMAC256 done. --");
      $finish;
    end // main
endmodule // hmac256_ctrl_tb

//======================================================================
// EOF hmac256_ctrl_tb.sv
//======================================================================
