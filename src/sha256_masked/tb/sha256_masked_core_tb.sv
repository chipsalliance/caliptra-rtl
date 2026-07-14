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
// sha256_masked_core_tb.sv
// --------
// SHA256 testbench for the SHA256 masked core.
//
//
//======================================================================

module sha256_masked_core_tb
  ();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;

  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  parameter MODE_SHA_224 = 1'h0;
  parameter MODE_SHA_256 = 1'h1;
  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [31 : 0]  cycle_ctr;
  reg [31 : 0]  error_ctr;
  reg [31 : 0]  tc_ctr;

  reg           clk_tb;
  reg           reset_n_tb;
  reg           zeroize_tb;

  reg           init_tb;
  reg           next_tb;
  reg           restore_tb;
  reg           mode_tb;

  reg [511 : 0] block_tb;
  reg [255 : 0] restore_digest_tb;
  wire [255: 0] digest_tb;

  reg [191 : 0] entropy_tb;

  wire          ready_tb;
  wire          valid_tb;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  sha256_masked_core DUT (
                     .clk(clk_tb),
                     .reset_n(reset_n_tb),
                     .zeroize(zeroize_tb),

                     .init_cmd(init_tb),
                     .next_cmd(next_tb),
                     .restore_cmd(restore_tb),
                     .mode(mode_tb),

                     .entropy(entropy_tb),

                     .block_msg(block_tb),
                     .restore_digest(restore_digest_tb),

                     .ready(ready_tb),
                     .digest(digest_tb),
                     .digest_valid(valid_tb)
                    );

  //----------------------------------------------------------------
  // Randomize function
  //
  //
  //----------------------------------------------------------------
  function logic [191 : 0] random_gen();
    return { $random, $random, $random, $random, $random, $random};
  endfunction

  //----------------------------------------------------------------
  // clk_gen
  //
  // Clock generator process.
  //----------------------------------------------------------------
  always
    begin : clk_gen
      #CLK_HALF_PERIOD clk_tb = !clk_tb;
    end // clk_gen

  //----------------------------------------------------------------
  // sys_monitor
  //
  // Generates a cycle counter and displays information about
  // the dut as needed.
  //----------------------------------------------------------------
  always
    begin : sys_monitor
      #(CLK_PERIOD);
      cycle_ctr = cycle_ctr + 1;
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
      #(4 * CLK_HALF_PERIOD);
      reset_n_tb = 1;
    end
  endtask // reset_dut

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
      #(CLK_PERIOD);

      while (!ready_tb)
        begin
          #(CLK_PERIOD);
        end
    end
  endtask // wait_ready

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
      zeroize_tb    = 0;

      init_tb     = '0;
      next_tb     = '0;
      restore_tb  = '0;
      mode_tb     = '0;
      block_tb    = '0;
      restore_digest_tb = '0;

      entropy_tb     = '0;
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
  // get_mask()
  //
  // Create the mask needed for a given mode. SHA-224 keeps the
  // upper 224 bits (7 dwords), SHA-256 keeps the full 256 bits.
  //----------------------------------------------------------------
  function [255 : 0] get_mask(input mode);
    begin
      case (mode)
        MODE_SHA_224:
          begin
            if (DEBUG)
              begin
                $display("Mode MODE_SHA_224");
              end
            get_mask = {{7{32'hffffffff}}, {1{32'h00000000}}};
          end

        MODE_SHA_256:
          begin
            if (DEBUG)
              begin
                $display("Mode MODE_SHA_256");
              end
            get_mask = {8{32'hffffffff}};
          end
      endcase // case (mode)
    end
  endfunction // get_mask

  //----------------------------------------------------------------
  // single_block_test()
  //
  //
  // Perform test of a single block digest.
  //----------------------------------------------------------------
  task single_block_test(input [7 : 0]   tc_number,
                         input           mode,
                         input [511 : 0] block,
                         input [255 : 0] expected);

    reg [255 : 0] mask;
    reg [255 : 0] masked_data;
    reg [31  : 0] start_time;
    reg [31  : 0] end_time;
    begin
      $display("*** TC%01d - Single block test started.", tc_ctr);

      start_time = cycle_ctr;
      block_tb = block;

      entropy_tb = random_gen();
      $display("   entropy_tb= %048x", entropy_tb);

      #CLK_PERIOD;
      mode_tb = mode;
      next_tb = '0;
      init_tb = 1'b1;

      #CLK_PERIOD;
      init_tb = '0;

      wait_ready();

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);

      mask = get_mask(mode);
      masked_data = digest_tb & mask;

      if (DEBUG)
        begin
          $display("masked_data = 0x%064x", masked_data);
        end

      if (masked_data == expected)
        begin
          $display("TC%01d: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR.", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%064x", tc_ctr, masked_data);
          error_ctr = error_ctr + 1;
        end
      $display("*** TC%01d - Single block test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // single_block_test


  //----------------------------------------------------------------
  // double_block_test()
  //
  //
  // Perform test of a double block digest. Note that we check
  // the digests for both the first and final block.
  //----------------------------------------------------------------
  task double_block_test(input [7 : 0]   tc_number,
                         input           mode,
                         input [511 : 0] block0,
                         input [511 : 0] block1,
                         input [255 : 0] expected0,
                         input [255 : 0] expected1
                        );
    reg [255 : 0] mask;
    reg [255 : 0] masked_data1;
    reg [31 : 0]  start_time;
    reg [31 : 0]  end_time;

    begin
      $display("*** TC%01d - Double block test started.", tc_ctr);

      mask = get_mask(mode);
      start_time = cycle_ctr;

      // First block
      block_tb = block0;
      entropy_tb = random_gen();
      $display("   entropy_tb= %048x", entropy_tb);

      #CLK_PERIOD;
      mode_tb = mode;
      next_tb = '0;
      init_tb = 1'b1;

      #CLK_PERIOD;
      init_tb = '0;

      wait_ready();

      if (digest_tb == expected0)
        begin
          $display("TC%01d first block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in first digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected0);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_tb);
          error_ctr = error_ctr + 1;
        end


      // Final block
      block_tb = block1;

      #CLK_PERIOD;
      mode_tb = mode;
      next_tb = 1'b1;
      init_tb = '0;

      #CLK_PERIOD;
      next_tb = '0;

      wait_ready();

      end_time = cycle_ctr - start_time;
      $display("*** Double block test processing time = %01d cycles", end_time);

      masked_data1 = digest_tb & mask;

      if (masked_data1 == expected1)
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected1);
          $display("TC%01d: Got:      0x%064x", tc_ctr, masked_data1);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - Double block test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // double_block_test


  //----------------------------------------------------------------
  // restore_test()
  //
  //
  // Perform test of a double block digest with restore feature.
  //----------------------------------------------------------------
  task restore_test(input [7 : 0]   tc_number,
                    input           mode,
                    input [511 : 0] block0,
                    input [511 : 0] block1,
                    input [255 : 0] expected0,
                    input [255 : 0] expected1
                   );
    reg [255 : 0] mask;
    reg [255 : 0] saved_digest;
    reg [255 : 0] masked_data;
    reg [31  : 0] start_time;
    reg [31  : 0] end_time;

    begin
      $display("*** TC%01d - Restore block test started.", tc_ctr);

      mask = get_mask(mode);
      start_time = cycle_ctr;

      // First block via INIT
      block_tb   = block0;
      entropy_tb = random_gen();
      $display("   entropy_tb= %048x", entropy_tb);

      #CLK_PERIOD;
      mode_tb    = mode;
      next_tb    = '0;
      restore_tb = '0;
      init_tb    = 1'b1;

      #CLK_PERIOD;
      init_tb    = '0;

      wait_ready();

      if (digest_tb == expected0)
        begin
          $display("TC%01d first block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in first digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected0);
          $display("TC%01d: Got:      0x%064x", tc_ctr, digest_tb);
          error_ctr = error_ctr + 1;
        end

      saved_digest = digest_tb;

      zeroize_tb = 1'b1;
      #CLK_PERIOD;
      zeroize_tb = 1'b0;

      // Final block via RESTORE + NEXT
      block_tb          = block1;
      restore_digest_tb = saved_digest;
      entropy_tb        = random_gen();

      #CLK_PERIOD;
      mode_tb    = mode;
      init_tb    = '0;
      next_tb    = 1'b1;
      restore_tb = 1'b1;

      #CLK_PERIOD;
      next_tb    = '0;
      restore_tb = '0;

      wait_ready();

      end_time = cycle_ctr - start_time;
      $display("*** Restore block test processing time = %01d cycles", end_time);

      masked_data = digest_tb & mask;

      if (masked_data == (expected1 & mask))
        begin
          $display("TC%01d final block: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR in final digest", tc_ctr);
          $display("TC%01d: Expected: 0x%064x", tc_ctr, expected1);
          $display("TC%01d: Got:      0x%064x", tc_ctr, masked_data);
          error_ctr = error_ctr + 1;
        end

      zeroize_tb = 1'b1;
      #CLK_PERIOD;
      zeroize_tb = 1'b0;

      $display("*** TC%01d - Restore block test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // restore_test


  //----------------------------------------------------------------
  // sha256_test
  // The main test functionality.
  //
  // Test cases taken from FIPS 180-4 Appendix B / RFC 3874.
  //----------------------------------------------------------------
  initial
    begin : sha256_test
      reg [511 : 0]  single_block;
      reg [255 : 0]  tc1_expected;
      reg [255 : 0]  tc2_expected;

      reg [511 : 0]  double_block_one;
      reg [511 : 0]  double_block_two;
      reg [255 : 0]  tc3_expected;
      reg [255 : 0]  tc4_expected;
      reg [255 : 0]  tc5_expected;
      reg [255 : 0]  tc6_expected;

      $display("   -- Testbench for sha256 started --");

      init_sim();
      reset_dut();


      // Single block test message: ASCII "abc" with FIPS-180 padding.
      single_block = 512'h6162638000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000_0018;

      // SHA-256 single block digest and test.
      tc1_expected = 256'hBA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD;
      single_block_test(8'h01, MODE_SHA_256, single_block, tc1_expected);

      // SHA-224 single block digest and test.
      tc2_expected = {224'h23097D223405D8228642A477BDA255B32AADBCE4BDA0B3F7E36C9DA7, {1{32'h00000000}}};
      single_block_test(8'h02, MODE_SHA_224, single_block, tc2_expected);


      // Two block test message: 448-bit alphabet, FIPS-180 padded.
      double_block_one = 512'h6162636462636465636465666465666765666768666768696768696A68696A6B696A6B6C6A6B6C6D6B6C6D6E6C6D6E6F6D6E6F706E6F70718000000000000000;
      double_block_two = 512'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001C0;

      // SHA-256 two block digests and test.
      tc3_expected = 256'h85E655D6417A17953363376A624CDE5C76E09589CAC5F811CC4B32C1F20E533A;
      tc4_expected = 256'h248D6A61D20638B8E5C026930C3E6039A33CE45964FF2167F6ECEDD419DB06C1;
      double_block_test(8'h03, MODE_SHA_256, double_block_one, double_block_two, tc3_expected, tc4_expected);

      // SHA-224 two block digests and test.
      tc5_expected = 256'h8250E65DBCF62F8466659C3333E5E91A10C8B7B0953927691F1419C2FD16F295;
      tc6_expected = {224'h75388B16512776CC5DBA5DA1FD890150B0C6455CB4F58B1952522525, {1{32'h00000000}}};
      double_block_test(8'h04, MODE_SHA_224, double_block_one, double_block_two, tc5_expected, tc6_expected);

      // SHA-256 restore test.
      restore_test(8'h05, MODE_SHA_256, double_block_one, double_block_two, tc3_expected, tc4_expected);
      // SHA-224 restore test.
      restore_test(8'h06, MODE_SHA_224, double_block_one, double_block_two, tc5_expected, tc6_expected);

      display_test_result();

      $display("   -- Testbench for sha256 done. --");
      $finish;
  end //sha256_test

endmodule
