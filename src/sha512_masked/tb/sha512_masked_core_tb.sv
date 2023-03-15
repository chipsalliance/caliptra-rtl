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
// sha512_masked_core_tb.sv
// --------
// SHA512 testbench for the SHA512 masked core.
//
//
//======================================================================

module sha512_masked_core_tb 
  ();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG = 0;

  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  parameter MODE_SHA_512_224     = 2'h0;
  parameter MODE_SHA_512_256     = 2'h1;
  parameter MODE_SHA_384         = 2'h2;
  parameter MODE_SHA_512         = 2'h3;
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
  reg [1:0]     mode_tb;

  reg [1023:0]  block_tb;
  wire [511:0]  digest_tb;
  
  reg [73:0]    lfsr_seed_tb;

  wire          ready_tb;
  wire          valid_tb;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  sha512_masked_core DUT (
                     .clk(clk_tb),
                     .reset_n(reset_n_tb),
                     .zeroize(zeroize_tb),

                     .init_cmd(init_tb),
                     .next_cmd(next_tb),
                     .mode(mode_tb),

                     .lfsr_seed(lfsr_seed_tb),

                     .block_msg(block_tb),

                     .ready(ready_tb),
                     .digest(digest_tb),
                     .digest_valid(valid_tb)
                    );

  //----------------------------------------------------------------
  // Randomize function
  //
  // 
  //----------------------------------------------------------------
  function logic [73 : 0] random_gen();
    return { $random & 10'h3FF , $random, $random};
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
      mode_tb     = '0;
      block_tb    = '0;

      lfsr_seed_tb     = '0;
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
  // Create the mask needed for a given mode.
  //----------------------------------------------------------------
  function [511 : 0] get_mask(input [1 : 0] mode);
    begin
      case (mode)
        MODE_SHA_512_224:
          begin
            if (DEBUG)
              begin
                $display("Mode MODE_SHA_512_224");
              end
            get_mask = {{7{32'hffffffff}}, {9{32'h00000000}}};
          end

        MODE_SHA_512_256:
          begin
            if (DEBUG)
              begin
                $display("Mode MODE_SHA_512_256");
              end
            get_mask = {{8{32'hffffffff}}, {8{32'h00000000}}};
          end

        MODE_SHA_384:
          begin
            if (DEBUG)
              begin
                $display("Mode MODE_SHA_512_384");
              end
            get_mask = {{12{32'hffffffff}}, {4{32'h00000000}}};
          end

        MODE_SHA_512:
          begin
            if (DEBUG)
              begin
                $display("Mode MODE_SHA_512");
              end
            get_mask = {16{32'hffffffff}};
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
  task single_block_test(input [7 : 0]    tc_number,
                         input [1 : 0]    mode,
                         input [1023 : 0] block,
                         input [511 : 0]  expected);

    reg [511 : 0] mask;
    reg [511 : 0] masked_data;
    reg [31  : 0] start_time;
    reg [31 : 0] end_time;
    begin
      $display("*** TC%01d - Single block test started.", tc_ctr);

      start_time = cycle_ctr;
      block_tb = block;

      lfsr_seed_tb = random_gen();
      $display("   lfsr_seed_tb= %019x", lfsr_seed_tb);

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
          $display("masked_data = 0x%0128x", masked_data);
        end

      if (masked_data == expected)
        begin
          $display("TC%01d: OK.", tc_ctr);
        end
      else
        begin
          $display("TC%01d: ERROR.", tc_ctr);
          $display("TC%01d: Expected: 0x%0128x", tc_ctr, expected);
          $display("TC%01d: Got:      0x%0128x", tc_ctr, masked_data);
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
  task double_block_test(input [7 : 0]    tc_number,
                         input [1 : 0]    mode,
                         input [1023 : 0] block0,
                         input [1023 : 0] block1,
                         input [511 : 0]  expected0,
                         input [511 : 0]  expected1
                        );
    reg [511 : 0] mask;
    reg [511 : 0] masked_data0;
    reg [511 : 0] masked_data1;
    reg [31 : 0] start_time;
    reg [31 : 0] end_time;

    begin
      $display("*** TC%01d - Double block test started.", tc_ctr);

      mask = get_mask(mode);
      start_time = cycle_ctr;

      // First block
      block_tb = block0;
      lfsr_seed_tb = random_gen();
      $display("   lfsr_seed_tb= %019x", lfsr_seed_tb);

      #CLK_PERIOD;
      mode_tb = mode;
      next_tb = '0;
      init_tb = 1'b1;

      #CLK_PERIOD;
      init_tb = '0;

      wait_ready();

      //masked_data0 = expected0 & mask;
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
          $display("TC%01d: Expected: 0x%0128x", tc_ctr, expected1);
          $display("TC%01d: Got:      0x%0128x", tc_ctr, masked_data1);
          error_ctr = error_ctr + 1;
        end

      $display("*** TC%01d - Double block test done.", tc_ctr);
      tc_ctr = tc_ctr + 1;
    end
  endtask // double_block_test


  //----------------------------------------------------------------
  // sha512_test
  // The main test functionality.
  //
  // Test cases taken from:
  // http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA_All.pdf
  //----------------------------------------------------------------
  initial
    begin : sha512_test
      reg [1024 : 0] single_block;
      reg [511 : 0]  tc1_expected;
      reg [511 : 0]  tc2_expected;
      reg [511 : 0]  tc3_expected;
      reg [511 : 0]  tc4_expected;

      reg [1024 : 0] double_block_one;
      reg [1024 : 0] double_block_two;
      reg [511 : 0]  tc5_expected;
      reg [511 : 0]  tc6_expected;
      reg [511 : 0]  tc7_expected;
      reg [511 : 0]  tc8_expected;
      reg [511 : 0]  tc9_expected;
      reg [511 : 0]  tc10_expected;
      reg [511 : 0]  tc11_expected;
      reg [511 : 0]  tc12_expected;

      $display("   -- Testbench for sha512 started --");

      init_sim();
      reset_dut();


      // Single block test mesage.
      single_block = 1024'h6162638000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018;

      // SHA-512 single block digest and test.
      tc1_expected = 512'hDDAF35A193617ABACC417349AE20413112E6FA4E89A97EA20A9EEEE64B55D39A2192992A274FC1A836BA3C23A3FEEBBD454D4423643CE80E2A9AC94FA54CA49F;
      single_block_test(8'h01, MODE_SHA_512, single_block, tc1_expected);

      // SHA-512_224 single block digest and test.
      tc2_expected = {224'h4634270F707B6A54DAAE7530460842E20E37ED265CEEE9A43E8924AA, {9{32'h00000000}}};
      single_block_test(8'h02, MODE_SHA_512_224, single_block, tc2_expected);

      // SHA-512_256 single block digest and test.
      tc3_expected = {256'h53048E2681941EF99B2E29B76B4C7DABE4C2D0C634FC6D46E0E2F13107E7AF23, {8{32'h00000000}}};
      single_block_test(8'h03, MODE_SHA_512_256, single_block, tc3_expected);

      // SHA-384 single block digest and test.
      tc4_expected = {384'hCB00753F45A35E8BB5A03D699AC65007272C32AB0EDED1631A8B605A43FF5BED8086072BA1E7CC2358BAECA134C825A7, {4{32'h00000000}}};
      single_block_test(8'h04, MODE_SHA_384, single_block, tc4_expected);


      // Two block test message.
      double_block_one = 1024'h61626364656667686263646566676869636465666768696A6465666768696A6B65666768696A6B6C666768696A6B6C6D6768696A6B6C6D6E68696A6B6C6D6E6F696A6B6C6D6E6F706A6B6C6D6E6F70716B6C6D6E6F7071726C6D6E6F707172736D6E6F70717273746E6F70717273747580000000000000000000000000000000;
      double_block_two = 1024'h0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000380;

      // SHA-512 two block digests and test.
      tc5_expected = 512'h4319017A2B706E69CD4B05938BAE5E890186BF199F30AA956EF8B71D2F810585D787D6764B20BDA2A26014470973692000EC057F37D14B8E06ADD5B50E671C72;
      tc6_expected = 512'h8E959B75DAE313DA8CF4F72814FC143F8F7779C6EB9F7FA17299AEADB6889018501D289E4900F7E4331B99DEC4B5433AC7D329EEB6DD26545E96E55B874BE909;
      double_block_test(8'h05, MODE_SHA_512, double_block_one, double_block_two, tc5_expected, tc6_expected);

      // SHA-512_224 two block digests and test.
      tc7_expected = 512'h9606CB2DB7823CE75FE35E2674A8F9EF1417ED9E89C412BB54EA29664586108625852563EED495096DEBAAE2F4737FD75319224B135486F8E6C0F55E700C35B3;
      tc8_expected = {224'h23FEC5BB94D60B23308192640B0C453335D664734FE40E7268674AF9, {9{32'h00000000}}};
      double_block_test(8'h06, MODE_SHA_512_224, double_block_one, double_block_two, tc7_expected, tc8_expected);

      // SHA-512_256 two block digests and test.
      tc9_expected = 512'h8DD99EB081311F8BCBBBC42CC7AFB288E8E9408730419D1E953FF7A2B194048DAE24175483C44C7C809B348E8E88E3ECBF2EA614CEED9C5B51807937F11867E1;
      tc10_expected = {256'h3928E184FB8690F840DA3988121D31BE65CB9D3EF83EE6146FEAC861E19B563A, {8{32'h00000000}}};
      double_block_test(8'h07, MODE_SHA_512_256, double_block_one, double_block_two, tc9_expected, tc10_expected);

      // SHA-384 two block digests and test.
      tc11_expected = 512'h2A7F1D895FD58E0BEAAE96D1A673C741015A2173796C1A88F6352CA156ACAFF7C662113E9EBB4D6417B61A85E2CCF0A937EB9A6660FEB5198F2EBE9A81E6A2C5;
      tc12_expected = {384'h09330C33F71147E83D192FC782CD1B4753111B173B3B05D22FA08086E3B0F712FCC7C71A557E2DB966C3E9FA91746039, {4{32'h00000000}}};
      double_block_test(8'h08, MODE_SHA_384, double_block_one, double_block_two, tc11_expected, tc12_expected);

      display_test_result();
      
      $display("   -- Testbench for sha512 done. --");
      $finish;
  end //sha512_test

endmodule
