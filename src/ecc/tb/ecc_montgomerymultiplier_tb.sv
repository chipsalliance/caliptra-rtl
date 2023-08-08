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
// mm_tb.sv
// --------
// 
//
//
//======================================================================

module ecc_montgomerymultiplier_tb #(
    parameter   OPERAND_WIDTH = 16,
    parameter   WORD_WIDTH = 4,
    parameter   TEST_VECTOR_NUM = 5
  )
  ();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  localparam                  TEST_VECTOR_ID_WIDTH = $clog2(TEST_VECTOR_NUM);
  
  localparam                  STAT_CNT_WIDTH = 64;
  localparam  int unsigned    S_NUM   = $ceil(real'(OPERAND_WIDTH) / WORD_WIDTH) + 1;
  // NOTE: This is for Optimized FIOS Montgomery Multiplication Algorithm.
  // It can be changed for other algorithms.
  localparam                  R_WIDTH = S_NUM * WORD_WIDTH + 1;

  //----------------------------------------------------------------
  // Type definitions
  //---------------------------------------------------------------- 
  typedef bit     [STAT_CNT_WIDTH-1:0]            stat_t;
  typedef bit     [OPERAND_WIDTH-1:0]             operand_t;
  typedef bit     [WORD_WIDTH-1:0]                word_t;
  typedef bit     [TEST_VECTOR_ID_WIDTH-1:0]      test_vector_id_t;
  typedef bit     [R_WIDTH-1:0]                   r_t;

  typedef struct packed {
      operand_t   a;
      operand_t   b;
      //operand_t   r_inverse;  // inverse is modulo 'n', therefore it has operand_t type
      operand_t   n;
      r_t         n_prime;    // n' = -n^(-1) mod r, therefore it is wider and has r_t type
      operand_t   product;
  } test_vector_t;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  stat_t      cycle_ctr;
  stat_t      error_ctr;
  stat_t      tc_ctr;

  logic       clk_tb;
  logic       reset_n_tb;

  logic       start_i_tb;
  operand_t   opa_i_tb;
  operand_t   opb_i_tb;
  operand_t   n_i_tb;
  word_t      n_prime_i_tb;
  operand_t   p_o_tb;
  logic       ready_tb;
  int         test_vector_cnt;

  test_vector_t [TEST_VECTOR_NUM-1:0] test_vectors;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  ecc_montgomerymultiplier #(
      .REG_SIZE   (OPERAND_WIDTH),
      .RADIX      (WORD_WIDTH)
  )
  mm_dut (
      .clk        (clk_tb),
      .reset_n    (reset_n_tb),
      .zeroize    (1'b0),

      .start_i    (start_i_tb),
      .opa_i      (opa_i_tb),
      .opb_i      (opb_i_tb),
      .n_i        (n_i_tb),
      .n_prime_i  (n_prime_i_tb),
      .p_o        (p_o_tb),
      .ready_o    (ready_tb)
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
    end 

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
      cycle_ctr     = 0;
      error_ctr     = 0;
      tc_ctr        = 0;

      clk_tb        = 0;
      reset_n_tb    = 0;

      start_i_tb    = 0;
      opa_i_tb      = '0;
      opb_i_tb      = '0;
      n_i_tb        = '0;
      n_prime_i_tb  = '0;
    end
  endtask // init_sim


  //----------------------------------------------------------------
  // wait_ready()
  //
  // Initialize all counters and testbed functionality as well
  // as setting the DUT inputs to defined values.
  //----------------------------------------------------------------
  task wait_ready;
    begin
      while (ready_tb == 0)
        begin
            #CLK_PERIOD;
        end
    end
  endtask // init_sim

  
  //----------------------------------------------------------------
  // mm_single_block_test()
  //
  // Perform a single Montgomery multiplication block test.
  //----------------------------------------------------------------
  task mm_single_block_test(input [7 : 0]   tc_number,
                            input test_vector_t test_vector);
    begin
      $display("*** TC %0d mm test started.", tc_number);
      tc_ctr = tc_ctr + 1;
    
      $display("Computing product of:\n0x%0x\n0x%0x\nmod 0x%0x\n", test_vector.a, test_vector.b, test_vector.n);
      opa_i_tb     = test_vector.a;
      opb_i_tb     = test_vector.b;
      n_i_tb       = test_vector.n;
      //only need to pass the last few bits of n_prime
      n_prime_i_tb = test_vector.n_prime[WORD_WIDTH-1:0];

      #CLK_PERIOD;

      start_i_tb = 1;
      #CLK_PERIOD;

      start_i_tb = 0;
      wait_ready();

      if (p_o_tb == test_vector.product)
        begin
          $display("*** TC %0d successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d NOT successful.", tc_number);
          $display("Expected: 0x%032x", test_vector.product);
          $display("Got:      0x%032x", p_o_tb);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // mm_single_block_test



  //----------------------------------------------------------------
  // mm_test()
  //
  //----------------------------------------------------------------
  task mm_test;        
      for (int i = 0; i < test_vector_cnt; i++) begin: test_vector_loop
          mm_single_block_test(i, test_vectors[i]);
      end
  endtask

  task read_test_vectors(input string fname);
      integer values_per_test_vector;
      integer line_cnt;
      integer fin;
      integer rv;
      r_t val;    // must be the largest width of any possible value
      test_vector_t test_vector;

      // ATTN: Must match the number of fields generated by gen_mm_test_vectors.py script
      values_per_test_vector = 6;
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
              0: test_vector.a            = val;
              1: test_vector.b            = val;
              //2: test_vector.r_inverse    = val;
              2: test_vector.n            = val;
              3: test_vector.n_prime      = val;
              4: begin
                 test_vector.product      = val;
                 test_vectors[test_vector_cnt] = test_vector;
              end
              5 : test_vector_cnt++;
          endcase
          
          line_cnt++;
      end
      $fclose(fin);

      $display("Read %0d test vectors from %s", test_vector_cnt, fname);
  endtask

  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      string fname;

      $display("   -= Testbench for mm started =-");
      $display("    ==============================\n");

      fname = $sformatf("mm_test_vectors_%0d_key_%0d_word_%0d.hex", TEST_VECTOR_NUM, OPERAND_WIDTH, WORD_WIDTH);

      read_test_vectors(fname);

      init_sim();
      reset_dut();

      mm_test();

      display_test_results();
      
      $display("");
      $display("*** mm simulation done. ***");
      $finish;
    end // main

endmodule // mm_tb
