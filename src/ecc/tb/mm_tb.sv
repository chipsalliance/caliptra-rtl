//======================================================================
//
// mm_tb.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module mm_tb();

//----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG     = 0;

  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  
  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0]  cycle_ctr;
  reg [63 : 0]  error_ctr;
  reg [63 : 0]  tc_ctr;

  reg            clk_tb;
  reg            reset_n_tb;

  reg            start_i_tb;
  reg  [383 : 0] opa_i_tb;
  reg  [383 : 0] opb_i_tb;
  wire [383 : 0] p_o_tb;
  wire           ready_tb;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  mm #(
        .REG_SIZE(384),
        .PE_UNITS(5),
        .S_NUM(13),
        .RADIX(32)
        )
        dut (
        .clk(clk_tb),
        .reset_n(reset_n_tb),

        .start_i(start_i_tb),
        .opa_i(opa_i_tb),
        .opb_i(opb_i_tb),
        .p_o(p_o_tb),
        .ready(ready_tb)
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
                            input [383 : 0] opa,
                            input [383 : 0] opb,
                            input [383 : 0] expected);
    begin
      $display("*** TC %0d mm test started.", tc_number);
      tc_ctr = tc_ctr + 1;
    
      opa_i_tb = opa;
      opb_i_tb = opb;
      #CLK_PERIOD;

      start_i_tb = 1;
      #CLK_PERIOD;

      start_i_tb = 0;
      wait_ready();

      if (p_o_tb == expected)
        begin
          $display("*** TC %0d successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d NOT successful.", tc_number);
          $display("Expected: 0x%032x", expected);
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
    reg [383 : 0] opa_1;
    reg [383 : 0] opb_1;
    reg [383 : 0] p_o_1;

    reg [383 : 0] opa_2;
    reg [383 : 0] opb_2;
    reg [383 : 0] p_o_2;

    begin
      opa_1 = 384'hb69827d455a581aa148763cac96828c994a50d2da2eae9226bc940a39b8b8a80421ba901d6a829dce6f6cdbdd28b9df4;
      opb_1 = 384'h7698f32a08d0bd3d9465032efad89cbfe5671547e5bdd9201dbb825a9ca83db17bfc8688d9669f0621ec6b87cbf0f657;
      p_o_1 = 384'h2bf656fdd371957f7afff11a33ddd0c8542128a314088f8213cd2b833542199a63fa887664d3c2dd7707e387f8d67d5e;
      
      opa_2 = 384'h7698f32a08d0bd3d9465032efad89cbfe5671547e5bdd9201dbb825a9ca83db17bfc8688d9669f0621ec6b87cbf0f657;
      opb_2 = 384'hb69827d455a581aa148763cac96828c994a50d2da2eae9226bc940a39b8b8a80421ba901d6a829dce6f6cdbdd28b9df4;
      p_o_2 = 384'h2bf656fdd371957f7afff11a33ddd0c8542128a314088f8213cd2b833542199a63fa887664d3c2dd7707e387f8d67d5e;
      
      $display("Mont 384 bit tests");
      $display("---------------------");
      mm_single_block_test(8'h01, opa_1, opb_1, p_o_1);

      mm_single_block_test(8'h02, opa_2, opb_2, p_o_2);
    end
  endtask // mm_test


  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -= Testbench for mm started =-");
      $display("    ==============================");
      $display("");

      init_sim();
      reset_dut();

      mm_test();

      display_test_results();
      
      $display("");
      $display("*** mm simulation done. ***");
      $finish;
    end // main

endmodule // mm_tb