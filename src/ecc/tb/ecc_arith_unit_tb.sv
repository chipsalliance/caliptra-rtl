//======================================================================
//
// ecc_arith_unit_tb.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module ecc_arith_unit_tb();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter [383 : 0] E_a_MONT = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffcfffffffbffffffff00000002fffffffdffffffff;
  parameter [383 : 0] ONE_MONT = 384'h100000000ffffffffffffffff0000000100000000;
  parameter [383 : 0] G_X_MONT = 384'h299e1513812ff723614ede2b6454868459a30eff879c3afc541b4d6e6e1e26a4ee117bfa3dd07565fc8607664d3aadc2;
  parameter [383 : 0] G_Y_MONT = 384'h5a15c5e9dd8002263969a840c6c3521968f4ffd98bade7562e83b050cd385481a72d556e23043dad1f8af93c2b78abc2;
  parameter [383 : 0] G_Z_MONT = 384'h100000000ffffffffffffffff0000000100000000;

  // q
  parameter [383 : 0] group_order = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973; 

  parameter [383 : 0] UOP_OPR_CONST_ZERO        = 8'd00;
  parameter [383 : 0] UOP_OPR_CONST_ONE         = 8'd01;
  parameter [383 : 0] UOP_OPR_CONST_E_a         = 8'd02;
  parameter [383 : 0] UOP_OPR_CONST_ONE_MONT    = 8'd03;

  parameter [383 : 0] UOP_OPR_CONST_GX_MONT     = 8'd04;
  parameter [383 : 0] UOP_OPR_CONST_GY_MONT     = 8'd05;
  parameter [383 : 0] UOP_OPR_CONST_GZ_MONT     = 8'd06;

  parameter [383 : 0] UOP_OPR_R0_X              = 8'd08;  // 8'b0000_1000;
  parameter [383 : 0] UOP_OPR_R0_Y              = 8'd09;  // 8'b0000_1001;
  parameter [383 : 0] UOP_OPR_R0_Z              = 8'd10;  // 8'b0000_1010;
  
  parameter [383 : 0] UOP_OPR_CONST_Qx_AFFN     = 8'd16;
  parameter [383 : 0] UOP_OPR_CONST_Qy_AFFN     = 8'd17;
  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG     = 0;

  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  parameter REG_SIZE      = 384;
  parameter PRIME         = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff;
  parameter ADD_NUM_ADDS  = 1;
  parameter ADD_BASE_SZ   = 384;


  localparam NOP_CMD        = 3'b000;
  localparam KEYGEN_CMD     = 3'b001;
  localparam SIGN_CMD       = 3'b010;
  localparam VERIFY_CMD     = 3'b100;
  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0]  cycle_ctr;
  reg [63 : 0]  error_ctr;
  reg [63 : 0]  tc_ctr;

  reg            clk_tb;
  reg            reset_n_tb;

  logic [2 : 0]         ecc_cmd_i_tb;
  logic [7 : 0]         addr_i_tb;
  logic                 wr_input_sel_i_tb;
  logic [1 : 0]         wr_op_sel_i_tb;
  logic [3 : 0]         wr_word_sel_i_tb;
  logic                 wr_en_i_tb;
  logic                 rd_reg_i_tb;
  logic [1 : 0]         rd_op_sel_i_tb;
  logic [3 : 0]         rd_word_sel_i_tb;
  logic [31: 0]         data_i_tb;
  logic [31: 0]         data_o_tb;
  logic                 busy_o_tb;

  logic [383 : 0]       read_data;
  reg   [384 : 0]       d_fixed_MSB;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  ecc_arith_unit #(
        .REG_SIZE(REG_SIZE),
        .PRIME(PRIME),
        .ADD_NUM_ADDS(ADD_NUM_ADDS),
        .ADD_BASE_SZ(ADD_BASE_SZ)
        )
        dut (
        .clk(clk_tb),
        .reset_n(reset_n_tb),
        .ecc_cmd_i(ecc_cmd_i_tb),
        .addr_i(addr_i_tb),
        .wr_input_sel_i(wr_input_sel_i_tb),
        .wr_op_sel_i(wr_op_sel_i_tb),
        .wr_word_sel_i(wr_word_sel_i_tb),
        .wr_en_i(wr_en_i_tb),
        .rd_reg_i(rd_reg_i_tb),
        .rd_op_sel_i(rd_op_sel_i_tb),
        .rd_word_sel_i(rd_word_sel_i_tb),
        .data_i(data_i_tb),
        .data_o(data_o_tb),
        .busy_o(busy_o_tb)
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

      clk_tb        = 1;
      reset_n_tb    = 0;

      ecc_cmd_i_tb      = NOP_CMD;
      addr_i_tb         = 0;
      wr_input_sel_i_tb = 0;
      wr_op_sel_i_tb    = 0;
      wr_word_sel_i_tb  = 0;
      wr_en_i_tb        = 0;
      rd_reg_i_tb       = 0;
      rd_op_sel_i_tb    = 0;
      rd_word_sel_i_tb  = 0;
      data_i_tb         = 0;
    end
  endtask // init_sim


  //----------------------------------------------------------------
  // wait_ready()
  //
  // Initialize all counters and testbed functionality as well
  // as setting the DUT inputs to defined values.
  //----------------------------------------------------------------
  task wait_ready();
    begin
      while (busy_o_tb == 1)
        begin
            #CLK_PERIOD;
        end
    end
  endtask // init_sim


  //----------------------------------------------------------------
  // read_word()
  //
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_single_word(input [1 : 0] reg_type, input [7 : 0]  address, input [7 : 0]  word_sel);
    begin
      ecc_cmd_i_tb      = NOP_CMD;
      addr_i_tb         = address;
      wr_input_sel_i_tb = 0;
      wr_op_sel_i_tb    = 0;
      wr_word_sel_i_tb  = 0;
      wr_en_i_tb        = 0;
      rd_reg_i_tb       = 1;
      rd_op_sel_i_tb    = reg_type;
      rd_word_sel_i_tb  = word_sel;
      data_i_tb         = 0;
      #(CLK_PERIOD);
    end
  endtask // read_word


  //----------------------------------------------------------------
  // read_reg()
  //
  // Read a reg from the given address in the DUT.
  // the reg will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_reg(input [7 : 0]  address);
    begin
      read_single_word(2'b00, address, 0);
      #(2*CLK_PERIOD);
      for (int i = 0; i < 12; i++) begin
        read_single_word(2'b00, address, i);
        read_data = {data_o_tb, read_data[383 : 32]};
      end
    end
  endtask // read_reg


  //----------------------------------------------------------------
  // read_scalar()
  //
  // Read a reg from the given address in the DUT.
  // the reg will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_scalar();
    begin
      for (int i = 0; i < 12; i++) begin
        read_single_word(2'b01, 8'h00, i);
        read_data = {data_o_tb, read_data[383 : 32]};
      end
    end
  endtask // read_scalar


  //----------------------------------------------------------------
  // write_single_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_word(input [1 : 0] reg_type, input [7 : 0]  address, input [7 : 0]  word_sel, input [31 : 0] word);
    begin
      ecc_cmd_i_tb      = NOP_CMD;
      addr_i_tb         = address;
      wr_input_sel_i_tb = 0;
      wr_op_sel_i_tb    = reg_type;
      wr_word_sel_i_tb  = word_sel;
      wr_en_i_tb        = 1;
      rd_reg_i_tb       = 0;
      rd_op_sel_i_tb    = 0;
      rd_word_sel_i_tb  = 0;
      data_i_tb         = word;
      #(CLK_PERIOD);
    end
  endtask // write_single_word


  //----------------------------------------------------------------
  // write_reg()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_reg(input [7 : 0]  address, input [383 : 0] word);
    begin
      for (int i = 0; i < 12; i++) begin
        write_single_word(2'b00, address, i, word[32*i +: 32]);
      end
      #(CLK_PERIOD);
      ecc_cmd_i_tb      = NOP_CMD;
      addr_i_tb         = 0;
      wr_input_sel_i_tb = 0;
      wr_op_sel_i_tb    = 0;
      wr_word_sel_i_tb  = 0;
      wr_en_i_tb        = 0;
      rd_reg_i_tb       = 0;
      rd_op_sel_i_tb    = 0;
      rd_word_sel_i_tb  = 0;
      data_i_tb         = 0;
      #(CLK_PERIOD);
    end
  endtask // write_reg


  //----------------------------------------------------------------
  // write_scalar()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_scalar(input [384 : 0] word);
    begin
      for (int i = 0; i < 13; i++) begin
        write_single_word(2'b01, 8'h00 , i, word[32*i +: 32]);
      end
      #(CLK_PERIOD);
      ecc_cmd_i_tb      = NOP_CMD;
      addr_i_tb         = 0;
      wr_input_sel_i_tb = 0;
      wr_op_sel_i_tb    = 0;
      wr_word_sel_i_tb  = 0;
      wr_en_i_tb        = 0;
      rd_reg_i_tb       = 0;
      rd_op_sel_i_tb    = 0;
      rd_word_sel_i_tb  = 0;
      data_i_tb         = 0;
      #(CLK_PERIOD);
    end
  endtask // write_scalar


  //----------------------------------------------------------------
  // fix_MSB()
  //
  // Set MSB of scalar to 1.
  //----------------------------------------------------------------
  task fix_MSB(input [383 : 0] d);
    reg [385 : 0] d_q;
    reg [385 : 0] d_2q;
    begin
      d_q = d + group_order;
      d_2q = d_q + group_order;
      if ((d_q >> 384) == 1)
        d_fixed_MSB = d_q[384 : 0];
      else
        d_fixed_MSB = d_2q[384 : 0];
    end
  endtask // fix_MSB

  //----------------------------------------------------------------
  // trig_ECPM()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task trig_ECPM(input [2 : 0] cmd);
    begin
      ecc_cmd_i_tb      = cmd;
      addr_i_tb         = 0;
      wr_input_sel_i_tb = 0;
      wr_op_sel_i_tb    = 0;
      wr_word_sel_i_tb  = 0;
      wr_en_i_tb        = 0;
      rd_reg_i_tb       = 0;
      rd_op_sel_i_tb    = 0;
      rd_word_sel_i_tb  = 0;
      data_i_tb         = 0;
      #(CLK_PERIOD);
    end
  endtask // trig_ECPM


  //----------------------------------------------------------------
  // ecc_single_block_test()
  //
  // Perform a single point multiplication block test.
  //----------------------------------------------------------------
  task ecc_single_block_test(input [7 : 0]  tc_number,
                            input [383 : 0] P[0 : 2],
                            input [384 : 0] scalar,
                            input [383 : 0] expected[0 : 1]);
    reg [383 : 0]   Q [0 : 1];
    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    begin
      $display("*** TC %0d ECPM test started.", tc_number);
      tc_ctr = tc_ctr + 1;
    
      start_time = cycle_ctr;
      write_reg(UOP_OPR_CONST_ZERO, 384'h0);
      write_reg(UOP_OPR_CONST_ONE, 384'h1);
      write_reg(UOP_OPR_CONST_E_a, E_a_MONT);
      write_reg(UOP_OPR_CONST_ONE_MONT, ONE_MONT);

      write_reg(UOP_OPR_CONST_GX_MONT, P[0]);
      write_reg(UOP_OPR_CONST_GY_MONT, P[1]);
      write_reg(UOP_OPR_CONST_GZ_MONT, P[2]);

      write_scalar(scalar);

      trig_ECPM(KEYGEN_CMD);

      wait_ready();

      read_reg(UOP_OPR_CONST_Qx_AFFN);
      Q[0] = read_data;

      read_reg(UOP_OPR_CONST_Qy_AFFN);
      Q[1] = read_data;
      
      end_time = cycle_ctr - start_time;
      $display("*** single block test processing time = %01d cycles.", end_time);
      
      if (Q == expected)
        begin
          $display("*** TC %0d successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d NOT successful.", tc_number);
          $display("scalar    : 0x%96x", scalar);
          $display("Expected_x: 0x%96x", expected[0]);
          $display("Got:        0x%96x", Q[0]);
          $display("Expected_y: 0x%96x", expected[1]);
          $display("Got:        0x%96x", Q[1]);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // ecc_single_block_test



  //----------------------------------------------------------------
  // ecc_test()
  //
  //----------------------------------------------------------------
  task ecc_test();
    reg [383 : 0] G_MONT [0 : 2];
    reg [383 : 0] d;
    reg [383 : 0] Q [0 : 1];

    integer               data_file;
    integer               scan_file;
    reg     [383:0]       captured_data;

    integer               test_cnt; 
    begin

      test_cnt = 0;

      data_file = $fopen("/home/mojtabab/workspace_aha_poc/ws1/Caliptra/src/ecc/tb/ecc_test_vectors.txt", "r");
      if (!data_file)
        $display("data_file handle was NULL");

      $display("ECPM 384 bit tests");
      $display("---------------------");

      G_MONT[0] = G_X_MONT;
      G_MONT[1] = G_Y_MONT;
      G_MONT[2] = G_Z_MONT;

      while(!$feof(data_file)) begin
        for (int i = 0; i < 3; i++) begin
          scan_file = $fscanf(data_file, "%h\n", captured_data); 
          case(i)
            0 : d    = captured_data;
            1 : Q[0] = captured_data;
            2 : Q[1] = captured_data;
            default : begin end
          endcase
        end

        fix_MSB(d);

        test_cnt = test_cnt + 1;
        ecc_single_block_test(test_cnt, G_MONT, d_fixed_MSB, Q);
      end
    end
  endtask // ecc_test


  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -= Testbench for ecc started =-");
      $display("    ==============================");
      $display("");

      init_sim();
      reset_dut();

      ecc_test();

      display_test_results();
      
      $display("");
      $display("*** ecc simulation done. ***");
      $finish;
    end // main

endmodule // ecc_arith_unit_tb