//======================================================================
//
// ecc_arith_unit_tb.sv
// --------
// 
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module ecc_arith_unit_tb #(
    parameter   TEST_VECTOR_NUM = 15
)
();

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter [383 : 0] E_a_MONT = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffcfffffffbffffffff00000002fffffffdffffffff;
  parameter [383 : 0] ONE_p_MONT = 384'h100000000ffffffffffffffff0000000100000000;
  parameter [383 : 0] G_X_MONT = 384'h299e1513812ff723614ede2b6454868459a30eff879c3afc541b4d6e6e1e26a4ee117bfa3dd07565fc8607664d3aadc2;
  parameter [383 : 0] G_Y_MONT = 384'h5a15c5e9dd8002263969a840c6c3521968f4ffd98bade7562e83b050cd385481a72d556e23043dad1f8af93c2b78abc2;
  parameter [383 : 0] G_Z_MONT = 384'h100000000ffffffffffffffff0000000100000000;
  //parameter [383 : 0] R2_MONT  = 384'h10000000200000000fffffffe000000000000000200000000fffffffe000000010000000000000000;

  // q
  parameter [383 : 0] group_order = 384'hffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973; 
  parameter [383 : 0] R2_q_MONT  = 384'h3fb05b7a28266895d40d49174aab1cc5bf030606de609f43be80721782118942bfd3ccc974971bd0d8d34124f50ddb2d;
  parameter [383 : 0] ONE_q_MONT = 384'h389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d00000000;


  parameter [383 : 0] UOP_OPR_CONST_ZERO        = 8'd00;
  parameter [383 : 0] UOP_OPR_CONST_ONE         = 8'd01;
  parameter [383 : 0] UOP_OPR_CONST_E_a         = 8'd02;
  parameter [383 : 0] UOP_OPR_CONST_ONE_MONT    = 8'd03;

  parameter [383 : 0] UOP_OPR_CONST_GX_MONT     = 8'd05;
  parameter [383 : 0] UOP_OPR_CONST_GY_MONT     = 8'd06;
  parameter [383 : 0] UOP_OPR_CONST_GZ_MONT     = 8'd07;
  
  parameter [383 : 0] UOP_OPR_Qx_AFFN           = 8'd16;
  parameter [383 : 0] UOP_OPR_Qy_AFFN           = 8'd17;

  parameter [383 : 0] UOP_OPR_SIGN_R            = 8'd18;
  parameter [383 : 0] UOP_OPR_SIGN_S            = 8'd19;

  parameter [383 : 0] UOP_OPR_PRIVKEY           = 8'd20;
  parameter [383 : 0] UOP_OPR_HASH_MSG          = 8'd21;
  parameter [383 : 0] UOP_OPR_SCALAR_G          = 8'd22;

  parameter [383 : 0] UOP_OPR_CONST_ONE_q_MONT  = 8'd28;  // Mont_mult(1, R2) % q
  parameter [383 : 0] UOP_OPR_CONST_q_R2        = 8'd29;

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
      operand_t     k;
      operand_t     R;
      operand_t     S;
  } test_vector_t;

  test_vector_t [TEST_VECTOR_NUM-1:0] test_vectors;
  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG           = 0;

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

  int                   test_vector_cnt;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  ecc_arith_unit #(
        .REG_SIZE(REG_SIZE),
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
  // ecc_keygen_test()
  //
  // Perform a single point multiplication block test.
  //----------------------------------------------------------------
  task ecc_keygen_test(input [7 : 0]  tc_number,
                       input test_vector_t test_vector);
    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    affn_point_t   pubkey;
    begin
      $display("*** TC %0d keygen test started.", tc_number);
      tc_ctr = tc_ctr + 1;
    
      start_time = cycle_ctr;
      // writing constant values
      write_reg(UOP_OPR_CONST_ZERO, 384'h0);
      write_reg(UOP_OPR_CONST_ONE, 384'h1);
      write_reg(UOP_OPR_CONST_E_a, E_a_MONT);
      write_reg(UOP_OPR_CONST_ONE_MONT, ONE_p_MONT);
      write_reg(UOP_OPR_CONST_GX_MONT, G_X_MONT);
      write_reg(UOP_OPR_CONST_GY_MONT, G_Y_MONT);
      write_reg(UOP_OPR_CONST_GZ_MONT, G_Z_MONT);

      fix_MSB(test_vector.privkey);
      write_scalar(d_fixed_MSB);

      trig_ECPM(KEYGEN_CMD);

      wait_ready();

      read_reg(UOP_OPR_Qx_AFFN);
      pubkey.x = read_data;

      read_reg(UOP_OPR_Qy_AFFN);
      pubkey.y = read_data;
      
      end_time = cycle_ctr - start_time;
      $display("*** keygen test processing time = %01d cycles.", end_time);
      $display("privkey    : 0x%96x", test_vector.privkey);

      if (pubkey == test_vector.pubkey)
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
      $display("*** TC %0d signing test started.", tc_number);
      tc_ctr = tc_ctr + 1;

      start_time = cycle_ctr;
      write_reg(UOP_OPR_CONST_ZERO, 384'h0);
      write_reg(UOP_OPR_CONST_ONE, 384'h1);
      write_reg(UOP_OPR_CONST_E_a, E_a_MONT);
      write_reg(UOP_OPR_CONST_ONE_MONT, ONE_p_MONT);
      write_reg(UOP_OPR_CONST_ONE_q_MONT, ONE_q_MONT);
      write_reg(UOP_OPR_CONST_q_R2, R2_q_MONT);

      write_reg(UOP_OPR_CONST_GX_MONT, G_X_MONT);
      write_reg(UOP_OPR_CONST_GY_MONT, G_Y_MONT);
      write_reg(UOP_OPR_CONST_GZ_MONT, G_Z_MONT);

      write_reg(UOP_OPR_HASH_MSG, test_vector.hashed_msg);
      write_reg(UOP_OPR_PRIVKEY, test_vector.privkey);
      write_reg(UOP_OPR_SCALAR_G, test_vector.k);

      fix_MSB(test_vector.k);
      write_scalar(d_fixed_MSB);

      trig_ECPM(SIGN_CMD);

      wait_ready();

      read_reg(UOP_OPR_SIGN_R);
      R = read_data;

      read_reg(UOP_OPR_SIGN_S);
      S = read_data;
      
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
  // ecc_test()
  //
  //----------------------------------------------------------------
  task ecc_test();
    begin   
      $display("ECC KEYGEN TEST");
      $display("---------------------");

      for (int i = 0; i < test_vector_cnt; i++) begin: test_vector_loop
          ecc_keygen_test(i, test_vectors[i]);
          ecc_signing_test(i, test_vectors[i]);
      end

      $display("ECC SIGNING TEST");
      $display("---------------------");

    end
  endtask // ecc_test


  task read_test_vectors(input string fname);
      integer values_per_test_vector;
      integer line_cnt;
      integer fin;
      integer rv;
      r_t val;    // must be the largest width of any possible value
      test_vector_t test_vector;

      // ATTN: Must match the number of fields generated by gen_mm_test_vectors.py script
      values_per_test_vector = 8;
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
              4: test_vector.k           = val;
              5: test_vector.R           = val;
              6: begin
                 test_vector.S           = val;
                 test_vectors[test_vector_cnt] = test_vector;
              end
              7 : test_vector_cnt++;
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

      $display("   -= Testbench for ecc started =-");
      $display("    ==============================");
      $display("");

      fname = "/home/mojtabab/workspace_aha_poc/ws1/Caliptra/src/ecc/tb/test_vectors/ecc_test_vectors.hex";
      read_test_vectors(fname);

      init_sim();
      reset_dut();

      ecc_test();

      display_test_results();
      
      $display("");
      $display("*** ecc simulation done. ***");
      $finish;
    end // main

endmodule // ecc_arith_unit_tb