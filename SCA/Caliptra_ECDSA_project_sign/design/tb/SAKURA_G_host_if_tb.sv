`timescale 1ns / 1ps
//======================================================================
//
// SAKURA_G_host_if.sv
// --------
// 
//
//
// Author: Emre Karabulut
//======================================================================

module SAKURA_G_host_if_tb ();

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

  logic           DEVRDY;   // Device ready
  logic           RRDYn;    // Read data empty
  logic           WRDYn;    // Write buffer almost full
  reg             HRE;      // Host read enable
  reg             HWE;      // Host write enable
  reg       [7:0] HDIN;     // Host data reg
  logic     [7:0] HDOUT;    // Host data logic

  logic           RSTOUTn;  // Internal reset logic
  logic           BUSY; // Encrypt/Decrypt select
  logic           DATA_EN;  // Encrypt or Decrypt Start

  logic [383: 0]        read_data;
  reg   [384 : 0]       d_fixed_MSB;
  logic [8:0] count_o;


  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  host_if  dut (
        .CLK(clk_tb),
        .RSTn(reset_n_tb),
        .DEVRDY(DEVRDY),
        .RRDYn(RRDYn),
        .WRDYn(WRDYn),
        .HRE(HRE),
        .HWE(HWE),
        .HDIN(HDIN),
        .HDOUT(HDOUT),
        .RSTOUTn(RSTOUTn),
        .BUSY(BUSY),
        .DATA_EN(DATA_EN),
        .COUNT(count_o)
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
  // wait_ready()
  //
  // Initialize all counters and testbed functionality as well
  // as setting the DUT inputs to defined values.
  //----------------------------------------------------------------
  task wait_ready ();
    begin
      while (BUSY == 1)
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
        cycle_ctr  = 0;


        clk_tb     = 0;
        reset_n_tb = 0;
        HRE        = 0;
        HWE        = 0;
        HDIN       = 0;
    end
  endtask // init_sim

  //----------------------------------------------------------------
  // read_word()
  //
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_single_word(input [15 : 0]  address, output [31 : 0]  data_out);
    reg [3:0] cnt;
    begin
        data_out=0;
        cnt=0;
        //-----------The First Half Read----------------------------

        // The first step is to write bus 00 to indicate that there
        // will be a read transaction.         
        HRE       = 1;
        HWE       = 1;
        HDIN      = 8'h00;
        cnt=cnt+1; // 1
        #(CLK_PERIOD);
        // The second step is to write address from MSB to LSB         
        HRE       = 1;
        HWE       = 1;
        HDIN      = address[15:8];
        cnt=cnt+1; // 2
        #(CLK_PERIOD);
        HRE       = 1;
        HWE       = 1;
        HDIN      = address[7:0];
        cnt=cnt+1; // 3
        #(CLK_PERIOD);
        // The third step is to read data from MSB to LSB         
        HRE             = 1;
        HWE             = 0;  
        cnt=cnt+1;      // 4
        #(CLK_PERIOD);


        HRE             = 1;
        HWE             = 0;
        #(CLK_HALF_PERIOD);  
        data_out[31:24] = HDOUT;
        cnt=cnt+1; // 5
        #(CLK_PERIOD);     
        
        
        data_out[23:16] = HDOUT;
        cnt=cnt+1;  // 6
        #(CLK_HALF_PERIOD);  


        //-----------The Second Half Read---------------------------

        // The first step is to write bus 00 to indicate that there
        // will be a read transaction.         
        HRE       = 1;
        HWE       = 1;
        HDIN      = 8'h00;
        cnt=cnt+1; // 7
        #(CLK_PERIOD);
        // The second step is to write address from MSB to LSB         
        HRE       = 1;
        HWE       = 1;
        HDIN      = address[15:8];
        cnt=cnt+1; // 8
        #(CLK_PERIOD);
        HRE       = 1;
        HWE       = 1;
        HDIN      = {address[7:2], 2'b10};
        cnt=cnt+1;  // 9
        #(CLK_PERIOD);
        // The third step is to read data from MSB to LSB         
        HRE             = 1;
        HWE             = 0;
        cnt=cnt+1; // 10
        #(CLK_PERIOD);
        HRE             = 1;
        HWE             = 0;
        cnt=cnt+1; // 11
        #(CLK_HALF_PERIOD); 
        data_out[15:8]  = HDOUT;
        cnt=cnt+1; // 12
        #(CLK_PERIOD);  
        data_out[7:0]   = HDOUT;
        cnt=cnt+1; // 13
        #(CLK_HALF_PERIOD); 
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
    reg [7:0] i_enc;
    logic [31 : 0] data_out2;
    begin
      data_out2=0;
      read_single_word({3'b010,address[4:0],8'h00}, data_out2);
      #(2*CLK_PERIOD);
      data_out2=0;
      for (int i = 0; i < 12; i++) begin
        i_enc=i<<2;
        read_single_word({3'b010,address[4:0],i_enc}, data_out2);
        read_data = {data_out2, read_data[383 : 32]};
      end
    end
  endtask // read_reg

  //----------------------------------------------------------------
  // read_AES_ciphertext()
  //
  // Read a reg from the given address in the DUT.
  // the reg will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_AES_ciphertext(input [15 : 0]  address);
    logic [31 : 0] data_out2;
    begin
      data_out2=0;
      read_data=0;
      for (int i = 0; i < 4; i++) begin
        read_single_word(address+i*4, data_out2);
        read_data = {read_data[95 : 0], data_out2};
      end
    end
  endtask // read_AES_ciphertext

  //----------------------------------------------------------------
  // write_single_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_word(input [15 : 0]  address, input [31 : 0] word);
    begin
      //-----------The First Half Write----------------------------

      // The first step is to write bus 00 to indicate that there
      // will be a write transaction.         
      HRE       = 0;
      HWE       = 1;
      HDIN      = 8'h01;
      #(CLK_PERIOD);
      // The second step is to write address from MSB to LSB         
      HRE       = 0;
      HWE       = 1;
      HDIN      = address[15:8];
      #(CLK_PERIOD);
      HRE       = 0;
      HWE       = 1;
      HDIN      = address[7:0];
      #(CLK_PERIOD);
      // The third step is to write data from MSB to LSB         
      HRE       = 0;
      HWE       = 1;
      HDIN      = word[31:24];
      #(CLK_PERIOD);         
      HRE       = 0;
      HWE       = 1;
      HDIN      = word[23:16];
      #(CLK_PERIOD);
      //-----------The Second Half Write---------------------------

      // The first step is to write bus 00 to indicate that there
      // will be a read transaction.         
      HRE       = 0;
      HWE       = 1;
      HDIN      = 8'h01;
      #(CLK_PERIOD);
      // The second step is to write address from MSB to LSB         
      HRE       = 0;
      HWE       = 1;
      HDIN      = address[15:8];
      #(CLK_PERIOD);
      HRE       = 0;
      HWE       = 1;
      HDIN      = {address[7:2], 2'b10};
      #(CLK_PERIOD);
      // The third step is to write data from MSB to LSB         
      HRE       = 0;
      HWE       = 1;
      HDIN      = word[15:8];
      #(CLK_PERIOD);         
      HRE       = 0;
      HWE       = 1;
      HDIN      = word[7:0];
      #(CLK_PERIOD);
      HWE       = 0;
    end
  endtask // write_single_word


  //----------------------------------------------------------------
  // write_scalar()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_scalar(input [384 : 0] word);
    reg [7:0] i_enc;
    begin
      for (int i = 0; i < 12; i++) begin
        i_enc=i<<2;
        write_single_word({8'h80,i_enc}, word[32*i +: 32] );
      end
      i_enc=12<<2;
      write_single_word({8'h80,i_enc}, {31'h0, word[384]});
      #(CLK_PERIOD);
    end
  endtask // write_scalar

  //----------------------------------------------------------------
  // write_reg()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_reg(input [7 : 0]  address, input [383 : 0] word);
    reg [7:0] i_enc;
    begin
      for (int i = 0; i < 12; i++) begin
        i_enc=i<<2;
        write_single_word({3'b010,address[4:0],i_enc}, word[32*i +: 32] );
      end
      #(CLK_PERIOD);
    end
  endtask // write_reg

  //----------------------------------------------------------------
  // trig_ECPM()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task trig_ECPM;
    begin
      write_single_word(16'h3000, 32'h0);
    end
  endtask // trig_ECPM


  

  //----------------------------------------------------------------
  // write_AES_plaintext_Key()
  //
  //----------------------------------------------------------------
  task write_AES_plaintext_Key(input [15 : 0]  address, [127:0] data_in);
    begin
      for (int i = 0; i < 4; i++) begin
        write_single_word(address+i*4, data_in[(127-32*i) -: 32]);
      end
    end
  endtask // write_AES_plaintext_Key

  //----------------------------------------------------------------
  // aes_single_block_test()
  //----------------------------------------------------------------
  task if_single_RW_test(input [15 : 0]  key_addr, 
                        input [15 : 0]  ptext_addr,
                        input [15 : 0]  ctext_addr,
                        input [127 : 0] key,
                        input [127 : 0] ptext);
    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    reg [127 : 0]   RESULT;
  begin
    
    $display("*** test started ***");
  
    start_time = cycle_ctr;
    write_AES_plaintext_Key(key_addr,key);
    write_AES_plaintext_Key(ptext_addr,ptext);
    #(10*CLK_PERIOD);
    RESULT     = key^ptext;
    read_AES_ciphertext(ctext_addr);

    if (RESULT == read_data)
    begin
      $display("*** TC successful.");
      $display("");
    end
    else
    begin
      $display("*** ERROR: TC NOT successful.");
      $display("read value    : 0x%32x", read_data);
      $display("Expected      : 0x%32x", RESULT);
      $display("");
      error_ctr = error_ctr + 1;
    end
  end
  endtask //if_single_RW_test

  task C_sharp_coder (input [415:0] data_frame);
    reg [31:0] word;
    begin
      word=0; 
      for (int i = 0; i < 13; i++)
      begin
        word = data_frame [32*i +: 32]; 
        $display("0x%2x, 0x%2x, 0x%2x, 0x%2x,",word[31:24],word[23:16], word[15:8], word[7:0]);
      end
    end
  endtask

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
    $display("-----E_a_MONT----");
    C_sharp_coder(E_a_MONT);
    write_reg(UOP_OPR_CONST_ONE_MONT, ONE_MONT);
    $display("-----------------");
    C_sharp_coder(ONE_MONT);
    write_reg(UOP_OPR_CONST_GX_MONT, P[0]);
    $display("-----------------");
    C_sharp_coder(P[0]);    
    write_reg(UOP_OPR_CONST_GY_MONT, P[1]);
    $display("-----------------");
    C_sharp_coder(P[1]);
    write_reg(UOP_OPR_CONST_GZ_MONT, P[2]);
    $display("-----------------");
    C_sharp_coder( P[2]);
    
    write_scalar(scalar);
    $display("-----------------");
    C_sharp_coder( scalar);
    $display("----EXPECTED1---");
    C_sharp_coder( expected[0]);
    $display("----EXPECTED2---");
    C_sharp_coder( expected[1]);
    
    trig_ECPM();

    wait_ready ();

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

  task ecc_main_test();
    reg [383 : 0] G_MONT [0 : 2];
    reg [383 : 0] d;
    reg [383 : 0] Q [0 : 1];
    begin

      $display("ECPM 384 bit tests");
      $display("---------------------");

      G_MONT[0] = G_X_MONT;
      G_MONT[1] = G_Y_MONT;
      G_MONT[2] = G_Z_MONT;

      d    = 384'hD27335EA71664AF244DD14E9FD1260715DFD8A7965571C48D709EE7A7962A156D706A90CBCB5DF2986F05FEADB9376F1;
      Q[0] = 384'h793148F1787634D5DA4C6D9074417D05E057AB62F82054D10EE6B0403D6279547E6A8EA9D1FD77427D016FE27A8B8C66;
      Q[1] = 384'hC6C41294331D23E6F480F4FB4CD40504C947392E94F4C3F06B8F398BB29E42368F7A685923DE3B67BACED214A1A1D128;

      fix_MSB(d);

      ecc_single_block_test(0, G_MONT, d_fixed_MSB, Q);
      
    end
  endtask


  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      $display("   -= Testbench for host interface started =-");
      $display("    ==============================");
      $display("");

      init_sim();
      reset_dut();
      #(CLK_HALF_PERIOD);  

      //if_single_RW_test(16'h8000, 16'h4000, 16'h5000, 128'hf000000a_f000000b_f000000c_f0001234,
      //                                                128'h01234560_01234560_01234560_0fff0000);

      ecc_main_test();
      
      $display("");
      $display("*** host interface simulation done. ***");
      //$finish;
    end // main

endmodule