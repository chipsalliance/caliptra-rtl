//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
//    This interface performs the AES_in signal driving.  It is
//     accessed by the uvm AES_in driver through a virtual interface
//     handle in the AES_in configuration.  It drives the singals passed
//     in through the port connection named bus of type AES_in_if.
//
//     Input signals from the AES_in_if are assigned to an internal input
//     signal with a _i suffix.  The _i signal should be used for sampling.
//
//     The input signal connections are as follows:
//       bus.signal -> signal_i 
//
//     This bfm drives signals with a _o suffix.  These signals
//     are driven onto signals within AES_in_if based on INITIATOR/RESPONDER and/or
//     ARBITRATION/GRANT status.  
//
//     The output signal connections are as follows:
//        signal_o -> bus.signal
//
//                                                                                           
//      Interface functions and tasks used by UVM components:
//
//             configure:
//                   This function gets configuration attributes from the
//                   UVM driver to set any required BFM configuration
//                   variables such as 'initiator_responder'.                                       
//                                                                                           
//             initiate_and_get_response:
//                   This task is used to perform signaling activity for initiating
//                   a protocol transfer.  The task initiates the transfer, using
//                   input data from the initiator struct.  Then the task captures
//                   response data, placing the data into the response struct.
//                   The response struct is returned to the driver class.
//
//             respond_and_wait_for_next_transfer:
//                   This task is used to complete a current transfer as a responder
//                   and then wait for the initiator to start the next transfer.
//                   The task uses data in the responder struct to drive protocol
//                   signals to complete the transfer.  The task then waits for 
//                   the next transfer.  Once the next transfer begins, data from
//                   the initiator is placed into the initiator struct and sent
//                   to the responder sequence for processing to determine 
//                   what data to respond with.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import AES_in_pkg_hdl::*;
`include "src/AES_in_macros.svh"

interface AES_in_driver_bfm #(
  int AHB_DATA_WIDTH = 32,
  int AHB_ADDR_WIDTH = 32,
  bit BYPASS_HSEL = 0
  )

  (AES_in_if bus);
  // The following pragma and additional ones in-lined further below are for running this BFM on Veloce
  // pragma attribute AES_in_driver_bfm partition_interface_xif

`ifndef XRTL
// This code is to aid in debugging parameter mismatches between the BFM and its corresponding agent.
// Enable this debug by setting UVM_VERBOSITY to UVM_DEBUG
// Setting UVM_VERBOSITY to UVM_DEBUG causes all BFM's and all agents to display their parameter settings.
// All of the messages from this feature have a UVM messaging id value of "CFG"
// The transcript or run.log can be parsed to ensure BFM parameter settings match its corresponding agents parameter settings.
import uvm_pkg::*;
`include "uvm_macros.svh"
initial begin : bfm_vs_agent_parameter_debug
  `uvm_info("CFG", 
      $psprintf("The BFM at '%m' has the following parameters: AHB_DATA_WIDTH=%x AHB_ADDR_WIDTH=%x BYPASS_HSEL=%x ", AHB_DATA_WIDTH,AHB_ADDR_WIDTH,BYPASS_HSEL),
      UVM_DEBUG)
end
`endif

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri rst_i;

  // Signal list (all signals are capable of being inputs and outputs for the sake
  // of supporting both INITIATOR and RESPONDER mode operation. Expectation is that 
  // directionality in the config file was from the point-of-view of the INITIATOR

  // INITIATOR mode input signals

  // INITIATOR mode output signals
  tri  aes_rst_i;
  reg  aes_rst_o = 'bz;
  tri [AHB_ADDR_WIDTH-1:0] hadrr_i;
  reg [AHB_ADDR_WIDTH-1:0] hadrr_o = 'bz;
  tri [AHB_DATA_WIDTH-1:0] hwdata_i;
  reg [AHB_DATA_WIDTH-1:0] hwdata_o = 'bz;
  tri  hsel_i;
  reg  hsel_o = 'bz;
  tri  hwrite_i;
  reg  hwrite_o = 'bz;
  tri  hmastlock_i;
  reg  hmastlock_o = 'bz;
  tri  hready_i;
  reg  hready_o = 'bz;
  tri [1:0] htrans_i;
  reg [1:0] htrans_o = 'bz;
  tri [3:0] hprot_i;
  reg [3:0] hprot_o = 'bz;
  tri [2:0] hburst_i;
  reg [2:0] hburst_o = 'bz;
  tri [2:0] hsize_i;
  reg [2:0] hsize_o = 'bz;
  tri  transaction_flag_in_monitor_i;
  reg  transaction_flag_in_monitor_o = 'bz;
  tri [1:0] op_i;
  reg [1:0] op_o = 'bz;
  tri [3:0] test_case_sel_i;
  reg [3:0] test_case_sel_o = 'bz;

  // Bi-directional signals
  

  assign clk_i = bus.clk;
  assign rst_i = bus.rst;

  // These are signals marked as 'input' by the config file, but the signals will be
  // driven by this BFM if put into RESPONDER mode (flipping all signal directions around)


  // These are signals marked as 'output' by the config file, but the outputs will
  // not be driven by this BFM unless placed in INITIATOR mode.
  assign bus.aes_rst = (initiator_responder == INITIATOR) ? (aes_rst_o && rst_i) : 'bz;
  assign aes_rst_i = bus.aes_rst;
  assign bus.hadrr = (initiator_responder == INITIATOR) ? hadrr_o : 'bz;
  assign hadrr_i = bus.hadrr;
  assign bus.hwdata = (initiator_responder == INITIATOR) ? hwdata_o : 'bz;
  assign hwdata_i = bus.hwdata;
  assign bus.hsel = (initiator_responder == INITIATOR) ? hsel_o : 'bz;
  assign hsel_i = bus.hsel;
  assign bus.hwrite = (initiator_responder == INITIATOR) ? hwrite_o : 'bz;
  assign hwrite_i = bus.hwrite;
  assign bus.hmastlock = (initiator_responder == INITIATOR) ? hmastlock_o : 'bz;
  assign hmastlock_i = bus.hmastlock;
  assign bus.hready = (initiator_responder == INITIATOR) ? hready_o : 'bz;
  assign hready_i = bus.hready;
  assign bus.htrans = (initiator_responder == INITIATOR) ? htrans_o : 'bz;
  assign htrans_i = bus.htrans;
  assign bus.hprot = (initiator_responder == INITIATOR) ? hprot_o : 'bz;
  assign hprot_i = bus.hprot;
  assign bus.hburst = (initiator_responder == INITIATOR) ? hburst_o : 'bz;
  assign hburst_i = bus.hburst;
  assign bus.hsize = (initiator_responder == INITIATOR) ? hsize_o : 'bz;
  assign hsize_i = bus.hsize;
  assign bus.transaction_flag_in_monitor = (initiator_responder == INITIATOR) ? transaction_flag_in_monitor_o : 'bz;
  assign transaction_flag_in_monitor_i = bus.transaction_flag_in_monitor;
  assign bus.op = (initiator_responder == INITIATOR) ? op_o : 'bz;
  assign op_i = bus.op;
  assign bus.test_case_sel = (initiator_responder == INITIATOR) ? test_case_sel_o : 'bz;
  assign test_case_sel_i = bus.test_case_sel;

  // Proxy handle to UVM driver
  AES_in_pkg::AES_in_driver #(
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .BYPASS_HSEL(BYPASS_HSEL)
    )
  proxy;
  // pragma tbx oneway proxy.my_function_name_in_uvm_driver                 

  // ****************************************************************************
  // **************************************************************************** 
  // Macros that define structs located in AES_in_macros.svh
  // ****************************************************************************
  // Struct for passing configuration data from AES_in_driver to this BFM
  // ****************************************************************************
  `AES_in_CONFIGURATION_STRUCT
  // ****************************************************************************
  // Structs for INITIATOR and RESPONDER data flow
  //*******************************************************************
  // Initiator macro used by AES_in_driver and AES_in_driver_bfm
  // to communicate initiator driven data to AES_in_driver_bfm.           
  `AES_in_INITIATOR_STRUCT
    AES_in_initiator_s initiator_struct;
  // Responder macro used by AES_in_driver and AES_in_driver_bfm
  // to communicate Responder driven data to AES_in_driver_bfm.
  `AES_in_RESPONDER_STRUCT
    AES_in_responder_s responder_struct;

  // ****************************************************************************
// pragma uvmf custom reset_condition_and_response begin
  // Always block used to return signals to reset value upon assertion of reset
  always @( negedge rst_i )
     begin
       // RESPONDER mode output signals
       // INITIATOR mode output signals
       aes_rst_o <= 'b0;
       hadrr_o <= 'Z;
       hwdata_o <= 'Z;
       hsel_o <= 0;
       hwrite_o <= 0;
       hmastlock_o <= 0;
       hready_o <= 0;
       htrans_o <= 0;
       hprot_o <= 0;
       hburst_o <= 0;
       hsize_o <= 3'b011;
       transaction_flag_in_monitor_o <= 0;
       op_o <= 'bZ;
       test_case_sel_o <= 'b0;
       // Bi-directional signals
 
     end    

// pragma uvmf custom reset_condition_and_response end

  // pragma uvmf custom interface_item_additional begin
  // pragma uvmf custom interface_item_additional end

  //******************************************************************
  // The configure() function is used to pass agent configuration
  // variables to the driver BFM.  It is called by the driver within
  // the agent at the beginning of the simulation.  It may be called 
  // during the simulation if agent configuration variables are updated
  // and the driver BFM needs to be aware of the new configuration 
  // variables.
  //

  function void configure(AES_in_configuration_s AES_in_configuration_arg); // pragma tbx xtf  
    initiator_responder = AES_in_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction                                                                             

// pragma uvmf custom initiate_and_get_response begin
// ****************************************************************************
// UVMF_CHANGE_ME
// This task is used by an initator.  The task first initiates a transfer then
// waits for the responder to complete the transfer.
    task initiate_and_get_response( 
       // This argument passes transaction variables used by an initiator
       // to perform the initial part of a protocol transfer.  The values
       // come from a sequence item created in a sequence.
       input AES_in_initiator_s AES_in_initiator_struct, 
       // This argument is used to send data received from the responder
       // back to the sequence item.  The sequence item is returned to the sequence.
       output AES_in_responder_s AES_in_responder_struct 
       );// pragma tbx xtf  
       // 
       // Members within the AES_in_initiator_struct:
       //   aes_in_op_transactions op ;
       //   bit [3:0] test_case_sel ;
       // Members within the AES_in_responder_struct:
       //   aes_in_op_transactions op ;
       //   bit [3:0] test_case_sel ;
       initiator_struct = AES_in_initiator_struct;
       //
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available initiator input and inout signals listed.
       //    Initiator input signals
       //    Initiator inout signals
       //    How to assign a signal from an initiator struct member named xyz.   
       //    All available initiator output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Initiator output signals
       //      aes_rst_o <= AES_in_initiator_struct.xyz;  //     
       //      hadrr_o <= AES_in_initiator_struct.xyz;  //    [AHB_ADDR_WIDTH-1:0] 
       //      hwdata_o <= AES_in_initiator_struct.xyz;  //    [AHB_DATA_WIDTH-1:0] 
       //      hsel_o <= AES_in_initiator_struct.xyz;  //     
       //      hwrite_o <= AES_in_initiator_struct.xyz;  //     
       //      hmastlock_o <= AES_in_initiator_struct.xyz;  //     
       //      hready_o <= AES_in_initiator_struct.xyz;  //     
       //      htrans_o <= AES_in_initiator_struct.xyz;  //    [1:0] 
       //      hprot_o <= AES_in_initiator_struct.xyz;  //    [3:0] 
       //      hburst_o <= AES_in_initiator_struct.xyz;  //    [2:0] 
       //      hsize_o <= AES_in_initiator_struct.xyz;  //    [2:0] 
       //      transaction_flag_in_monitor_o <= AES_in_initiator_struct.xyz;  //     
       //      op_o <= AES_in_initiator_struct.xyz;  //    [1:0] 
       //      test_case_sel_o <= AES_in_initiator_struct.xyz;  //    [3:0] 
       //    Initiator inout signals
    // Initiate a transfer using the data received.
    @(posedge clk_i);
    $display("aes_in_driver_bfm : Inside initiate_and_get_response");
    
    case (AES_in_initiator_struct.op)
      reset_op  : aes_init(AES_in_initiator_struct.op, AES_in_initiator_struct.test_case_sel);
      default   : cbc_mode_mmt_vector_test(AES_in_initiator_struct.op, AES_in_initiator_struct.test_case_sel);
    endcase

  endtask

  // ****************************************************************************
  // steven mod aes tb replica
  // ****************************************************************************

  parameter BASE_ADDR        = 32'h60000000;

  parameter ADDR_NAME0        = BASE_ADDR + 32'h00000000;
  parameter ADDR_NAME1        = BASE_ADDR + 32'h00000004;
  parameter ADDR_VERSION0     = BASE_ADDR + 32'h00000008;
  parameter ADDR_VERSION1     = BASE_ADDR + 32'h0000000c;

  parameter ADDR_CTRL        = BASE_ADDR + 32'h00000010;
  parameter ADDR_STATUS      = BASE_ADDR + 32'h00000018;
  parameter ADDR_CONFIG      = BASE_ADDR + 32'h00000020;

  parameter ADDR_KEY0        = BASE_ADDR + 32'h00000040;
  parameter ADDR_KEY1        = BASE_ADDR + 32'h00000044;
  parameter ADDR_KEY2        = BASE_ADDR + 32'h00000048;
  parameter ADDR_KEY3        = BASE_ADDR + 32'h0000004c;
  parameter ADDR_KEY4        = BASE_ADDR + 32'h00000050;
  parameter ADDR_KEY5        = BASE_ADDR + 32'h00000054;
  parameter ADDR_KEY6        = BASE_ADDR + 32'h00000058;
  parameter ADDR_KEY7        = BASE_ADDR + 32'h0000005c;

  parameter ADDR_BLOCK0      = BASE_ADDR + 32'h00000080;
  parameter ADDR_BLOCK1      = BASE_ADDR + 32'h00000084;
  parameter ADDR_BLOCK2      = BASE_ADDR + 32'h00000088;
  parameter ADDR_BLOCK3      = BASE_ADDR + 32'h0000008c;

  parameter ADDR_RESULT0     = BASE_ADDR + 32'h00000100;
  parameter ADDR_RESULT1     = BASE_ADDR + 32'h00000104;
  parameter ADDR_RESULT2     = BASE_ADDR + 32'h00000108;
  parameter ADDR_RESULT3     = BASE_ADDR + 32'h0000010c;

  parameter ADDR_IV0         = BASE_ADDR + 32'h00000110;
  parameter ADDR_IV1         = BASE_ADDR + 32'h00000114;
  parameter ADDR_IV2         = BASE_ADDR + 32'h00000118;
  parameter ADDR_IV3         = BASE_ADDR + 32'h0000011c;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  parameter AES_128_BIT_KEY = 0;
  parameter AES_256_BIT_KEY = 1;


  reg [31 : 0]  read_data;
  reg [127 : 0] result_data;

  task do_assert_rst();
    begin
      aes_rst_o = 0;
      transaction_flag_in_monitor_o = 0;
      repeat (5) @(posedge clk_i);
      aes_rst_o = 1;
    end
  endtask // reset_dut

  task aes_init(input aes_in_op_transactions op,
                input bit [3:0] test_case_sel);
  $display("%d ***************   Starting Reset", $time);
    op_o = op;
    test_case_sel_o = 0;
    aes_rst_o <= 1'b0;
    transaction_flag_in_monitor_o = 0;

    hadrr_o     = 'Z;
    hwdata_o    = 'Z;
    hsel_o      = 0;
    hwrite_o    = 0;
    hmastlock_o = 0;
    hready_o    = 0;
    htrans_o    = AHB_HTRANS_IDLE;
    hprot_o     = 0;
    hburst_o    = 0;
    hsize_o     = 3'b011;

    repeat (10) @(posedge clk_i);
    aes_rst_o <= 1'b1;
    repeat (5) @(posedge clk_i);

  $display("%d ***************   Ending Reset", $time);
  endtask

  task write_IV(input [127 : 0] IV);
    begin
      write_single_word(ADDR_IV0, IV[127  :  96]);
      write_single_word(ADDR_IV1, IV[95   :  64]);
      write_single_word(ADDR_IV2, IV[63   :  32]);
      write_single_word(ADDR_IV3, IV[31   :   0]);
    end
  endtask // write_IV

  // reset other signals
  always @ (negedge rst_i)
  begin
    aes_rst_o   = 0;
    hadrr_o     = 'Z;
    hwdata_o    = 'Z;
    hsel_o      = 0;
    hwrite_o    = 0;
    hmastlock_o = 0;
    hready_o    = 0;
    htrans_o    = AHB_HTRANS_IDLE;
    hprot_o     = 0;
    hburst_o    = 0;
    hsize_o     = 3'b011;
  end

  always @ (posedge rst_i)
  begin
    aes_rst_o = 1;
  end

  task write_single_word(input [31 : 0]  address,
                    input [31 : 0] word);
    begin
      hsel_o       = 1;
      hadrr_o      = address;
      hwrite_o     = 1;
      hmastlock_o  = 0;
      hready_o     = 1;
      htrans_o     = AHB_HTRANS_NONSEQ;
      hprot_o      = 0;
      hburst_o     = 0;
      hsize_o      = 3'b010;
      @(posedge clk_i);

      hadrr_o      = 'Z;
      hwdata_o     = word;
      hwrite_o     = 0;
      htrans_o     = AHB_HTRANS_IDLE;
    end
  endtask // write_single_word

  task write_block(input [127 : 0] block);
    begin
      write_single_word(ADDR_BLOCK0, block[127  :  96]);
      write_single_word(ADDR_BLOCK1, block[95   :  64]);
      write_single_word(ADDR_BLOCK2, block[63   :  32]);
      write_single_word(ADDR_BLOCK3, block[31   :   0]);
    end
  endtask // write_block

  task read_single_word_driverbfm(input [31 : 0]  address);
    begin
      hsel_o       = 1;
      hadrr_o      = address;
      hwrite_o     = 0;
      hmastlock_o  = 0;
      hready_o     = 1;
      htrans_o     = AHB_HTRANS_NONSEQ;
      hprot_o      = 0;
      hburst_o     = 0;
      hsize_o      = 3'b010;
      @(posedge clk_i);
      
      hwdata_o     = 0;

    end
  endtask // read_single_word_driverbfm

  task read_result;
    begin
      read_single_word_driverbfm(ADDR_RESULT0);
      read_single_word_driverbfm(ADDR_RESULT1);
      read_single_word_driverbfm(ADDR_RESULT2);
      read_single_word_driverbfm(ADDR_RESULT3);
    end
  endtask // read_result

  task init_key(input [255 : 0] key, input key_length);
    begin
      write_single_word(ADDR_KEY0, key[255  : 224]);
      write_single_word(ADDR_KEY1, key[223  : 192]);
      write_single_word(ADDR_KEY2, key[191  : 160]);
      write_single_word(ADDR_KEY3, key[159  : 128]);
      write_single_word(ADDR_KEY4, key[127  :  96]);
      write_single_word(ADDR_KEY5, key[95   :  64]);
      write_single_word(ADDR_KEY6, key[63   :  32]);
      write_single_word(ADDR_KEY7, key[31   :   0]);

      if (key_length)
          write_single_word(ADDR_CONFIG, 8'h02);
      else
          write_single_word(ADDR_CONFIG, 8'h00);

      write_single_word(ADDR_CTRL, 8'h01);
      
      @(posedge clk_i);
      hsel_o       = 0;

      repeat (100) @(posedge clk_i);

    end
  endtask // init_key

task cbc_mode_mmt_vector_test(input aes_in_op_transactions op,
                                  input bit [3:0] test_case_sel);
    
    reg [255 : 0] key;
    reg [127 : 0] IV;
    reg [127 : 0] block;
    reg [127 : 0] expected;
    reg [1279: 0] block_all;
    reg [1279: 0] expected_all;
    reg key_length;

    int line_skip;
    int cnt_tmp;
    int cyc_cnt;
    int fd_r;

    string        line_read;
    string        tmp_str1;
    string        tmp_str2;

    begin

      // limit the selection range from 0-9
      $display("***************   test_case_sel value is: ", test_case_sel);
      if (test_case_sel > 9) test_case_sel = 9;

      // initialisation
      key_length = AES_256_BIT_KEY;
      line_skip = test_case_sel * 6 + 5;
      if (op == 2'b10) line_skip = line_skip + 62;
      cnt_tmp = 0;
      cyc_cnt = 0;

      // pass the operation mode and selection to monitor
      transaction_flag_in_monitor_o = 1'b0;
      op_o = op;
      test_case_sel_o = test_case_sel;

      // for some reason, $fopen only recognizes the absolute path
      // change it to your path before running!!
      fd_r = $fopen("/home/t-stevenlian/AHA_workspaces/aes_vector/Caliptra/src/aes/tb/CBCMMT256_clean.txt","r");
      if(fd_r) $display("file opened successfully!");

      while (cnt_tmp < line_skip) begin
        cnt_tmp = cnt_tmp + 1;
        $fgets(line_read,fd_r);
      end

      // gets key, IV, and block text
      $display("*** Getting key");
      $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, key);
      $fgets(line_read,fd_r);
      $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, IV);
      $fgets(line_read,fd_r);
      $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, block_all);
      $fgets(line_read,fd_r);
      // $display("*** driver key is: %h", key);
      // $display("*** driver IV is: %h", IV);
      // $display("*** driver block_all is: %h", block_all);

      // shift the block text
      block_all = block_all << (9 - test_case_sel) * 128;
      // $display("block_all = %h", block_all);

      $display("*** AES test started");
      
      // initialize key and write IV in
      init_key(key, key_length);
      write_IV(IV);

      while (cyc_cnt <= test_case_sel) begin

        block = block_all[1279:1152];
        block_all = block_all << 128;

        // write block
        write_block(block);

        write_single_word(ADDR_CONFIG, (8'h00 + (key_length << 1)+ op[0]));
        write_single_word(ADDR_CTRL, 8'h02);
        
        @(posedge clk_i);
        hsel_o       = 0;

        // wait and read out result for monitor bfm
        repeat (100) begin
          @(posedge clk_i);
          read_single_word_driverbfm(ADDR_STATUS);
        end

        @(posedge clk_i);
        read_result();
        @(posedge clk_i);

        cyc_cnt = cyc_cnt + 1;

      end 

      // indicate that this cycle is done
      transaction_flag_in_monitor_o = 1'b1;
      repeat(10) @(posedge clk_i);
      transaction_flag_in_monitor_o = 1'b0;
      @(posedge clk_i);
      // tests done

    end
  endtask // cbc_mode_mmt_vector_test

// ****************************************************************************
// end of steven's mod
// ****************************************************************************

// pragma uvmf custom initiate_and_get_response end

// pragma uvmf custom respond_and_wait_for_next_transfer begin
// ****************************************************************************
// The first_transfer variable is used to prevent completing a transfer in the 
// first call to this task.  For the first call to this task, there is not
// current transfer to complete.
bit first_transfer=1;

// UVMF_CHANGE_ME
// This task is used by a responder.  The task first completes the current 
// transfer in progress then waits for the initiator to start the next transfer.
  task respond_and_wait_for_next_transfer( 
       // This argument is used to send data received from the initiator
       // back to the sequence item.  The sequence determines how to respond.
       output AES_in_initiator_s AES_in_initiator_struct, 
       // This argument passes transaction variables used by a responder
       // to complete a protocol transfer.  The values come from a sequence item.       
       input AES_in_responder_s AES_in_responder_struct 
       );// pragma tbx xtf   
  // Variables within the AES_in_initiator_struct:
  //   aes_in_op_transactions op ;
  //   bit [3:0] test_case_sel ;
  // Variables within the AES_in_responder_struct:
  //   aes_in_op_transactions op ;
  //   bit [3:0] test_case_sel ;
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available responder input and inout signals listed.
       //    Responder input signals
       //      AES_in_responder_struct.xyz = aes_rst_i;  //     
       //      AES_in_responder_struct.xyz = hadrr_i;  //    [AHB_ADDR_WIDTH-1:0] 
       //      AES_in_responder_struct.xyz = hwdata_i;  //    [AHB_DATA_WIDTH-1:0] 
       //      AES_in_responder_struct.xyz = hsel_i;  //     
       //      AES_in_responder_struct.xyz = hwrite_i;  //     
       //      AES_in_responder_struct.xyz = hmastlock_i;  //     
       //      AES_in_responder_struct.xyz = hready_i;  //     
       //      AES_in_responder_struct.xyz = htrans_i;  //    [1:0] 
       //      AES_in_responder_struct.xyz = hprot_i;  //    [3:0] 
       //      AES_in_responder_struct.xyz = hburst_i;  //    [2:0] 
       //      AES_in_responder_struct.xyz = hsize_i;  //    [2:0] 
       //      AES_in_responder_struct.xyz = transaction_flag_in_monitor_i;  //     
       //      AES_in_responder_struct.xyz = op_i;  //    [1:0] 
       //      AES_in_responder_struct.xyz = test_case_sel_i;  //    [3:0] 
       //    Responder inout signals
       //    How to assign a signal, named xyz, from an initiator struct member.   
       //    All available responder output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Responder output signals
       //    Responder inout signals
    
  @(posedge clk_i);
  if (!first_transfer) begin
    // Perform transfer response here.   
    // Reply using data recieved in the AES_in_responder_struct.
    @(posedge clk_i);
    // Reply using data recieved in the transaction handle.
    @(posedge clk_i);
  end
    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the AES_in_initiator_struct.
    @(posedge clk_i);
    @(posedge clk_i);
    first_transfer = 0;
  endtask
// pragma uvmf custom respond_and_wait_for_next_transfer end

 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

