//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
//    This interface performs the SHA512_in signal driving.  It is
//     accessed by the uvm SHA512_in driver through a virtual interface
//     handle in the SHA512_in configuration.  It drives the singals passed
//     in through the port connection named bus of type SHA512_in_if.
//
//     Input signals from the SHA512_in_if are assigned to an internal input
//     signal with a _i suffix.  The _i signal should be used for sampling.
//
//     The input signal connections are as follows:
//       bus.signal -> signal_i 
//
//     This bfm drives signals with a _o suffix.  These signals
//     are driven onto signals within SHA512_in_if based on INITIATOR/RESPONDER and/or
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
import SHA512_in_pkg_hdl::*;
`include "src/SHA512_in_macros.svh"

interface SHA512_in_driver_bfm #(
  int AHB_DATA_WIDTH = 32,
  int AHB_ADDR_WIDTH = 32,
  bit BYPASS_HSEL = 0
  )

  (SHA512_in_if bus);
  // The following pragma and additional ones in-lined further below are for running this BFM on Veloce
  // pragma attribute SHA512_in_driver_bfm partition_interface_xif

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
  tri  sha512_rst_i;
  reg  sha512_rst_o = 'bz;
  tri [AHB_ADDR_WIDTH-1:0] hadrr_i;
  reg [AHB_ADDR_WIDTH-1:0] hadrr_o = 'bz;
  tri [AHB_DATA_WIDTH-1:0] hwdata_i;
  reg [AHB_DATA_WIDTH-1:0] hwdata_o = 'bz;
  tri  hsel_i;
  reg  hsel_o = 'bz;
  tri  hwrite_i;
  reg  hwrite_o = 'bz;
  tri  hready_i;
  reg  hready_o = 'bz;
  tri [1:0] htrans_i;
  reg [1:0] htrans_o = 'bz;
  tri [2:0] hsize_i;
  reg [2:0] hsize_o = 'bz;
  tri  transaction_flag_in_monitor_i;
  reg  transaction_flag_in_monitor_o = 'bz;
  tri [2:0] op_i;
  reg [2:0] op_o = 'bz;
  tri [7:0] test_case_sel_i;
  reg [7:0] test_case_sel_o = 'bz;

  // Bi-directional signals
  

  assign clk_i = bus.clk;
  assign rst_i = bus.rst;

  // These are signals marked as 'input' by the config file, but the signals will be
  // driven by this BFM if put into RESPONDER mode (flipping all signal directions around)


  // These are signals marked as 'output' by the config file, but the outputs will
  // not be driven by this BFM unless placed in INITIATOR mode.
  assign bus.sha512_rst = (initiator_responder == INITIATOR) ? (sha512_rst_o && rst_i) : 'bz;
  assign sha512_rst_i = bus.sha512_rst;
  assign bus.hadrr = (initiator_responder == INITIATOR) ? hadrr_o : 'bz;
  assign hadrr_i = bus.hadrr;
  assign bus.hwdata = (initiator_responder == INITIATOR) ? hwdata_o : 'bz;
  assign hwdata_i = bus.hwdata;
  assign bus.hsel = (initiator_responder == INITIATOR) ? hsel_o : 'bz;
  assign hsel_i = bus.hsel;
  assign bus.hwrite = (initiator_responder == INITIATOR) ? hwrite_o : 'bz;
  assign hwrite_i = bus.hwrite;
  assign bus.hready = (initiator_responder == INITIATOR) ? hready_o : 'bz;
  assign hready_i = bus.hready;
  assign bus.htrans = (initiator_responder == INITIATOR) ? htrans_o : 'bz;
  assign htrans_i = bus.htrans;
  assign bus.hsize = (initiator_responder == INITIATOR) ? hsize_o : 'bz;
  assign hsize_i = bus.hsize;
  assign bus.transaction_flag_in_monitor = (initiator_responder == INITIATOR) ? transaction_flag_in_monitor_o : 'bz;
  assign transaction_flag_in_monitor_i = bus.transaction_flag_in_monitor;
  assign bus.op = (initiator_responder == INITIATOR) ? op_o : 'bz;
  assign op_i = bus.op;
  assign bus.test_case_sel = (initiator_responder == INITIATOR) ? test_case_sel_o : 'bz;
  assign test_case_sel_i = bus.test_case_sel;

  // Proxy handle to UVM driver
  SHA512_in_pkg::SHA512_in_driver #(
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .BYPASS_HSEL(BYPASS_HSEL)
    )
  proxy;
  // pragma tbx oneway proxy.my_function_name_in_uvm_driver                 

  // ****************************************************************************
  // **************************************************************************** 
  // Macros that define structs located in SHA512_in_macros.svh
  // ****************************************************************************
  // Struct for passing configuration data from SHA512_in_driver to this BFM
  // ****************************************************************************
  `SHA512_in_CONFIGURATION_STRUCT
  // ****************************************************************************
  // Structs for INITIATOR and RESPONDER data flow
  //*******************************************************************
  // Initiator macro used by SHA512_in_driver and SHA512_in_driver_bfm
  // to communicate initiator driven data to SHA512_in_driver_bfm.           
  `SHA512_in_INITIATOR_STRUCT
    SHA512_in_initiator_s initiator_struct;
  // Responder macro used by SHA512_in_driver and SHA512_in_driver_bfm
  // to communicate Responder driven data to SHA512_in_driver_bfm.
  `SHA512_in_RESPONDER_STRUCT
    SHA512_in_responder_s responder_struct;

  // ****************************************************************************
// pragma uvmf custom reset_condition_and_response begin
  // Always block used to return signals to reset value upon assertion of reset
  always @( negedge rst_i )
     begin
       // RESPONDER mode output signals
       // INITIATOR mode output signals
      sha512_rst_o <= 'b0;
      hadrr_o <= 0;
      hwdata_o <= 0;
      hsel_o <= 0;
      hwrite_o <= 0;
      hready_o <= 0;
      htrans_o <= 0;
      hsize_o <= 3'b011;
      transaction_flag_in_monitor_o <= 0;
      op_o <= 'bz;
      test_case_sel_o <= 0;
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

  function void configure(SHA512_in_configuration_s SHA512_in_configuration_arg); // pragma tbx xtf  
    initiator_responder = SHA512_in_configuration_arg.initiator_responder;
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
       input SHA512_in_initiator_s SHA512_in_initiator_struct, 
       // This argument is used to send data received from the responder
       // back to the sequence item.  The sequence item is returned to the sequence.
       output SHA512_in_responder_s SHA512_in_responder_struct 
       );// pragma tbx xtf  
       // 
       // Members within the SHA512_in_initiator_struct:
       //   sha512_in_op_transactions op ;
       //   bit [7:0] test_case_sel ;
       // Members within the SHA512_in_responder_struct:
       //   sha512_in_op_transactions op ;
       //   bit [7:0] test_case_sel ;
       initiator_struct = SHA512_in_initiator_struct;
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
       //      sha512_rst_o <= SHA512_in_initiator_struct.xyz;  //     
       //      hadrr_o <= SHA512_in_initiator_struct.xyz;  //    [AHB_ADDR_WIDTH-1:0] 
       //      hwdata_o <= SHA512_in_initiator_struct.xyz;  //    [AHB_DATA_WIDTH-1:0] 
       //      hsel_o <= SHA512_in_initiator_struct.xyz;  //     
       //      hwrite_o <= SHA512_in_initiator_struct.xyz;  //     
       //      hready_o <= SHA512_in_initiator_struct.xyz;  //     
       //      htrans_o <= SHA512_in_initiator_struct.xyz;  //    [1:0] 
       //      hsize_o <= SHA512_in_initiator_struct.xyz;  //    [2:0] 
       //      transaction_flag_in_monitor_o <= SHA512_in_initiator_struct.xyz;  //     
       //      op_o <= SHA512_in_initiator_struct.xyz;  //    [2:0] 
       //      test_case_sel_o <= SHA512_in_initiator_struct.xyz;  //    [7:0] 
       //    Initiator inout signals
    // Initiate a transfer using the data received.
       @(posedge clk_i);
       
       case (SHA512_in_initiator_struct.op)
         reset_op  : sha512_init(SHA512_in_initiator_struct.op, SHA512_in_initiator_struct.test_case_sel);
         default   : sha512_testbench(SHA512_in_initiator_struct.op, SHA512_in_initiator_struct.test_case_sel);
       endcase

  endtask        

// ****************************************************************************
  // steven mod sha512 tb replica
  // ****************************************************************************

  parameter BASE_ADDR            = 32'h40000000;

  parameter ADDR_CTRL            = BASE_ADDR + 32'h00000010;
  parameter CTRL_INIT_BIT        = 0;
  parameter CTRL_NEXT_BIT        = 1;
  parameter CTRL_MODE_LOW_BIT    = 2;
  parameter CTRL_MODE_HIGH_BIT   = 3;
  parameter CTRL_WORK_FACTOR_BIT = 7;

  parameter ADDR_STATUS          = BASE_ADDR + 32'h00000018;
  parameter STATUS_READY_BIT     = 0;
  parameter STATUS_VALID_BIT     = 1;

  parameter ADDR_WORK_FACTOR_NUM = BASE_ADDR + 32'h00000020;

  parameter ADDR_BLOCK0          = BASE_ADDR + 32'h00000080;
  parameter ADDR_BLOCK1          = BASE_ADDR + 32'h00000084;
  parameter ADDR_BLOCK2          = BASE_ADDR + 32'h00000088;
  parameter ADDR_BLOCK3          = BASE_ADDR + 32'h0000008c;
  parameter ADDR_BLOCK4          = BASE_ADDR + 32'h00000090;
  parameter ADDR_BLOCK5          = BASE_ADDR + 32'h00000094;
  parameter ADDR_BLOCK6          = BASE_ADDR + 32'h00000098;
  parameter ADDR_BLOCK7          = BASE_ADDR + 32'h0000009c;
  parameter ADDR_BLOCK8          = BASE_ADDR + 32'h000000a0;
  parameter ADDR_BLOCK9          = BASE_ADDR + 32'h000000a4;
  parameter ADDR_BLOCK10         = BASE_ADDR + 32'h000000a8;
  parameter ADDR_BLOCK11         = BASE_ADDR + 32'h000000ac;
  parameter ADDR_BLOCK12         = BASE_ADDR + 32'h000000b0;
  parameter ADDR_BLOCK13         = BASE_ADDR + 32'h000000b4;
  parameter ADDR_BLOCK14         = BASE_ADDR + 32'h000000b8;
  parameter ADDR_BLOCK15         = BASE_ADDR + 32'h000000bc;
  parameter ADDR_BLOCK16         = BASE_ADDR + 32'h000000c0;
  parameter ADDR_BLOCK17         = BASE_ADDR + 32'h000000c4;
  parameter ADDR_BLOCK18         = BASE_ADDR + 32'h000000c8;
  parameter ADDR_BLOCK19         = BASE_ADDR + 32'h000000cc;
  parameter ADDR_BLOCK20         = BASE_ADDR + 32'h000000d0;
  parameter ADDR_BLOCK21         = BASE_ADDR + 32'h000000d4;
  parameter ADDR_BLOCK22         = BASE_ADDR + 32'h000000d8;
  parameter ADDR_BLOCK23         = BASE_ADDR + 32'h000000dc;
  parameter ADDR_BLOCK24         = BASE_ADDR + 32'h000000e0;
  parameter ADDR_BLOCK25         = BASE_ADDR + 32'h000000e4;
  parameter ADDR_BLOCK26         = BASE_ADDR + 32'h000000e8;
  parameter ADDR_BLOCK27         = BASE_ADDR + 32'h000000ec;
  parameter ADDR_BLOCK28         = BASE_ADDR + 32'h000000f0;
  parameter ADDR_BLOCK29         = BASE_ADDR + 32'h000000f4;
  parameter ADDR_BLOCK30         = BASE_ADDR + 32'h000000f8;
  parameter ADDR_BLOCK31         = BASE_ADDR + 32'h000000fc;

  parameter ADDR_DIGEST0         = BASE_ADDR + 32'h00000100;
  parameter ADDR_DIGEST1         = BASE_ADDR + 32'h00000104;
  parameter ADDR_DIGEST2         = BASE_ADDR + 32'h00000108;
  parameter ADDR_DIGEST3         = BASE_ADDR + 32'h0000010c;
  parameter ADDR_DIGEST4         = BASE_ADDR + 32'h00000110;
  parameter ADDR_DIGEST5         = BASE_ADDR + 32'h00000114;
  parameter ADDR_DIGEST6         = BASE_ADDR + 32'h00000118;
  parameter ADDR_DIGEST7         = BASE_ADDR + 32'h0000011c;
  parameter ADDR_DIGEST8         = BASE_ADDR + 32'h00000120;
  parameter ADDR_DIGEST9         = BASE_ADDR + 32'h00000124;
  parameter ADDR_DIGEST10        = BASE_ADDR + 32'h00000128;
  parameter ADDR_DIGEST11        = BASE_ADDR + 32'h0000012c;
  parameter ADDR_DIGEST12        = BASE_ADDR + 32'h00000130;
  parameter ADDR_DIGEST13        = BASE_ADDR + 32'h00000134;
  parameter ADDR_DIGEST14        = BASE_ADDR + 32'h00000138;
  parameter ADDR_DIGEST15        = BASE_ADDR + 32'h0000013c;

  parameter MODE_SHA_512_224     = 2'h0;
  parameter MODE_SHA_512_256     = 2'h1;
  parameter MODE_SHA_384         = 2'h2;
  parameter MODE_SHA_512         = 2'h3;

  parameter CTRL_INIT_VALUE      = 2'h1;
  parameter CTRL_NEXT_VALUE      = 2'h2;

  parameter AHB_HTRANS_IDLE      = 0;
  parameter AHB_HTRANS_BUSY      = 1;
  parameter AHB_HTRANS_NONSEQ    = 2;
  parameter AHB_HTRANS_SEQ       = 3;

  int clock_cnt = 0;

  always@(posedge clk_i) clock_cnt = clock_cnt + 1;

  task sha512_init(input sha512_in_op_transactions op,
    input bit [7:0] test_case_sel);
    begin
      op_o = op;
      test_case_sel_o = 0;
      sha512_rst_o <= 1'b0;
      transaction_flag_in_monitor_o = 0;

      hadrr_o      = 0;
      hwdata_o     = 0;
      hsel_o       = 0;
      hwrite_o     = 0;
      hready_o     = 0;
      htrans_o     = AHB_HTRANS_IDLE;
      hsize_o      = 3'b011;

      repeat (10) @(posedge clk_i);
      sha512_rst_o <= 1'b1;
      repeat (5) @(posedge clk_i);
    end
  endtask 

  // raise the reset for DUT
  always @ (posedge rst_i)
  begin
    sha512_rst_o = 1;
  end

  task write_single_word(input [31 : 0]  address,
                    input [31 : 0] word);
    begin
      hsel_o       = 1;
      hadrr_o      = address;
      hwrite_o     = 1;
      hready_o     = 1;
      htrans_o     = AHB_HTRANS_NONSEQ;
      hsize_o      = 3'b010;
      @(posedge clk_i);

      hadrr_o      = 'Z;
      hwdata_o     = word;
      hwrite_o     = 0;
      htrans_o     = AHB_HTRANS_IDLE;
    end
  endtask // write_single_word

  task read_single_word_driverbfm(input [31 : 0]  address);
    begin
      hsel_o       = 1;
      hadrr_o      = address;
      hwrite_o     = 0;
      hready_o     = 1;
      htrans_o     = AHB_HTRANS_NONSEQ;
      hsize_o      = 3'b010;
      @(posedge clk_i);
      
      hwdata_o     = 0;

    end
  endtask // read_single_word_driverbfm

  task write_block(input [1023 : 0] block);
    begin
      write_single_word(ADDR_BLOCK0,  block[1023 : 992]);
      write_single_word(ADDR_BLOCK1,  block[991  : 960]);
      write_single_word(ADDR_BLOCK2,  block[959  : 928]);
      write_single_word(ADDR_BLOCK3,  block[927  : 896]);
      write_single_word(ADDR_BLOCK4,  block[895  : 864]);
      write_single_word(ADDR_BLOCK5,  block[863  : 832]);
      write_single_word(ADDR_BLOCK6,  block[831  : 800]);
      write_single_word(ADDR_BLOCK7,  block[799  : 768]);
      write_single_word(ADDR_BLOCK8,  block[767  : 736]);
      write_single_word(ADDR_BLOCK9,  block[735  : 704]);
      write_single_word(ADDR_BLOCK10, block[703  : 672]);
      write_single_word(ADDR_BLOCK11, block[671  : 640]);
      write_single_word(ADDR_BLOCK12, block[639  : 608]);
      write_single_word(ADDR_BLOCK13, block[607  : 576]);
      write_single_word(ADDR_BLOCK14, block[575  : 544]);
      write_single_word(ADDR_BLOCK15, block[543  : 512]);
      write_single_word(ADDR_BLOCK16, block[511  : 480]);
      write_single_word(ADDR_BLOCK17, block[479  : 448]);
      write_single_word(ADDR_BLOCK18, block[447  : 416]);
      write_single_word(ADDR_BLOCK19, block[415  : 384]);
      write_single_word(ADDR_BLOCK20, block[383  : 352]);
      write_single_word(ADDR_BLOCK21, block[351  : 320]);
      write_single_word(ADDR_BLOCK22, block[319  : 288]);
      write_single_word(ADDR_BLOCK23, block[287  : 256]);
      write_single_word(ADDR_BLOCK24, block[255  : 224]);
      write_single_word(ADDR_BLOCK25, block[223  : 192]);
      write_single_word(ADDR_BLOCK26, block[191  : 160]);
      write_single_word(ADDR_BLOCK27, block[159  : 128]);
      write_single_word(ADDR_BLOCK28, block[127  :  96]);
      write_single_word(ADDR_BLOCK29, block[95   :  64]);
      write_single_word(ADDR_BLOCK30, block[63   :  32]);
      write_single_word(ADDR_BLOCK31, block[31   :   0]);
    end
  endtask // write_block

  task read_digest_bfm;
    begin
      read_single_word_driverbfm(ADDR_DIGEST0);
      read_single_word_driverbfm(ADDR_DIGEST1);
      read_single_word_driverbfm(ADDR_DIGEST2);
      read_single_word_driverbfm(ADDR_DIGEST3);
      read_single_word_driverbfm(ADDR_DIGEST4);
      read_single_word_driverbfm(ADDR_DIGEST5);
      read_single_word_driverbfm(ADDR_DIGEST6);
      read_single_word_driverbfm(ADDR_DIGEST7);
      read_single_word_driverbfm(ADDR_DIGEST8);
      read_single_word_driverbfm(ADDR_DIGEST9);
      read_single_word_driverbfm(ADDR_DIGEST10);
      read_single_word_driverbfm(ADDR_DIGEST11);
      read_single_word_driverbfm(ADDR_DIGEST12);
      read_single_word_driverbfm(ADDR_DIGEST13);
      read_single_word_driverbfm(ADDR_DIGEST14);
      read_single_word_driverbfm(ADDR_DIGEST15);
    end
  endtask // read_digest_bfm

  task sha512_testbench(input sha512_in_op_transactions op,
                                  input bit [7:0] test_case_sel);
    
    // reg [1:0]     mode;
    reg [1:0]     ctrl_value;
    reg [1023: 0] block;
    reg [1023: 0] block_last;
    reg [102399: 0] block_all;

    int cnt_tmp;
    int line_skip;
    int block_len;
    int block_len_res;
    int block_shift;
    int block_shift_cnt;
    int fd_r;

    string line_read;
    string tmp_str1;
    string tmp_str2;
    string file_name;

    begin

      // pass the operation mode and selection to monitor
      transaction_flag_in_monitor_o = 1'b0;
      op_o = op;
      test_case_sel_o = test_case_sel;
      $display(" **SHA512_in_driver_bfm** clock count value is: ", clock_cnt);
      $display(" **SHA512_in_driver_bfm** op value is: ", op);
      $display(" **SHA512_in_driver_bfm** test_case_sel value is: ", test_case_sel);
      
      // initialisation
      cnt_tmp = 0;
      block_shift_cnt = 0;

      case(op[1:0])
        MODE_SHA_512_224: begin
          // mode = MODE_SHA_512_224;
          case(test_case_sel) inside
            [0:127]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA512_224ShortMsg.rsp";
              line_skip = test_case_sel * 4 + 7;
            end
            [128:255]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA512_224LongMsg.rsp";
              line_skip = (test_case_sel - 128) * 4 + 7;
            end
          endcase
        end
        MODE_SHA_512_256: begin
          // mode = MODE_SHA_512_256;
          case(test_case_sel) inside
            [0:127]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA512_256ShortMsg.rsp";
              line_skip = test_case_sel * 4 + 7;
            end
            [128:255]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA512_256LongMsg.rsp";
              line_skip = (test_case_sel - 128) * 4 + 7;
            end
          endcase
        end
        MODE_SHA_384:     begin
          // mode = MODE_SHA_384;
          case(test_case_sel) inside
            [0:127]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA384ShortMsg.rsp";
              line_skip = test_case_sel * 4 + 7;
            end
            [128:255]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA384LongMsg.rsp";
              line_skip = (test_case_sel - 128) * 4 + 7;
            end
          endcase
        end
        MODE_SHA_512:     begin
          // mode = MODE_SHA_512;
          case(test_case_sel) inside
            [0:127]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA512ShortMsg.rsp";
              line_skip = test_case_sel * 4 + 7;
            end
            [128:255]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA512LongMsg.rsp";
              line_skip = (test_case_sel - 128) * 4 + 7;
            end
          endcase
        end
      endcase

      fd_r = $fopen(file_name,"r");
      $display(" **SHA512_in_driver_bfm** clock count value is: ", clock_cnt);
      if(fd_r) $display("**SHA512_in_driver_bfm** file opened successfully!");

      while (cnt_tmp <= line_skip) begin
        cnt_tmp = cnt_tmp + 1;
        $fgets(line_read,fd_r);
      end

      // get the block and its length
      $display("**SHA512_in_driver_bfm** Getting block length");
      $sscanf( line_read, "%s %s %d", tmp_str1, tmp_str2, block_len);
      $fgets(line_read,fd_r);
      $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, block_all);
      
      // shift the block text
      block_all = block_all << (102400 - block_len);
      // $display("**SHA512_in_driver_bfm** block_all = %h", block_all);
      $display(" **SHA512_in_driver_bfm** clock count value is: ", clock_cnt);
      $display("**SHA512_in_driver_bfm** block_len is: %h", block_len);

      $display(" **SHA512_in_driver_bfm** clock count value is: ", clock_cnt);
      $display("**SHA512_in_driver_bfm** SHA512 test started");
      block_shift = block_len / 1024;
      block_len_res = block_len % 1024;
      block_len_res = 1024 - block_len_res - 1;
      block_shift_cnt = 0;
      block_last = 0;
      ctrl_value = 0;

      while (block_shift_cnt <= block_shift) begin

        block_shift_cnt = block_shift_cnt + 1;

        block = block_all[102399:101376];
        block_all = block_all << 1024;

        // check the last 1024 bit, add padding and block length
        if (block_shift_cnt == block_shift + 1) begin
          if (block_len_res > 128) block_last = block + (1024'h1 << block_len_res) + block_len;
          else begin
            if (block_last == 0) begin
              block_last = block + (1024'h1 << block_len_res);
              block_shift_cnt = block_shift_cnt - 1;
            end
            else block_last = block_len;
          end

          block = block_last;
        end

        $display(" **SHA512_in_driver_bfm** clock count value is: ", clock_cnt);
        $display("**SHA512_in_driver_bfm** block is: %h", block);
        
        // write block
        write_block(block);
        @(posedge clk_i);
        // repeat (50) begin
        //   @(posedge clk_i);
        //   read_single_word_driverbfm(ADDR_STATUS);
        // end
        
        if (ctrl_value == 0) ctrl_value = CTRL_INIT_VALUE;
        else ctrl_value = CTRL_NEXT_VALUE;
        $display(" **SHA512_in_driver_bfm** clock count value is: ", clock_cnt);
        $display("**SHA512_in_driver_bfm** ctrl_value is: %h", ctrl_value);
        write_single_word(ADDR_CTRL, {28'h0, op[1:0], ctrl_value});

        @(posedge clk_i);
        hsel_o       = 0;

        repeat (50) begin
          @(posedge clk_i);
          read_single_word_driverbfm(ADDR_STATUS);
        end

      end

      @(posedge clk_i);
      // give signal to monitors that ready to read
      transaction_flag_in_monitor_o = 1'b1; 
      repeat(op[1:0]) @(posedge clk_i);
      transaction_flag_in_monitor_o = 1'b0;
      @(posedge clk_i);
      read_digest_bfm();
      @(posedge clk_i);

    end
  endtask // double_block_test

  // ****************************************************************************
  // steven mod ends
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
       output SHA512_in_initiator_s SHA512_in_initiator_struct, 
       // This argument passes transaction variables used by a responder
       // to complete a protocol transfer.  The values come from a sequence item.       
       input SHA512_in_responder_s SHA512_in_responder_struct 
       );// pragma tbx xtf   
  // Variables within the SHA512_in_initiator_struct:
  //   sha512_in_op_transactions op ;
  //   bit [7:0] test_case_sel ;
  // Variables within the SHA512_in_responder_struct:
  //   sha512_in_op_transactions op ;
  //   bit [7:0] test_case_sel ;
       // Reference code;
       //    How to wait for signal value
       //      while (control_signal == 1'b1) @(posedge clk_i);
       //    
       //    How to assign a responder struct member, named xyz, from a signal.   
       //    All available responder input and inout signals listed.
       //    Responder input signals
       //      SHA512_in_responder_struct.xyz = sha512_rst_i;  //     
       //      SHA512_in_responder_struct.xyz = hadrr_i;  //    [AHB_ADDR_WIDTH-1:0] 
       //      SHA512_in_responder_struct.xyz = hwdata_i;  //    [AHB_DATA_WIDTH-1:0] 
       //      SHA512_in_responder_struct.xyz = hsel_i;  //     
       //      SHA512_in_responder_struct.xyz = hwrite_i;  //     
       //      SHA512_in_responder_struct.xyz = hready_i;  //     
       //      SHA512_in_responder_struct.xyz = htrans_i;  //    [1:0] 
       //      SHA512_in_responder_struct.xyz = hsize_i;  //    [2:0] 
       //      SHA512_in_responder_struct.xyz = transaction_flag_in_monitor_i;  //     
       //      SHA512_in_responder_struct.xyz = op_i;  //    [2:0] 
       //      SHA512_in_responder_struct.xyz = test_case_sel_i;  //    [7:0] 
       //    Responder inout signals
       //    How to assign a signal, named xyz, from an initiator struct member.   
       //    All available responder output and inout signals listed.
       //    Notice the _o.  Those are storage variables that allow for procedural assignment.
       //    Responder output signals
       //    Responder inout signals
    
  @(posedge clk_i);
  if (!first_transfer) begin
    // Perform transfer response here.   
    // Reply using data recieved in the SHA512_in_responder_struct.
    @(posedge clk_i);
    // Reply using data recieved in the transaction handle.
    @(posedge clk_i);
  end
    // Wait for next transfer then gather info from intiator about the transfer.
    // Place the data into the SHA512_in_initiator_struct.
    @(posedge clk_i);
    @(posedge clk_i);
    first_transfer = 0;
  endtask
// pragma uvmf custom respond_and_wait_for_next_transfer end

 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

