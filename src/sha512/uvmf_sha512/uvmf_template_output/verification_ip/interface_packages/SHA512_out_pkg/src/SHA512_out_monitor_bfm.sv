//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This interface performs the SHA512_out signal monitoring.
//      It is accessed by the uvm SHA512_out monitor through a virtual
//      interface handle in the SHA512_out configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type SHA512_out_if.
//
//     Input signals from the SHA512_out_if are assigned to an internal input
//     signal with a _i suffix.  The _i signal should be used for sampling.
//
//     The input signal connections are as follows:
//       bus.signal -> signal_i 
//
//      Interface functions and tasks used by UVM components:
//             monitor(inout TRANS_T txn);
//                   This task receives the transaction, txn, from the
//                   UVM monitor and then populates variables in txn
//                   from values observed on bus activity.  This task
//                   blocks until an operation on the SHA512_out bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import SHA512_out_pkg_hdl::*;
`include "src/SHA512_out_macros.svh"


interface SHA512_out_monitor_bfm #(
  int AHB_DATA_WIDTH = 32,
  int AHB_ADDR_WIDTH = 32,
  int OUTPUT_TEXT_WIDTH = 512,
  bit BYPASS_HSEL = 0
  )

  ( SHA512_out_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute SHA512_out_monitor_bfm partition_interface_xif                                  

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
      $psprintf("The BFM at '%m' has the following parameters: AHB_DATA_WIDTH=%x AHB_ADDR_WIDTH=%x OUTPUT_TEXT_WIDTH=%x BYPASS_HSEL=%x ", AHB_DATA_WIDTH,AHB_ADDR_WIDTH,OUTPUT_TEXT_WIDTH,BYPASS_HSEL),
      UVM_DEBUG)
end
`endif


  // Structure used to pass transaction data from monitor BFM to monitor class in agent.
`SHA512_out_MONITOR_STRUCT
  SHA512_out_monitor_s SHA512_out_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `SHA512_out_CONFIGURATION_STRUCT
 

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri rst_i;
  tri  hresp_i;
  tri  hreadyout_i;
  tri [AHB_DATA_WIDTH-1:0] hrdata_i;
  tri  read_flag_monitor_i;
  assign clk_i = bus.clk;
  assign rst_i = bus.rst;
  assign hresp_i = bus.hresp;
  assign hreadyout_i = bus.hreadyout;
  assign hrdata_i = bus.hrdata;
  assign read_flag_monitor_i = bus.read_flag_monitor;

  // Proxy handle to UVM monitor
  SHA512_out_pkg::SHA512_out_monitor #(
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
    .BYPASS_HSEL(BYPASS_HSEL)
    )
 proxy;
  // pragma tbx oneway proxy.notify_transaction                 

  // pragma uvmf custom interface_item_additional begin
  parameter MODE_SHA_512_224     = 2'h0;
  parameter MODE_SHA_512_256     = 2'h1;
  parameter MODE_SHA_384         = 2'h2;
  parameter MODE_SHA_512         = 2'h3;

  reg [511:0] result_temp;
  reg [511 : 0] mask;
  reg [511 : 0] masked_data;

  int op_cnt;
  // pragma uvmf custom interface_item_additional end
  
  //******************************************************************                         
  task wait_for_reset();// pragma tbx xtf  
    @(posedge clk_i) ;                                                                    
    do_wait_for_reset();                                                                   
  endtask                                                                                   

  // ****************************************************************************              
  task do_wait_for_reset(); 
  // pragma uvmf custom reset_condition begin
    wait ( rst_i == 1 ) ;                                                              
    @(posedge clk_i) ;                                                                    
  // pragma uvmf custom reset_condition end                                                                
  endtask    

  //******************************************************************                         
 
  task wait_for_num_clocks(input int unsigned count); // pragma tbx xtf 
    @(posedge clk_i);  
                                                                   
    repeat (count-1) @(posedge clk_i);                                                    
  endtask      

  //******************************************************************                         
  event go;                                                                                 
  function void start_monitoring();// pragma tbx xtf    
    -> go;
  endfunction                                                                               
  
  // ****************************************************************************              
  initial begin                                                                             
    @go;                                                                                   
    forever begin                                                                        
      @(posedge clk_i);  
      do_monitor( SHA512_out_monitor_struct );
                                                                 
 
      proxy.notify_transaction( SHA512_out_monitor_struct );
 
    end                                                                                    
  end                                                                                       

  //******************************************************************
  // The configure() function is used to pass agent configuration
  // variables to the monitor BFM.  It is called by the monitor within
  // the agent at the beginning of the simulation.  It may be called 
  // during the simulation if agent configuration variables are updated
  // and the monitor BFM needs to be aware of the new configuration 
  // variables.
  //
    function void configure(SHA512_out_configuration_s SHA512_out_configuration_arg); // pragma tbx xtf  
    initiator_responder = SHA512_out_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction   


  // ****************************************************************************  
            
  task do_monitor(output SHA512_out_monitor_s SHA512_out_monitor_struct);
    //
    // Available struct members:
    //     //    SHA512_out_monitor_struct.result
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal == 1'b1) @(posedge clk_i);
    //    
    //    How to assign a struct member, named xyz, from a signal.   
    //    All available input signals listed.
    //      SHA512_out_monitor_struct.xyz = hresp_i;  //     
    //      SHA512_out_monitor_struct.xyz = hreadyout_i;  //     
    //      SHA512_out_monitor_struct.xyz = hrdata_i;  //    [AHB_DATA_WIDTH-1:0] 
    //      SHA512_out_monitor_struct.xyz = read_flag_monitor_i;  //     
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code 
    // below are examples of how to capture signal values and assign them to 
    // structure members.  All available input signals are listed.  The 'while' 
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe 
    // the next transfer. One clock cycle is consumed between calls to do_monitor.
    
    if (rst_i == 0) begin
      while (rst_i == 0) @(posedge clk_i);
      repeat (5) @(posedge clk_i);
      SHA512_out_monitor_struct.result = 0;
    end
    else begin
      result_temp = 0;
      op_cnt = 0;
      mask = {16{32'hffffffff}};
      masked_data = 0;

      while (read_flag_monitor_i != 1) @(posedge clk_i);

      while (read_flag_monitor_i == 1)begin
        op_cnt = op_cnt + 1;
        @(posedge clk_i);
      end

      repeat(2) @(posedge clk_i);
      result_temp[511 : 480] = hrdata_i;
      @(posedge clk_i);
      result_temp[479 : 448] = hrdata_i;
      @(posedge clk_i);
      result_temp[447 : 416] = hrdata_i;
      @(posedge clk_i);
      result_temp[415 : 384] = hrdata_i;
      @(posedge clk_i);
      result_temp[383 : 352] = hrdata_i;
      @(posedge clk_i);
      result_temp[351 : 320] = hrdata_i;
      @(posedge clk_i);
      result_temp[319 : 288] = hrdata_i;
      @(posedge clk_i);
      result_temp[287 : 256] = hrdata_i;
      @(posedge clk_i);
      result_temp[255 : 224] = hrdata_i;
      @(posedge clk_i);
      result_temp[223 : 192] = hrdata_i;
      @(posedge clk_i);
      result_temp[191 : 160] = hrdata_i;
      @(posedge clk_i);
      result_temp[159 : 128] = hrdata_i;
      @(posedge clk_i);
      result_temp[127 :  96] = hrdata_i;
      @(posedge clk_i);
      result_temp[95  :  64] = hrdata_i;
      @(posedge clk_i);
      result_temp[63  :  32] = hrdata_i;
      @(posedge clk_i);
      result_temp[31  :   0] = hrdata_i;
      @(posedge clk_i);
    end

    mask = get_mask(op_cnt[1:0]);
    masked_data = result_temp & mask;

    SHA512_out_monitor_struct.result = masked_data;

    // pragma uvmf custom do_monitor end
  endtask         
  
  function [511 : 0] get_mask(input [2:0] op);
    begin
      case (op)
        MODE_SHA_512_224: get_mask = {{7{32'hffffffff}}, {9{32'h00000000}}};
        MODE_SHA_512_256: get_mask = {{8{32'hffffffff}}, {8{32'h00000000}}};
        MODE_SHA_384:     get_mask = {{12{32'hffffffff}}, {4{32'h00000000}}};
        MODE_SHA_512:     get_mask = {16{32'hffffffff}};
      endcase // case (mode)
    end
  endfunction // get_mask

endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

