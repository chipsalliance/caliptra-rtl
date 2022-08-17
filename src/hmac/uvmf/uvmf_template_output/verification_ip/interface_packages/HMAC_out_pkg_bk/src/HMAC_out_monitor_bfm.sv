//----------------------------------------------------------------------
// Created with uvmf_gen version 2021.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This interface performs the HMAC_out signal monitoring.
//      It is accessed by the uvm HMAC_out monitor through a virtual
//      interface handle in the HMAC_out configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type HMAC_out_if.
//
//     Input signals from the HMAC_out_if are assigned to an internal input
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
//                   blocks until an operation on the HMAC_out bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import HMAC_out_pkg_hdl::*;
`include "src/HMAC_out_macros.svh"


interface HMAC_out_monitor_bfm #(
  int AHB_DATA_WIDTH = 32,
  int AHB_ADDR_WIDTH = 32,
  int OUTPUT_TEXT_WIDTH = 1280, //TODO knupadhy: might need to change this to 384
  bit BYPASS_HSEL = 0
  )
  ( HMAC_out_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute HMAC_out_monitor_bfm partition_interface_xif                                  

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
`HMAC_out_MONITOR_STRUCT
  HMAC_out_monitor_s HMAC_out_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `HMAC_out_CONFIGURATION_STRUCT
 

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri rst_i;
  tri  hresp_i;
  tri  hreadyout_i;
  tri [AHB_DATA_WIDTH-1:0] hrdata_i;
  tri  transaction_flag_in_monitor_i;
  assign clk_i = bus.clk;
  assign rst_i = bus.rst;
  assign hresp_i = bus.hresp;
  assign hreadyout_i = bus.hreadyout;
  assign hrdata_i = bus.hrdata;
  assign transaction_flag_in_monitor_i = bus.transaction_flag_in_monitor;

  // Proxy handle to UVM monitor
  HMAC_out_pkg::HMAC_out_monitor #(
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
    .BYPASS_HSEL(BYPASS_HSEL)
    ) proxy;
  // pragma tbx oneway proxy.notify_transaction                 

  // pragma uvmf custom interface_item_additional begin
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
  
  reg transaction_flag;
  reg [383:0] result_temp;
  reg [383:0] block_temp;

  // ****************************************************************************              
  initial begin  

    transaction_flag = 0;
    result_temp = 0;
    block_temp = 0;

    @go;                                                                                   
    forever begin                                                                        
      @(posedge clk_i);  
      do_monitor( HMAC_out_monitor_struct );
                                                                 
 
      proxy.notify_transaction( HMAC_out_monitor_struct );
 
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
    function void configure(HMAC_out_configuration_s HMAC_out_configuration_arg); // pragma tbx xtf  
    initiator_responder = HMAC_out_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction   


  // ****************************************************************************  
            
  task do_monitor(output HMAC_out_monitor_s HMAC_out_monitor_struct);
    //
    // Available struct members:
    //     //    HMAC_out_monitor_struct.result
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal == 1'b1) @(posedge clk_i);
    //    
    //    How to assign a struct member, named xyz, from a signal.   
    //    All available input signals listed.
    //      HMAC_out_monitor_struct.xyz = hresp_i;  //     
    //      HMAC_out_monitor_struct.xyz = hreadyout_i;  //     
    //      HMAC_out_monitor_struct.xyz = hrdata_i;  //    [AHB_DATA_WIDTH-1:0] 
    //      HMAC_out_monitor_struct.xyz = transaction_flag_in_monitor_i;  //     
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
      HMAC_out_monitor_struct.result = 0;
    end
    else begin
      //Add logic for multiple blks later
      result_temp = 0;
      block_temp = 0;
      transaction_flag = 0;
      $display("In else blk KNU");

      while (transaction_flag_in_monitor_i ==0) @(posedge clk_i);
      repeat(4) @(posedge clk_i);
      if (transaction_flag_in_monitor_i == 1 ) transaction_flag = 1;
      block_temp[383:352] = hrdata_i;
      repeat (2) @(posedge clk_i);
      block_temp[351:320] = hrdata_i;
      repeat (2) @(posedge clk_i);
      block_temp[319:288] = hrdata_i;
      repeat (2) @(posedge clk_i);
      block_temp[287:256] = hrdata_i;
      repeat (2) @(posedge clk_i);
      block_temp[255:224] = hrdata_i;
      repeat (2) @(posedge clk_i);
      block_temp[223:192] = hrdata_i;
      repeat (2) @(posedge clk_i);
      block_temp[191:160] = hrdata_i;
      repeat (2) @(posedge clk_i);
      block_temp[159:128] = hrdata_i;
      repeat (2) @(posedge clk_i);
      block_temp[127:96]  = hrdata_i;
      repeat (2) @(posedge clk_i);
      block_temp[95:64]   = hrdata_i;
      repeat (2) @(posedge clk_i);
      block_temp[63:32]   = hrdata_i;
      repeat (2) @(posedge clk_i);
      block_temp[31:0]    = hrdata_i;

      @(posedge clk_i);
      HMAC_out_monitor_struct.result = block_temp;
      block_temp = 0;
      $display("%%%% result = %h %%%%", HMAC_out_monitor_struct.result);
    end


    // pragma uvmf custom do_monitor end
  endtask         
  
 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

