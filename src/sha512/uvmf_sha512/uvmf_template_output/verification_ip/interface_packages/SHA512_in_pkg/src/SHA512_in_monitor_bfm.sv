//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This interface performs the SHA512_in signal monitoring.
//      It is accessed by the uvm SHA512_in monitor through a virtual
//      interface handle in the SHA512_in configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type SHA512_in_if.
//
//     Input signals from the SHA512_in_if are assigned to an internal input
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
//                   blocks until an operation on the SHA512_in bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import SHA512_in_pkg_hdl::*;
`include "src/SHA512_in_macros.svh"


interface SHA512_in_monitor_bfm #(
  int AHB_DATA_WIDTH = 32,
  int AHB_ADDR_WIDTH = 32,
  bit BYPASS_HSEL = 0
  )

  ( SHA512_in_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute SHA512_in_monitor_bfm partition_interface_xif                                  

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


  // Structure used to pass transaction data from monitor BFM to monitor class in agent.
`SHA512_in_MONITOR_STRUCT
  SHA512_in_monitor_s SHA512_in_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `SHA512_in_CONFIGURATION_STRUCT
 

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri rst_i;
  tri  sha512_rst_i;
  tri [AHB_ADDR_WIDTH-1:0] hadrr_i;
  tri [AHB_DATA_WIDTH-1:0] hwdata_i;
  tri  hsel_i;
  tri  hwrite_i;
  tri  hready_i;
  tri [1:0] htrans_i;
  tri [2:0] hsize_i;
  tri  transaction_flag_in_monitor_i;
  tri [2:0] op_i;
  tri [7:0] test_case_sel_i;
  assign clk_i = bus.clk;
  assign rst_i = bus.rst;
  assign sha512_rst_i = bus.sha512_rst;
  assign hadrr_i = bus.hadrr;
  assign hwdata_i = bus.hwdata;
  assign hsel_i = bus.hsel;
  assign hwrite_i = bus.hwrite;
  assign hready_i = bus.hready;
  assign htrans_i = bus.htrans;
  assign hsize_i = bus.hsize;
  assign transaction_flag_in_monitor_i = bus.transaction_flag_in_monitor;
  assign op_i = bus.op;
  assign test_case_sel_i = bus.test_case_sel;

  // Proxy handle to UVM monitor
  SHA512_in_pkg::SHA512_in_monitor #(
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .BYPASS_HSEL(BYPASS_HSEL)
    )
 proxy;
  // pragma tbx oneway proxy.notify_transaction                 

  // pragma uvmf custom interface_item_additional begin
 int internal_debug;
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
      internal_debug = 0;                                                                
      @(posedge clk_i);  
      do_monitor( SHA512_in_monitor_struct );
                                                                 
 
      proxy.notify_transaction( SHA512_in_monitor_struct );
      // steven mod, delay to wait for SHA512_out_monitor
      repeat(20) @(posedge clk_i);
 
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
    function void configure(SHA512_in_configuration_s SHA512_in_configuration_arg); // pragma tbx xtf  
    initiator_responder = SHA512_in_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction   


  // ****************************************************************************  
            
  task do_monitor(output SHA512_in_monitor_s SHA512_in_monitor_struct);
    //
    // Available struct members:
    //     //    SHA512_in_monitor_struct.op
    //     //    SHA512_in_monitor_struct.test_case_sel
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal == 1'b1) @(posedge clk_i);
    //    
    //    How to assign a struct member, named xyz, from a signal.   
    //    All available input signals listed.
    //      SHA512_in_monitor_struct.xyz = sha512_rst_i;  //     
    //      SHA512_in_monitor_struct.xyz = hadrr_i;  //    [AHB_ADDR_WIDTH-1:0] 
    //      SHA512_in_monitor_struct.xyz = hwdata_i;  //    [AHB_DATA_WIDTH-1:0] 
    //      SHA512_in_monitor_struct.xyz = hsel_i;  //     
    //      SHA512_in_monitor_struct.xyz = hwrite_i;  //     
    //      SHA512_in_monitor_struct.xyz = hready_i;  //     
    //      SHA512_in_monitor_struct.xyz = htrans_i;  //    [1:0] 
    //      SHA512_in_monitor_struct.xyz = hsize_i;  //    [2:0] 
    //      SHA512_in_monitor_struct.xyz = transaction_flag_in_monitor_i;  //     
    //      SHA512_in_monitor_struct.xyz = op_i;  //    [2:0] 
    //      SHA512_in_monitor_struct.xyz = test_case_sel_i;  //    [7:0] 
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code 
    // below are examples of how to capture signal values and assign them to 
    // structure members.  All available input signals are listed.  The 'while' 
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe 
    // the next transfer. One clock cycle is consumed between calls to do_monitor.
    
    if (sha512_rst_i == 1'b0) begin
      while (sha512_rst_i == 1'b0) @(posedge clk_i);
      SHA512_in_monitor_struct.op = sha512_in_op_transactions'(op_i);
      SHA512_in_monitor_struct.test_case_sel = test_case_sel_i;
    end
    else begin
      while (transaction_flag_in_monitor_i == 0) @(posedge clk_i);
      internal_debug = 1;
      SHA512_in_monitor_struct.op = sha512_in_op_transactions'(op_i);
      SHA512_in_monitor_struct.test_case_sel = test_case_sel_i;
    end
    
    // pragma uvmf custom do_monitor end
  endtask         
  
 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

