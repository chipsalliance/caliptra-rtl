//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This interface performs the ECC_in signal monitoring.
//      It is accessed by the uvm ECC_in monitor through a virtual
//      interface handle in the ECC_in configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type ECC_in_if.
//
//     Input signals from the ECC_in_if are assigned to an internal input
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
//                   blocks until an operation on the ECC_in bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import ECC_in_pkg_hdl::*;
`include "src/ECC_in_macros.svh"


interface ECC_in_monitor_bfm #(
  int AHB_ADDR_WIDTH = 32,
  int AHB_DATA_WIDTH = 32
  )

  ( ECC_in_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute ECC_in_monitor_bfm partition_interface_xif                                  

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
      $psprintf("The BFM at '%m' has the following parameters: AHB_ADDR_WIDTH=%x AHB_DATA_WIDTH=%x ", AHB_ADDR_WIDTH,AHB_DATA_WIDTH),
      UVM_DEBUG)
end
`endif


  // Structure used to pass transaction data from monitor BFM to monitor class in agent.
`ECC_in_MONITOR_STRUCT
  ECC_in_monitor_s ECC_in_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `ECC_in_CONFIGURATION_STRUCT
 

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri rst_n_i;
  tri  ecc_rst_n_i;
  tri [AHB_ADDR_WIDTH-1:0] haddr_i;
  tri [AHB_DATA_WIDTH-1:0] hwdata_i;
  tri  hsel_i;
  tri  hwrite_i;
  tri  hready_i;
  tri [1:0] htrans_i;
  tri [2:0] hsize_i;
  tri [AHB_DATA_WIDTH-1:0] hrdata_i;
  tri  hreadyout_i;
  tri  transaction_flag_out_monitor_i;
  tri [2:0] test_i;
  tri [1:0] op_i;
  assign clk_i = bus.clk;
  assign rst_n_i = bus.rst_n;
  assign ecc_rst_n_i = bus.ecc_rst_n;
  assign haddr_i = bus.haddr;
  assign hwdata_i = bus.hwdata;
  assign hsel_i = bus.hsel;
  assign hwrite_i = bus.hwrite;
  assign hready_i = bus.hready;
  assign htrans_i = bus.htrans;
  assign hsize_i = bus.hsize;
  assign hrdata_i = bus.hrdata;
  assign hreadyout_i = bus.hreadyout;
  assign transaction_flag_out_monitor_i = bus.transaction_flag_out_monitor;
  assign test_i = bus.test;
  assign op_i = bus.op;

  // Proxy handle to UVM monitor
  ECC_in_pkg::ECC_in_monitor #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH)
    )
 proxy;
  // pragma tbx oneway proxy.notify_transaction                 

  // pragma uvmf custom interface_item_additional begin
  reg transaction_flag;
 // pragma uvmf custom interface_item_additional end
  
  //******************************************************************                         
  task wait_for_reset();// pragma tbx xtf  
    @(posedge clk_i) ;                                                                    
    do_wait_for_reset();                                                                   
  endtask                                                                                   

  // ****************************************************************************              
  task do_wait_for_reset(); 
  // pragma uvmf custom reset_condition begin
    wait ( rst_n_i === 1 ) ;                                                              
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
      do_monitor( ECC_in_monitor_struct );
                                                                 
 
      proxy.notify_transaction( ECC_in_monitor_struct );
 
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
    function void configure(ECC_in_configuration_s ECC_in_configuration_arg); // pragma tbx xtf  
    initiator_responder = ECC_in_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction   


  // ****************************************************************************  
            
  task do_monitor(output ECC_in_monitor_s ECC_in_monitor_struct);
    //
    // Available struct members:
    //     //    ECC_in_monitor_struct.test
    //     //    ECC_in_monitor_struct.op
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i);
    //    
    //    How to assign a struct member, named xyz, from a signal.   
    //    All available input signals listed.
    //      ECC_in_monitor_struct.xyz = ecc_rst_n_i;  //     
    //      ECC_in_monitor_struct.xyz = haddr_i;  //    [AHB_ADDR_WIDTH-1:0] 
    //      ECC_in_monitor_struct.xyz = hwdata_i;  //    [AHB_DATA_WIDTH-1:0] 
    //      ECC_in_monitor_struct.xyz = hsel_i;  //     
    //      ECC_in_monitor_struct.xyz = hwrite_i;  //     
    //      ECC_in_monitor_struct.xyz = hready_i;  //     
    //      ECC_in_monitor_struct.xyz = htrans_i;  //    [1:0] 
    //      ECC_in_monitor_struct.xyz = hsize_i;  //    [2:0] 
    //      ECC_in_monitor_struct.xyz = hrdata_i;  //    [AHB_DATA_WIDTH-1:0] 
    //      ECC_in_monitor_struct.xyz = hreadyout_i;  //     
    //      ECC_in_monitor_struct.xyz = transaction_flag_out_monitor_i;  //     
    //      ECC_in_monitor_struct.xyz = test_i;  //    [2:0] 
    //      ECC_in_monitor_struct.xyz = op_i;  //    [1:0] 
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code 
    // below are examples of how to capture signal values and assign them to 
    // structure members.  All available input signals are listed.  The 'while' 
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe 
    // the next transfer. One clock cycle is consumed between calls to do_monitor.
    if (ecc_rst_n_i == 1'b0) begin
      while (ecc_rst_n_i == 1'b0) @(posedge clk_i);
      ECC_in_monitor_struct.test = ecc_in_test_transactions'(test_i);
      ECC_in_monitor_struct.op = ecc_in_op_transactions'(op_i);
      transaction_flag = 0; //Still want to capture reset tx in the out monitor
    end
    else begin
	    transaction_flag = 0;
	    while (transaction_flag == 0) begin
		    if (transaction_flag_out_monitor_i == 1) begin
          transaction_flag = 1;
          ECC_in_monitor_struct.test = ecc_in_test_transactions'(test_i);
				  ECC_in_monitor_struct.op = ecc_in_op_transactions'(op_i);
		    end //tx flag monitor = 1
		    @(posedge clk_i);
	    end //tx flag = 0
    end

    // pragma uvmf custom do_monitor end
  endtask         
  
 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

