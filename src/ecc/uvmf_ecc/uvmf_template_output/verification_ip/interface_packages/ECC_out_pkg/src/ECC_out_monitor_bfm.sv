//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This interface performs the ECC_out signal monitoring.
//      It is accessed by the uvm ECC_out monitor through a virtual
//      interface handle in the ECC_out configuration.  It monitors the
//      signals passed in through the port connection named bus of
//      type ECC_out_if.
//
//     Input signals from the ECC_out_if are assigned to an internal input
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
//                   blocks until an operation on the ECC_out bus is complete.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import uvmf_base_pkg_hdl::*;
import ECC_out_pkg_hdl::*;
`include "src/ECC_out_macros.svh"


interface ECC_out_monitor_bfm #(
  int AHB_ADDR_WIDTH = 32,
  int AHB_DATA_WIDTH = 32,
  int OUTPUT_TEXT_WIDTH = 384
  )

  ( ECC_out_if  bus );
  // The pragma below and additional ones in-lined further down are for running this BFM on Veloce
  // pragma attribute ECC_out_monitor_bfm partition_interface_xif                                  

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
      $psprintf("The BFM at '%m' has the following parameters: AHB_ADDR_WIDTH=%x AHB_DATA_WIDTH=%x OUTPUT_TEXT_WIDTH=%x ", AHB_ADDR_WIDTH,AHB_DATA_WIDTH,OUTPUT_TEXT_WIDTH),
      UVM_DEBUG)
end
`endif


  // Structure used to pass transaction data from monitor BFM to monitor class in agent.
`ECC_out_MONITOR_STRUCT
  ECC_out_monitor_s ECC_out_monitor_struct;

  // Structure used to pass configuration data from monitor class to monitor BFM.
 `ECC_out_CONFIGURATION_STRUCT
 

  // Config value to determine if this is an initiator or a responder 
  uvmf_initiator_responder_t initiator_responder;
  // Custom configuration variables.  
  // These are set using the configure function which is called during the UVM connect_phase

  tri clk_i;
  tri rst_n_i;
  tri  hresp_i;
  tri  hreadyout_i;
  tri [AHB_DATA_WIDTH-1:0] hrdata_i;
  tri  transaction_flag_out_monitor_i;
  tri [2:0] test_i;
  tri [1:0] op_i;
  assign clk_i = bus.clk;
  assign rst_n_i = bus.rst_n;
  assign hresp_i = bus.hresp;
  assign hreadyout_i = bus.hreadyout;
  assign hrdata_i = bus.hrdata;
  assign transaction_flag_out_monitor_i = bus.transaction_flag_out_monitor;
  assign test_i = bus.test;
  assign op_i = bus.op;

  // Proxy handle to UVM monitor
  ECC_out_pkg::ECC_out_monitor #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH)
    )
 proxy;
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
  
  reg transaction_flag; 
  reg [383:0]   privkey;
  reg [383:0]   pubkey_x;
  reg [383:0]   pubkey_y;
  reg [383:0]   R;
  reg [383:0]   S;
  reg [383:0]   verify_R;


  reg [1:0]     op;
  reg [2:0]     test;

  // ****************************************************************************              
  initial begin  
    
    transaction_flag = 0;
    privkey = 0;
    pubkey_x = 0;
    pubkey_y = 0;
    R = 0;
    S = 0;
    verify_R = 0;


    @go;                                                                                   
    forever begin                                                                        
      @(posedge clk_i);  
      do_monitor( ECC_out_monitor_struct );
                                                                 
 
      proxy.notify_transaction( ECC_out_monitor_struct );
 
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
    function void configure(ECC_out_configuration_s ECC_out_configuration_arg); // pragma tbx xtf  
    initiator_responder = ECC_out_configuration_arg.initiator_responder;
  // pragma uvmf custom configure begin
  // pragma uvmf custom configure end
  endfunction   


  // ****************************************************************************  
            
  task do_monitor(output ECC_out_monitor_s ECC_out_monitor_struct);
    //
    // Available struct members:
    //     //    ECC_out_monitor_struct.result_privkey
    //     //    ECC_out_monitor_struct.result_pubkey_x
    //     //    ECC_out_monitor_struct.result_pubkey_y
    //     //    ECC_out_monitor_struct.result_R
    //     //    ECC_out_monitor_struct.result_S
    //     //    ECC_out_monitor_struct.result_verify_R
    //     //
    // Reference code;
    //    How to wait for signal value
    //      while (control_signal === 1'b1) @(posedge clk_i);
    //    
    //    How to assign a struct member, named xyz, from a signal.   
    //    All available input signals listed.
    //      ECC_out_monitor_struct.xyz = hresp_i;  //     
    //      ECC_out_monitor_struct.xyz = hreadyout_i;  //     
    //      ECC_out_monitor_struct.xyz = hrdata_i;  //    [AHB_DATA_WIDTH-1:0] 
    //      ECC_out_monitor_struct.xyz = transaction_flag_out_monitor_i;  //     
    //      ECC_out_monitor_struct.xyz = test_i;  //    [2:0] 
    //      ECC_out_monitor_struct.xyz = op_i;  //    [1:0] 
    // pragma uvmf custom do_monitor begin
    // UVMF_CHANGE_ME : Implement protocol monitoring.  The commented reference code 
    // below are examples of how to capture signal values and assign them to 
    // structure members.  All available input signals are listed.  The 'while' 
    // code example shows how to wait for a synchronous flow control signal.  This
    // task should return when a complete transfer has been observed.  Once this task is
    // exited with captured values, it is then called again to wait for and observe 
    // the next transfer. One clock cycle is consumed between calls to do_monitor.
    if (rst_n_i == 0) begin
      while (rst_n_i == 0) @(posedge clk_i);
      repeat (5) @(posedge clk_i);
      ECC_out_monitor_struct.result_privkey   = 0;
      ECC_out_monitor_struct.result_pubkey_x  = 0;
      ECC_out_monitor_struct.result_pubkey_y  = 0;
      ECC_out_monitor_struct.result_R         = 0;
      ECC_out_monitor_struct.result_S         = 0;
      ECC_out_monitor_struct.result_verify_R         = 0;

      op = op_i;
      test = test_i;
    end
    else begin
      op = op_i;
      test = test_i;

      privkey   = 0;
      pubkey_x  = 0;
      pubkey_y  = 0;
      R         = 0;
      S         = 0;
      verify_R  = 0;

      
      transaction_flag = 0;

      $display("@ %0t ** ECC_out_monitor_bfm** : test = %3b", $time, test);
      $display("@ %0t ** ECC_out_monitor_bfm** : op = %2b", $time, op);

      while (transaction_flag_out_monitor_i ==0) @(posedge clk_i);
      if (transaction_flag_out_monitor_i == 1 ) begin
        $display("***DEBUG*** transaction_flag_out_monitor is 1");
        transaction_flag = 1;
        repeat (2) @(posedge clk_i);
        if (test == 3'b001 || test == 3'b010) begin // ecc_normal_test (3'b001) or ecc_otl_reset_test (3'b010)
          if (op == 2'b00) begin // KEY_GEN
            @(posedge clk_i);
            privkey[383:352] = hrdata_i;
            $display("**ECC_out_monitor_bfm: privkey[383:352] = %h, time = %0t", privkey[383:352], $time);
            repeat (2) @(posedge clk_i);
            privkey[351:320] = hrdata_i;
            repeat (2) @(posedge clk_i);
            privkey[319:288] = hrdata_i;
            repeat (2) @(posedge clk_i);
            privkey[287:256] = hrdata_i;
            repeat (2) @(posedge clk_i);
            privkey[255:224] = hrdata_i;
            repeat (2) @(posedge clk_i);
            privkey[223:192] = hrdata_i;
            repeat (2) @(posedge clk_i);
            privkey[191:160] = hrdata_i;
            repeat (2) @(posedge clk_i);
            privkey[159:128] = hrdata_i;
            repeat (2) @(posedge clk_i);
            privkey[127:96]  = hrdata_i;
            repeat (2) @(posedge clk_i);
            privkey[95:64]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            privkey[63:32]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            privkey[31:0]    = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[383:352] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[351:320] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[319:288] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[287:256] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[255:224] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[223:192] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[191:160] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[159:128] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[127:96]  = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[95:64]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[63:32]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[31:0]    = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[383:352] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[351:320] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[319:288] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[287:256] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[255:224] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[223:192] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[191:160] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[159:128] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[127:96]  = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[95:64]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[63:32]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[31:0]    = hrdata_i;

            @(posedge clk_i);
            ECC_out_monitor_struct.result_privkey = privkey;
            ECC_out_monitor_struct.result_pubkey_x = pubkey_x;
            ECC_out_monitor_struct.result_pubkey_y = pubkey_y;
            ECC_out_monitor_struct.result_R = 0;
            ECC_out_monitor_struct.result_S = 0;
            ECC_out_monitor_struct.result_verify_R = 0;
            
            privkey   = 0;
            pubkey_x  = 0;
            pubkey_y  = 0;
            R         = 0;
            S         = 0;
            verify_R  = 0;

            
          end
          else if (op == 2'b01) begin // KEY_SIGN
            @(posedge clk_i);
            R[383:352] = hrdata_i;
            repeat (2) @(posedge clk_i);
            R[351:320] = hrdata_i;
            repeat (2) @(posedge clk_i);
            R[319:288] = hrdata_i;
            repeat (2) @(posedge clk_i);
            R[287:256] = hrdata_i;
            repeat (2) @(posedge clk_i);
            R[255:224] = hrdata_i;
            repeat (2) @(posedge clk_i);
            R[223:192] = hrdata_i;
            repeat (2) @(posedge clk_i);
            R[191:160] = hrdata_i;
            repeat (2) @(posedge clk_i);
            R[159:128] = hrdata_i;
            repeat (2) @(posedge clk_i);
            R[127:96]  = hrdata_i;
            repeat (2) @(posedge clk_i);
            R[95:64]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            R[63:32]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            R[31:0]    = hrdata_i;
            repeat (2) @(posedge clk_i);
            S[383:352] = hrdata_i;
            repeat (2) @(posedge clk_i);
            S[351:320] = hrdata_i;
            repeat (2) @(posedge clk_i);
            S[319:288] = hrdata_i;
            repeat (2) @(posedge clk_i);
            S[287:256] = hrdata_i;
            repeat (2) @(posedge clk_i);
            S[255:224] = hrdata_i;
            repeat (2) @(posedge clk_i);
            S[223:192] = hrdata_i;
            repeat (2) @(posedge clk_i);
            S[191:160] = hrdata_i;
            repeat (2) @(posedge clk_i);
            S[159:128] = hrdata_i;
            repeat (2) @(posedge clk_i);
            S[127:96]  = hrdata_i;
            repeat (2) @(posedge clk_i);
            S[95:64]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            S[63:32]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            S[31:0]    = hrdata_i;

            @(posedge clk_i);
            ECC_out_monitor_struct.result_privkey = 0;
            ECC_out_monitor_struct.result_pubkey_x = 0;
            ECC_out_monitor_struct.result_pubkey_y = 0;
            ECC_out_monitor_struct.result_R = R;
            ECC_out_monitor_struct.result_S = S;
            ECC_out_monitor_struct.result_verify_R = 0;
            

            privkey   = 0;
            pubkey_x  = 0;
            pubkey_y  = 0;
            R         = 0;
            S         = 0;
            verify_R  = 0;

          end
          else if (op == 2'b10) begin // KEY_VERIFY
            @(posedge clk_i);
            verify_R[383:352] = hrdata_i;
            repeat (2) @(posedge clk_i);
            verify_R[351:320] = hrdata_i;
            repeat (2) @(posedge clk_i);
            verify_R[319:288] = hrdata_i;
            repeat (2) @(posedge clk_i);
            verify_R[287:256] = hrdata_i;
            repeat (2) @(posedge clk_i);
            verify_R[255:224] = hrdata_i;
            repeat (2) @(posedge clk_i);
            verify_R[223:192] = hrdata_i;
            repeat (2) @(posedge clk_i);
            verify_R[191:160] = hrdata_i;
            repeat (2) @(posedge clk_i);
            verify_R[159:128] = hrdata_i;
            repeat (2) @(posedge clk_i);
            verify_R[127:96]  = hrdata_i;
            repeat (2) @(posedge clk_i);
            verify_R[95:64]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            verify_R[63:32]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            verify_R[31:0]    = hrdata_i;

            @(posedge clk_i);
            ECC_out_monitor_struct.result_privkey = 0;
            ECC_out_monitor_struct.result_pubkey_x = 0;
            ECC_out_monitor_struct.result_pubkey_y = 0;
            ECC_out_monitor_struct.result_R = 0;
            ECC_out_monitor_struct.result_S = 0;
            ECC_out_monitor_struct.result_verify_R = verify_R;
            

            privkey   = 0;
            pubkey_x  = 0;
            pubkey_y  = 0;
            R         = 0;
            S         = 0;
            verify_R  = 0;

          end
        end
          else if (test == 3'b011) begin // ecc_openssl_test, KEY_GEN
            $display("***DEBUG*** TEst is ecc_openssl_test");
            @(posedge clk_i);
            pubkey_x[383:352] = hrdata_i;
            $display("pubkey[383:352] = %h", pubkey_x[383:352]);
            repeat (2) @(posedge clk_i);
            pubkey_x[351:320] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[319:288] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[287:256] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[255:224] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[223:192] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[191:160] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[159:128] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[127:96]  = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[95:64]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[63:32]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_x[31:0]    = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[383:352] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[351:320] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[319:288] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[287:256] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[255:224] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[223:192] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[191:160] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[159:128] = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[127:96]  = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[95:64]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[63:32]   = hrdata_i;
            repeat (2) @(posedge clk_i);
            pubkey_y[31:0]    = hrdata_i;

            @(posedge clk_i);
            ECC_out_monitor_struct.result_privkey = 0;
            ECC_out_monitor_struct.result_pubkey_x = pubkey_x;
            ECC_out_monitor_struct.result_pubkey_y = pubkey_y;
            ECC_out_monitor_struct.result_R = 0;
            ECC_out_monitor_struct.result_S = 0;
            ECC_out_monitor_struct.result_verify_R = 0;
            

            privkey   = 0;
            pubkey_x  = 0;
            pubkey_y  = 0;
            R         = 0;
            S         = 0;
            verify_R  = 0;
          end
        end
      end
    // pragma uvmf custom do_monitor end
  endtask         
  
 
endinterface

// pragma uvmf custom external begin
// pragma uvmf custom external end

