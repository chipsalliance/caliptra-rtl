//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This class receives SHA512_in transactions observed by the
//     SHA512_in monitor BFM and broadcasts them through the analysis port
//     on the agent. It accesses the monitor BFM through the monitor
//     task. This UVM component captures transactions
//     for viewing in the waveform viewer if the
//     enable_transaction_viewing flag is set in the configuration.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class SHA512_in_monitor #(
      int AHB_DATA_WIDTH = 32,
      int AHB_ADDR_WIDTH = 32,
      bit BYPASS_HSEL = 0
      )
 extends uvmf_monitor_base #(
                    .CONFIG_T(SHA512_in_configuration  #(
                             .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                             .BYPASS_HSEL(BYPASS_HSEL)
                             )
),
                    .BFM_BIND_T(virtual SHA512_in_monitor_bfm  #(
                             .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                             .BYPASS_HSEL(BYPASS_HSEL)
                             )
),
                    .TRANS_T(SHA512_in_transaction  #(
                             .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                             .BYPASS_HSEL(BYPASS_HSEL)
                             )
));

  `uvm_component_param_utils( SHA512_in_monitor #(
                              AHB_DATA_WIDTH,
                              AHB_ADDR_WIDTH,
                              BYPASS_HSEL
                              )
)

// Structure used to pass data from monitor BFM to monitor class in agent.
// Use to_monitor_struct function to pack transaction variables into structure.
// Use from_monitor_struct function to unpack transaction variables from structure.
`SHA512_in_MONITOR_STRUCT

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
// ****************************************************************************
// This function is the standard SystemVerilog constructor.
//
  function new( string name = "", uvm_component parent = null );
    super.new( name, parent );
  endfunction

// ****************************************************************************
// This function sends configuration object variables to the monitor BFM 
// using the configuration struct.
//
   virtual function void configure(input CONFIG_T cfg);
      bfm.configure( cfg.to_struct() );

   endfunction

// ****************************************************************************
// This function places a handle to this class in the proxy variable in the
// monitor BFM.  This allows the monitor BFM to call the notify_transaction
// function within this class.
//
   virtual function void set_bfm_proxy_handle();
      bfm.proxy = this;   endfunction

// ***************************************************************************              
  virtual task run_phase(uvm_phase phase);                                                   
  // Start monitor BFM thread and don't call super.run() in order to                       
  // override the default monitor proxy 'pull' behavior with the more                      
  // emulation-friendly BFM 'push' approach using the notify_transaction                   
  // function below                                                                        
  bfm.start_monitoring();                                                   
  endtask                                                                                    
  
// **************************************************************************  
  
// This function is called by the monitor BFM.  It receives data observed by the
// monitor BFM.  Data is passed using the SHA512_in_monitor_struct.          
 virtual function void notify_transaction(input SHA512_in_monitor_s SHA512_in_monitor_struct);
 
 
    trans = new("trans");
    trans.from_monitor_struct(SHA512_in_monitor_struct);
    trans.start_time = time_stamp;                                                          
    trans.end_time = $time;                                                                 
    time_stamp = trans.end_time;
 
    analyze(trans);                                                                         
  endfunction  

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

