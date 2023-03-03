//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This class receives ECC_out transactions observed by the
//     ECC_out monitor BFM and broadcasts them through the analysis port
//     on the agent. It accesses the monitor BFM through the monitor
//     task. This UVM component captures transactions
//     for viewing in the waveform viewer if the
//     enable_transaction_viewing flag is set in the configuration.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class ECC_out_monitor #(
      int AHB_ADDR_WIDTH = 32,
      int AHB_DATA_WIDTH = 32,
      int OUTPUT_TEXT_WIDTH = 384
      )
 extends uvmf_monitor_base #(
                    .CONFIG_T(ECC_out_configuration  #(
                             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                             .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                             .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH)
                             )
),
                    .BFM_BIND_T(virtual ECC_out_monitor_bfm  #(
                             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                             .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                             .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH)
                             )
),
                    .TRANS_T(ECC_out_transaction  #(
                             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                             .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                             .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH)
                             )
));

  `uvm_component_param_utils( ECC_out_monitor #(
                              AHB_ADDR_WIDTH,
                              AHB_DATA_WIDTH,
                              OUTPUT_TEXT_WIDTH
                              )
)

// Structure used to pass data from monitor BFM to monitor class in agent.
// Use to_monitor_struct function to pack transaction variables into structure.
// Use from_monitor_struct function to unpack transaction variables from structure.
`ECC_out_MONITOR_STRUCT

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
// monitor BFM.  Data is passed using the ECC_out_monitor_struct.          
 virtual function void notify_transaction(input ECC_out_monitor_s ECC_out_monitor_struct);
 
 
    trans = new("trans");
    trans.from_monitor_struct(ECC_out_monitor_struct);
    trans.start_time = time_stamp;                                                          
    trans.end_time = $time;                                                                 
    time_stamp = trans.end_time;
 
    analyze(trans);                                                                         
  endfunction  

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

