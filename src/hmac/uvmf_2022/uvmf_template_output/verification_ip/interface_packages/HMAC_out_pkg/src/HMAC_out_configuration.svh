//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: This class contains all variables and functions used
//      to configure the HMAC_out agent and its bfm's.  It gets the
//      bfm's from the uvm_config_db for use by the agent.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class HMAC_out_configuration #(
      int AHB_DATA_WIDTH = 32,
      int AHB_ADDR_WIDTH = 32,
      int OUTPUT_TEXT_WIDTH = 384,
      bit BYPASS_HSEL = 0
      )
 extends uvmf_parameterized_agent_configuration_base #(
      .DRIVER_BFM_BIND_T(virtual HMAC_out_driver_bfm #(
                          .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                          .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                          .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
                          .BYPASS_HSEL(BYPASS_HSEL)
                          )
),
      .MONITOR_BFM_BIND_T( virtual HMAC_out_monitor_bfm #(
                          .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                          .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                          .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
                          .BYPASS_HSEL(BYPASS_HSEL)
                          )
));

  `uvm_object_param_utils( HMAC_out_configuration #(
                           AHB_DATA_WIDTH,
                           AHB_ADDR_WIDTH,
                           OUTPUT_TEXT_WIDTH,
                           BYPASS_HSEL
                           )
)


  // Sequencer handle populated by agent
  uvm_sequencer #(HMAC_out_transaction #(
       .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
       .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
       .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
       .BYPASS_HSEL(BYPASS_HSEL)
       )
 ) sequencer;

  //Constraints for the configuration variables:

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  covergroup HMAC_out_configuration_cg;
    // pragma uvmf custom covergroup begin
    option.auto_bin_max=1024;
    // pragma uvmf custom covergroup end
  endgroup

  //*******************************************************************
  //*******************************************************************
  // Structure used to pass configuration variables to monitor and driver BFM's.
  // Use to_struct function to pack variables into structure.
  // Use from_struct function to unpack variables from structure.
  // This structure is defined in HMAC_out_macros.svh
  `HMAC_out_CONFIGURATION_STRUCT
  HMAC_out_configuration_s HMAC_out_configuration_struct;
  //*******************************************************************
  // FUNCTION: to_struct()
  // This function packs variables into a HMAC_out_configuration_s
  // structure.  The function returns the handle to the HMAC_out_configuration_struct.
  // This function is defined in HMAC_out_macros.svh
  `HMAC_out_CONFIGURATION_TO_STRUCT_FUNCTION
  //*******************************************************************
  // FUNCTION: from_struct()
  // This function unpacks the struct provided as an argument into 
  // variables of this class.
  // This function is defined in HMAC_out_macros.svh
  `HMAC_out_CONFIGURATION_FROM_STRUCT_FUNCTION

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new( string name = "" );
    super.new( name );
    // Construct the covergroup for this configuration class 
    HMAC_out_configuration_cg = new;
  endfunction

  // ****************************************************************************
  // FUNCTION: post_randomize()
  // This function is automatically called after the randomize() function 
  // is executed.
  //
  function void post_randomize();
    super.post_randomize();
    HMAC_out_configuration_cg.sample();
  endfunction

  // ****************************************************************************
  // FUNCTION: initialize
  //                   This function causes the configuration to retrieve
  //                   its virtual interface handle from the uvm_config_db.
  //                   This function also makes itself available to its
  //                   agent through the uvm_config_db.
  //
  //                ARGUMENTS:
  //                   uvmf_active_passive_t activity:
  //                        This argument identifies the simulation level
  //                        as either BLOCK, CHIP, SIMULATION, etc.
  //
  //                   AGENT_PATH:
  //                        This argument identifies the path to this
  //                        configurations agent.  This configuration
  //                        makes itself available to the agent specified
  //                        by agent_path by placing itself into the
  //                        uvm_config_db.
  //
  //                   INTERFACE_NAME:
  //                        This argument identifies the string name of
  //                        this configurations BFM's.  This string
  //                        name is used to retrieve the driver and 
  //                        monitor BFM from the uvm_config_db.
  //
  virtual function void initialize(uvmf_active_passive_t activity,
                                            string agent_path,
                                            string interface_name);

    super.initialize( activity, agent_path, interface_name);
    // The covergroup is given the same name as the interface
    HMAC_out_configuration_cg.set_inst_name(interface_name);

    // This configuration places itself into the uvm_config_db for the agent, identified by the agent_path variable, to retrieve.  
    uvm_config_db #( HMAC_out_configuration  #(
                             .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                             .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
                             .BYPASS_HSEL(BYPASS_HSEL)
                             )

                    )::set( null ,agent_path,UVMF_AGENT_CONFIG, this );

    // This configuration also places itself in the config db using the same identifier used by the interface.  This allows users to access
    // configuration variables and the interface through the bfm api class rather than directly accessing the BFM.  This is useful for 
    // accessingthe BFM when using Veloce
    uvm_config_db #( HMAC_out_configuration  #(
                             .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                             .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
                             .BYPASS_HSEL(BYPASS_HSEL)
                             )

                    )::set( null ,UVMF_CONFIGURATIONS, interface_name, this );

    HMAC_out_configuration_cg.set_inst_name($sformatf("HMAC_out_configuration_cg_%s",get_full_name()));

// This code is to aid in debugging parameter mismatches between the BFM and its corresponding agent.
// Enable this debug by setting UVM_VERBOSITY to UVM_DEBUG
// Setting UVM_VERBOSITY to UVM_DEBUG causes all BFM's and all agents to display their parameter settings.
// All of the messages from this feature have a UVM messaging id value of "CFG"
// The transcript or run.log can be parsed to ensure BFM parameter settings match its corresponding agents parameter settings.
    `uvm_info("CFG", 
              $psprintf("The agent at '%s' is using interface named %s has the following parameters: AHB_DATA_WIDTH=%x AHB_ADDR_WIDTH=%x OUTPUT_TEXT_WIDTH=%x BYPASS_HSEL=%x ", agent_path, interface_name, AHB_DATA_WIDTH ,AHB_ADDR_WIDTH ,OUTPUT_TEXT_WIDTH ,BYPASS_HSEL ),
              UVM_DEBUG)

    // pragma uvmf custom initialize begin
    // This controls whether or not the agent returns a transaction handle in the driver when calling 
    // item_done() back into the sequencer or not. If set to 1, a transaction is sent back which means
    // the sequence on the other end must use the get_response() part of the driver/sequence API. If 
    // this doesn't occur, there will eventually be response_queue overflow errors during the test.
    return_transaction_response = 1'b0;

    // pragma uvmf custom initialize end

  endfunction

  // ****************************************************************************
  // TASK: wait_for_reset
  // *[Required]*  Blocks until reset is released.  The wait_for_reset operation is performed
  // by a task in the monitor bfm.
  virtual task wait_for_reset();
    monitor_bfm.wait_for_reset();
  endtask

  // ****************************************************************************
  // TASK: wait_for_num_clocks
  // *[Required]* Blocks until specified number of clocks have elapsed. The wait_for_num_clocks
  // operation is performed by a task in the monitor bfm.
  virtual task wait_for_num_clocks(int clocks);
    monitor_bfm.wait_for_num_clocks(clocks);
  endtask

  // ****************************************************************************
  // FUNCTION : convert2string()
  // This function is used to convert variables in this class into a string for log messaging.
  // 
  virtual function string convert2string ();
    // pragma uvmf custom convert2string begin
    return $sformatf("");
    // pragma uvmf custom convert2string end
  endfunction

  // ****************************************************************************
  // FUNCTION: get_sequencer
  function uvm_sequencer #(HMAC_out_transaction#(
       .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
       .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
       .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
       .BYPASS_HSEL(BYPASS_HSEL)
       )
) get_sequencer();
    return sequencer;
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

