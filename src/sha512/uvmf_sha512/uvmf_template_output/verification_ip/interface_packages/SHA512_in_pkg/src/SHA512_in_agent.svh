//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: Protocol specific agent class definition
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class SHA512_in_agent #(
     int AHB_DATA_WIDTH = 32,
     int AHB_ADDR_WIDTH = 32,
     bit BYPASS_HSEL = 0
     )
 extends uvmf_parameterized_agent #(
                    .CONFIG_T(SHA512_in_configuration #(
                              .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                              .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                              .BYPASS_HSEL(BYPASS_HSEL)
                              )
),
                    .DRIVER_T(SHA512_in_driver #(
                              .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                              .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                              .BYPASS_HSEL(BYPASS_HSEL)
                              )
),
                    .MONITOR_T(SHA512_in_monitor #(
                               .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                               .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                               .BYPASS_HSEL(BYPASS_HSEL)
                               )
),
                    .COVERAGE_T(SHA512_in_transaction_coverage #(
                                .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                                .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                                .BYPASS_HSEL(BYPASS_HSEL)
                                )
),
                    .TRANS_T(SHA512_in_transaction #(
                             .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                             .BYPASS_HSEL(BYPASS_HSEL)
                             )
)
                    );

  `uvm_component_param_utils( SHA512_in_agent #(
                              AHB_DATA_WIDTH,
                              AHB_ADDR_WIDTH,
                              BYPASS_HSEL
                              )
)

// pragma uvmf custom class_item_additional begin
// pragma uvmf custom class_item_additional end

// ****************************************************************************
// FUNCTION : new()
// This function is the standard SystemVerilog constructor.
//
  function new( string name = "", uvm_component parent = null );
    super.new( name, parent );
  endfunction

// ****************************************************************************
  // FUNCTION: build_phase
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (configuration.active_passive == ACTIVE) begin
      // Place sequencer handle into configuration object
      // so that it may be retrieved from configuration 
      // rather than using uvm_config_db
      configuration.sequencer = this.sequencer;
    end
  endfunction
  
endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

