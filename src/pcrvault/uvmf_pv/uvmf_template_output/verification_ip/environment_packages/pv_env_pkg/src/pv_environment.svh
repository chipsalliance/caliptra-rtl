//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: This environment contains all agents, predictors and
// scoreboards required for the block level design.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class pv_environment  extends uvmf_environment_base #(
    .CONFIG_T( pv_env_configuration 
  ));
  `uvm_component_utils( pv_environment )


  qvip_ahb_lite_slave_environment #()  qvip_ahb_lite_slave_subenv;



  uvm_analysis_port #( mvc_sequence_item_base ) qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap [string];

  typedef pv_rst_agent  pv_rst_agent_t;
  pv_rst_agent_t pv_rst_agent;

  typedef pv_write_agent  pv_sha512_write_agent_t;
  pv_sha512_write_agent_t pv_sha512_write_agent;

  typedef pv_read_agent  pv_sha512_block_read_agent_t;
  pv_sha512_block_read_agent_t pv_sha512_block_read_agent;




  typedef pv_predictor #(
                .CONFIG_T(CONFIG_T)
                )
 pv_pred_t;
  pv_pred_t pv_pred;
  typedef pv_scoreboard #(
                .CONFIG_T(CONFIG_T)
                )
 pv_sb_t;
  pv_sb_t pv_sb;


// UVMF_CHANGE_ME: QVIP_AGENT_USED_FOR_REG_MAP: 
// Identify the UVM reg adapter in the QVIP installation for the protocol agent.
// Change the typedef below to reflect the reg adapter class type and any parameters.
// Be sure to modify the envioronment package to import the QVIP protocol package 
// that contains the selected adapter.
   // Instantiate register model adapter and predictor
   typedef uvm_reg_adapter    reg_adapter_t;
   reg_adapter_t    reg_adapter;
// UVMF_CHANGE_ME: QVIP_AGENT_USED_FOR_REG_MAP:
// Identify the sequence_item type, including any parameters, used by the reg adapter
// type specified above.  Parameterize the uvm_reg_predictor to use this sequence item
// type, including any parameters of the sequence item.
  //  typedef uvm_reg_predictor #(uvm_sequence_item) reg_predictor_t;
  //  reg_predictor_t    reg_predictor;
   typedef pv_reg_predictor #(pv_write_transaction) write_reg_predictor_t;
   write_reg_predictor_t sha512_write_reg_predictor;

   typedef pv_reg_predictor #(pv_read_transaction) read_reg_predictor_t;
   read_reg_predictor_t sha512_block_read_reg_predictor;


  typedef uvmf_virtual_sequencer_base #(.CONFIG_T(pv_env_configuration)) pv_vsqr_t;
  pv_vsqr_t vsqr;

  // pragma uvmf custom class_item_additional begin
  typedef ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
  ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
  ahb_lite_slave_0_params::AHB_NUM_SLAVES,
  ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
  ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
  ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_reg_transfer_t;

  typedef reg2ahb_adapter #(ahb_reg_transfer_t,
  ahb_lite_slave_0_params::AHB_NUM_MASTERS,
  ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
  ahb_lite_slave_0_params::AHB_NUM_SLAVES,
  ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
  ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
  ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_reg_adapter_t;
  
  ahb_reg_adapter_t    ahb_reg_adapter;
  
  typedef ahb_reg_predictor #(ahb_reg_transfer_t,
  ahb_lite_slave_0_params::AHB_NUM_MASTERS,
  ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
  ahb_lite_slave_0_params::AHB_NUM_SLAVES,
  ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
  ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
  ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_reg_predictor_t;
  
  //ahb_reg_predictor_t    ahb_reg_predictor;

  typedef pv_ahb_reg_predictor #(ahb_reg_transfer_t,
  ahb_lite_slave_0_params::AHB_NUM_MASTERS,
  ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
  ahb_lite_slave_0_params::AHB_NUM_SLAVES,
  ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
  ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
  ahb_lite_slave_0_params::AHB_RDATA_WIDTH) pv_ahb_reg_predictor_t;

  pv_ahb_reg_predictor_t    ahb_reg_predictor;
  
  typedef pv_write2reg_adapter write_reg_adapter_t;
  write_reg_adapter_t pv_sha512_write_reg_adapter;
  
  typedef pv_read2reg_adapter read_reg_adapter_t;
  read_reg_adapter_t pv_sha512_block_read_reg_adapter;
  
  // pragma uvmf custom class_item_additional end
 
// ****************************************************************************
// FUNCTION : new()
// This function is the standard SystemVerilog constructor.
//
  function new( string name = "", uvm_component parent = null );
    super.new( name, parent );
  endfunction

// ****************************************************************************
// FUNCTION: build_phase()
// This function builds all components within this environment.
//
  virtual function void build_phase(uvm_phase phase);
// pragma uvmf custom build_phase_pre_super begin
// pragma uvmf custom build_phase_pre_super end
    super.build_phase(phase);
    qvip_ahb_lite_slave_subenv = qvip_ahb_lite_slave_environment#()::type_id::create("qvip_ahb_lite_slave_subenv",this);
    qvip_ahb_lite_slave_subenv.set_config(configuration.qvip_ahb_lite_slave_subenv_config);
    pv_rst_agent = pv_rst_agent_t::type_id::create("pv_rst_agent",this);
    pv_rst_agent.set_config(configuration.pv_rst_agent_config);
    pv_sha512_write_agent = pv_sha512_write_agent_t::type_id::create("pv_sha512_write_agent",this);
    pv_sha512_write_agent.set_config(configuration.pv_sha512_write_agent_config);
    pv_sha512_block_read_agent = pv_sha512_block_read_agent_t::type_id::create("pv_sha512_block_read_agent",this);
    pv_sha512_block_read_agent.set_config(configuration.pv_sha512_block_read_agent_config);
    pv_pred = pv_pred_t::type_id::create("pv_pred",this);
    pv_pred.configuration = configuration;
    pv_sb = pv_sb_t::type_id::create("pv_sb",this);
    pv_sb.configuration = configuration;
// pragma uvmf custom reg_model_build_phase begin
  // Build register model predictor if prediction is enabled
  if (configuration.enable_reg_prediction) begin
    sha512_write_reg_predictor  = write_reg_predictor_t::type_id::create("sha512_write_reg_predictor", this);
    sha512_block_read_reg_predictor = read_reg_predictor_t::type_id::create("sha512_block_read_reg_predictor", this);
    ahb_reg_predictor = pv_ahb_reg_predictor_t::type_id::create("ahb_reg_predictor", this);
  end
// pragma uvmf custom reg_model_build_phase end

    vsqr = pv_vsqr_t::type_id::create("vsqr", this);
    vsqr.set_config(configuration);
    configuration.set_vsqr(vsqr);

    // pragma uvmf custom build_phase begin
    // pragma uvmf custom build_phase end
  endfunction

// ****************************************************************************
// FUNCTION: connect_phase()
// This function makes all connections within this environment.  Connections
// typically inclue agent to predictor, predictor to scoreboard and scoreboard
// to agent.
//
  virtual function void connect_phase(uvm_phase phase);
// pragma uvmf custom connect_phase_pre_super begin
// pragma uvmf custom connect_phase_pre_super end
    super.connect_phase(phase);
    pv_rst_agent.monitored_ap.connect(pv_pred.pv_rst_agent_ae);
    
    pv_sha512_write_agent.monitored_ap.connect(pv_pred.pv_sha512_write_agent_ae);
    pv_sha512_block_read_agent.monitored_ap.connect(pv_pred.pv_sha512_block_read_agent_ae);

    pv_sha512_write_agent.monitored_ap.connect(pv_sb.actual_sha512_write_analysis_export);
    pv_sha512_block_read_agent.monitored_ap.connect(pv_sb.actual_sha512_block_read_analysis_export);

    pv_pred.pv_sha512_write_sb_ap.connect(pv_sb.expected_sha512_write_analysis_export);
    pv_pred.pv_sha512_block_read_sb_ap.connect(pv_sb.expected_sha512_block_read_analysis_export);
    
    
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap = qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.ap; 
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap["burst_transfer"].connect(pv_pred.ahb_slave_0_ae);
    
    if ( configuration.qvip_ahb_lite_slave_subenv_interface_activity[0] == ACTIVE )
       uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,configuration.qvip_ahb_lite_slave_subenv_interface_names[0],qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer  );
    // pragma uvmf custom reg_model_connect_phase begin
    // Create register model adapter if required
    if (configuration.enable_reg_prediction ||
        configuration.enable_reg_adaptation) begin

        ahb_reg_adapter = ahb_reg_adapter_t::type_id::create("reg2ahb_adapter");
        ahb_reg_adapter.en_n_bits = 1; // This is to allow the adapter to generate addresses
        // that are not aligned to 64-bit width (the native AHB interface width)

        pv_sha512_write_reg_adapter       = write_reg_adapter_t::type_id::create("pv_write2reg_adapter");
        pv_sha512_block_read_reg_adapter  = read_reg_adapter_t::type_id::create("pv_read2reg_adapter");

    end
// UVMF_CHANGE_ME: QVIP_AGENT_USED_FOR_REG_MAP:
// Uncomment the construction of the reg adapter below.  This was commented so that the 
// generated code would compile and run as generated.  The uvm_reg_adapter is a virtual
// class so it can not be constructed.  Once the type is changed to a QVIP reg adapter
// type, it must be constructed.
      //reg_adapter = reg_adapter_t::type_id::create("reg_adapter");
    // Set sequencer and adapter in register model map
    if ((configuration.enable_reg_adaptation) && (qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer != null ))
      configuration.pv_rm.pv_AHB_map.set_sequencer(qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer, ahb_reg_adapter);
    
    if (configuration.enable_reg_adaptation) begin

      //Write map
      if (pv_sha512_write_agent.sequencer != null)
        configuration.pv_rm.pv_sha512_write_map.set_sequencer(pv_sha512_write_agent.sequencer, pv_sha512_write_reg_adapter);
      //Read map
      if (pv_sha512_block_read_agent.sequencer != null)
        configuration.pv_rm.pv_sha512_block_read_map.set_sequencer(pv_sha512_block_read_agent.sequencer, pv_sha512_block_read_reg_adapter);

    end
    // Set map and adapter handles within uvm predictor
    if (configuration.enable_reg_prediction) begin
      ahb_reg_predictor.map     = configuration.pv_rm.pv_AHB_map;
      ahb_reg_predictor.adapter = ahb_reg_adapter;

      sha512_write_reg_predictor.map = configuration.pv_rm.pv_sha512_write_map;
      sha512_write_reg_predictor.adapter = pv_sha512_write_reg_adapter;

      sha512_block_read_reg_predictor.map = configuration.pv_rm.pv_sha512_block_read_map;
      sha512_block_read_reg_predictor.adapter = pv_sha512_block_read_reg_adapter;
      
      // The connection between the agent analysis_port and uvm_reg_predictor 
      // analysis_export could cause problems due to a uvm register package bug,
      // if this environment is used as a sub-environment at a higher level.
      // The uvm register package does not construct sub-maps within register
      // sub blocks.  While the connection below succeeds, the execution of the
      // write method associated with the analysis_export fails.  It fails because
      // the write method executes the get_reg_by_offset method of the register
      // map, which is null because of the uvm register package bug.
      // The call works when operating at block level because the uvm register 
      // package constructs the top level register map.  The call fails when the 
      // register map associated with this environment is a sub-map.  Construction
      // of the sub-maps must be done manually.
      //qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.monitored_ap.connect(reg_predictor.bus_in);

      //Bus connections:
      qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.ap["burst_transfer"].connect(ahb_reg_predictor.bus_in); //TODO burst transfer?

      pv_sha512_write_agent.monitored_ap.connect(sha512_write_reg_predictor.bus_in);

      pv_sha512_block_read_agent.monitored_ap.connect(sha512_block_read_reg_predictor.bus_in);
    end
    // pragma uvmf custom reg_model_connect_phase end
  endfunction

// ****************************************************************************
// FUNCTION: end_of_simulation_phase()
// This function is executed just prior to executing run_phase.  This function
// was added to the environment to sample environment configuration settings
// just before the simulation exits time 0.  The configuration structure is 
// randomized in the build phase before the environment structure is constructed.
// Configuration variables can be customized after randomization in the build_phase
// of the extended test.
// If a sequence modifies values in the configuration structure then the sequence is
// responsible for sampling the covergroup in the configuration if required.
//
  virtual function void start_of_simulation_phase(uvm_phase phase);
     configuration.pv_configuration_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

