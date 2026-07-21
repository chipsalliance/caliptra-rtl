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

class HMAC256_environment  extends uvmf_environment_base #(
    .CONFIG_T( HMAC256_env_configuration 
  ));
  `uvm_component_utils( HMAC256_environment )


  qvip_ahb_lite_slave_environment #()  qvip_ahb_lite_slave_subenv;



  uvm_analysis_port #( mvc_sequence_item_base ) qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap [string];

  typedef HMAC256_rst_agent  hmac256_rst_agent_t;
  hmac256_rst_agent_t HMAC256_rst_agent;




  typedef HMAC256_predictor #(
                .CONFIG_T(CONFIG_T)
                )
 hmac256_pred_t;
  hmac256_pred_t hmac256_pred;
  typedef HMAC256_scoreboard #(
                .CONFIG_T(CONFIG_T)
                )
 hmac256_sb_t;
  hmac256_sb_t hmac256_sb;


// REG ADAPTER: use the concrete reg2ahb_adapter from the QVIP AHB package
// (matches the adams-bridge / mldsa pattern). The default uvm_reg_adapter is
// abstract and cannot be constructed; without a concrete adapter the reg
// model emits "[REG_NO_ADAPT]" warnings and our RAL writes never reach the
// AHB sequencer.
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
                             ahb_lite_slave_0_params::AHB_RDATA_WIDTH) reg_adapter_t;
   reg_adapter_t    reg_adapter;
   typedef uvm_reg_predictor #(ahb_reg_transfer_t) reg_predictor_t;
   reg_predictor_t    reg_predictor;


  typedef uvmf_virtual_sequencer_base #(.CONFIG_T(HMAC256_env_configuration)) hmac256_vsqr_t;
  hmac256_vsqr_t vsqr;

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
// FUNCTION: build_phase()
// This function builds all components within this environment.
//
  virtual function void build_phase(uvm_phase phase);
// pragma uvmf custom build_phase_pre_super begin
// pragma uvmf custom build_phase_pre_super end
    super.build_phase(phase);
    qvip_ahb_lite_slave_subenv = qvip_ahb_lite_slave_environment#()::type_id::create("qvip_ahb_lite_slave_subenv",this);
    qvip_ahb_lite_slave_subenv.set_config(configuration.qvip_ahb_lite_slave_subenv_config);
    HMAC256_rst_agent = hmac256_rst_agent_t::type_id::create("HMAC256_rst_agent",this);
    HMAC256_rst_agent.set_config(configuration.hmac256_rst_agent_config);
    hmac256_pred = hmac256_pred_t::type_id::create("hmac256_pred",this);
    hmac256_pred.configuration = configuration;
    hmac256_sb = hmac256_sb_t::type_id::create("hmac256_sb",this);
    hmac256_sb.configuration = configuration;
// pragma uvmf custom reg_model_build_phase begin
  // Build register model predictor if prediction is enabled
  if (configuration.enable_reg_prediction) begin
    reg_predictor = reg_predictor_t::type_id::create("reg_predictor", this);
  end
// pragma uvmf custom reg_model_build_phase end

    vsqr = hmac256_vsqr_t::type_id::create("vsqr", this);
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
    HMAC256_rst_agent.monitored_ap.connect(hmac256_pred.hmac256_rst_agent_ae);
    hmac256_pred.hmac256_sb_ahb_ap.connect(hmac256_sb.expected_ahb_analysis_export);
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap = qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.ap; 
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap["burst_transfer"].connect(hmac256_pred.ahb_slave_0_ae);
    if ( configuration.qvip_ahb_lite_slave_subenv_interface_activity[0] == ACTIVE )
       uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,configuration.qvip_ahb_lite_slave_subenv_interface_names[0],qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer  );
    // pragma uvmf custom reg_model_connect_phase begin
    // Create register model adapter if required
    if (configuration.enable_reg_prediction ||
        configuration.enable_reg_adaptation) begin
      // Construct the concrete AHB reg adapter (mldsa pattern). Without
      // this `reg_adapter` stays null and `set_sequencer` below installs
      // a null adapter, leading to "[REG_NO_ADAPT]" + abstract uvm_reg_item
      // traffic that never reaches the bus.
      reg_adapter = reg_adapter_t::type_id::create("reg2ahb_adapter");
      reg_adapter.en_n_bits = 1; // allow byte/word accesses, not just 64-bit
    end
    // Set sequencer and adapter in register model map
    if ((configuration.enable_reg_adaptation) && (qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer != null ))
      configuration.hmac256_rm.ahb_map.set_sequencer(qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer, reg_adapter);
    // Set map and adapter handles within uvm predictor
    if (configuration.enable_reg_prediction) begin
      reg_predictor.map     = configuration.hmac256_rm.ahb_map;
      reg_predictor.adapter = reg_adapter;
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
     configuration.hmac256_configuration_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

