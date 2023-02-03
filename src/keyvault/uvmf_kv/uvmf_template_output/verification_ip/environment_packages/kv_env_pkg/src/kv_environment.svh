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

class kv_environment  extends uvmf_environment_base #(
    .CONFIG_T( kv_env_configuration 
  ));
  `uvm_component_utils( kv_environment )


  qvip_ahb_lite_slave_environment #()  qvip_ahb_lite_slave_subenv;



  uvm_analysis_port #( mvc_sequence_item_base ) qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap [string];

  typedef kv_rst_agent  kv_rst_agent_t;
  kv_rst_agent_t kv_rst_agent;

  typedef kv_write_agent  kv_hmac_write_agent_t;
  kv_hmac_write_agent_t kv_hmac_write_agent;

  typedef kv_write_agent  kv_sha512_write_agent_t;
  kv_sha512_write_agent_t kv_sha512_write_agent;

  typedef kv_write_agent  kv_ecc_write_agent_t;
  kv_ecc_write_agent_t kv_ecc_write_agent;

  typedef kv_write_agent  kv_doe_write_agent_t;
  kv_doe_write_agent_t kv_doe_write_agent;

  typedef kv_read_agent  kv_hmac_key_read_agent_t;
  kv_hmac_key_read_agent_t kv_hmac_key_read_agent;

  typedef kv_read_agent  kv_hmac_block_read_agent_t;
  kv_hmac_block_read_agent_t kv_hmac_block_read_agent;

  typedef kv_read_agent  kv_sha512_block_read_agent_t;
  kv_sha512_block_read_agent_t kv_sha512_block_read_agent;

  typedef kv_read_agent  kv_ecc_privkey_read_agent_t;
  kv_ecc_privkey_read_agent_t kv_ecc_privkey_read_agent;

  typedef kv_read_agent  kv_ecc_seed_read_agent_t;
  kv_ecc_seed_read_agent_t kv_ecc_seed_read_agent;

  typedef kv_read_agent  kv_ecc_msg_read_agent_t;
  kv_ecc_msg_read_agent_t kv_ecc_msg_read_agent;




  typedef kv_predictor #(
                .CONFIG_T(CONFIG_T)
                ) kv_pred_t;
  kv_pred_t kv_pred;

  typedef uvmf_in_order_scoreboard #(.T(kv_read_transaction))  kv_sb_t;
  kv_sb_t kv_sb;

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
   typedef uvm_reg_predictor #(uvm_sequence_item) reg_predictor_t;
   reg_predictor_t    reg_predictor;


  typedef uvmf_virtual_sequencer_base #(.CONFIG_T(kv_env_configuration)) kv_vsqr_t;
  kv_vsqr_t vsqr;

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
    kv_rst_agent = kv_rst_agent_t::type_id::create("kv_rst_agent",this);
    kv_rst_agent.set_config(configuration.kv_rst_agent_config);
    kv_hmac_write_agent = kv_hmac_write_agent_t::type_id::create("kv_hmac_write_agent",this);
    kv_hmac_write_agent.set_config(configuration.kv_hmac_write_agent_config);
    kv_sha512_write_agent = kv_sha512_write_agent_t::type_id::create("kv_sha512_write_agent",this);
    kv_sha512_write_agent.set_config(configuration.kv_sha512_write_agent_config);
    kv_ecc_write_agent = kv_ecc_write_agent_t::type_id::create("kv_ecc_write_agent",this);
    kv_ecc_write_agent.set_config(configuration.kv_ecc_write_agent_config);
    kv_doe_write_agent = kv_doe_write_agent_t::type_id::create("kv_doe_write_agent",this);
    kv_doe_write_agent.set_config(configuration.kv_doe_write_agent_config);
    kv_hmac_key_read_agent = kv_hmac_key_read_agent_t::type_id::create("kv_hmac_key_read_agent",this);
    kv_hmac_key_read_agent.set_config(configuration.kv_hmac_key_read_agent_config);
    kv_hmac_block_read_agent = kv_hmac_block_read_agent_t::type_id::create("kv_hmac_block_read_agent",this);
    kv_hmac_block_read_agent.set_config(configuration.kv_hmac_block_read_agent_config);
    kv_sha512_block_read_agent = kv_sha512_block_read_agent_t::type_id::create("kv_sha512_block_read_agent",this);
    kv_sha512_block_read_agent.set_config(configuration.kv_sha512_block_read_agent_config);
    kv_ecc_privkey_read_agent = kv_ecc_privkey_read_agent_t::type_id::create("kv_ecc_privkey_read_agent",this);
    kv_ecc_privkey_read_agent.set_config(configuration.kv_ecc_privkey_read_agent_config);
    kv_ecc_seed_read_agent = kv_ecc_seed_read_agent_t::type_id::create("kv_ecc_seed_read_agent",this);
    kv_ecc_seed_read_agent.set_config(configuration.kv_ecc_seed_read_agent_config);
    kv_ecc_msg_read_agent = kv_ecc_msg_read_agent_t::type_id::create("kv_ecc_msg_read_agent",this);
    kv_ecc_msg_read_agent.set_config(configuration.kv_ecc_msg_read_agent_config);
    kv_pred = kv_pred_t::type_id::create("kv_pred",this);
    kv_pred.configuration = configuration;
    kv_sb = kv_sb_t::type_id::create("kv_sb",this);
// pragma uvmf custom reg_model_build_phase begin
  // Build register model predictor if prediction is enabled
  if (configuration.enable_reg_prediction) begin
    reg_predictor = reg_predictor_t::type_id::create("reg_predictor", this);
  end
// pragma uvmf custom reg_model_build_phase end

    vsqr = kv_vsqr_t::type_id::create("vsqr", this);
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
    kv_rst_agent.monitored_ap.connect(kv_pred.kv_rst_agent_ae);
    kv_pred.kv_sb_ap.connect(kv_sb.expected_analysis_export);
    kv_hmac_key_read_agent.monitored_ap.connect(kv_sb.actual_analysis_export);
    kv_hmac_block_read_agent.monitored_ap.connect(kv_sb.actual_analysis_export);
    kv_sha512_block_read_agent.monitored_ap.connect(kv_sb.actual_analysis_export);
    kv_ecc_privkey_read_agent.monitored_ap.connect(kv_sb.actual_analysis_export);
    kv_ecc_seed_read_agent.monitored_ap.connect(kv_sb.actual_analysis_export);
    kv_ecc_msg_read_agent.monitored_ap.connect(kv_sb.actual_analysis_export);
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap = qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.ap; 
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap["burst_transfer"].connect(kv_pred.ahb_slave_0_ae);
    if ( configuration.qvip_ahb_lite_slave_subenv_interface_activity[0] == ACTIVE )
       uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,configuration.qvip_ahb_lite_slave_subenv_interface_names[0],qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer  );
    // pragma uvmf custom reg_model_connect_phase begin
    // Create register model adapter if required
    if (configuration.enable_reg_prediction ||
        configuration.enable_reg_adaptation)
// UVMF_CHANGE_ME: QVIP_AGENT_USED_FOR_REG_MAP:
// Uncomment the construction of the reg adapter below.  This was commented so that the 
// generated code would compile and run as generated.  The uvm_reg_adapter is a virtual
// class so it can not be constructed.  Once the type is changed to a QVIP reg adapter
// type, it must be constructed.
      //reg_adapter = reg_adapter_t::type_id::create("reg_adapter");
    // Set sequencer and adapter in register model map
    if ((configuration.enable_reg_adaptation) && (qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer != null ))
      configuration.kv_rm.ahb_map.set_sequencer(qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer, reg_adapter);
    // Set map and adapter handles within uvm predictor
    if (configuration.enable_reg_prediction) begin
      reg_predictor.map     = configuration.kv_rm.ahb_map;
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
     configuration.kv_configuration_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

