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

class soc_ifc_environment  extends uvmf_environment_base #(
    .CONFIG_T( soc_ifc_env_configuration 
  ));
  `uvm_component_utils( soc_ifc_environment )


  qvip_ahb_lite_slave_environment #()  qvip_ahb_lite_slave_subenv;

  qvip_apb5_slave_environment #()  qvip_apb5_slave_subenv;



  uvm_analysis_port #( mvc_sequence_item_base ) qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap [string];
  uvm_analysis_port #( mvc_sequence_item_base ) qvip_apb5_slave_subenv_apb5_master_0_ap [string];

  typedef soc_ifc_ctrl_agent  soc_ifc_ctrl_agent_t;
  soc_ifc_ctrl_agent_t soc_ifc_ctrl_agent;

  typedef cptra_ctrl_agent  cptra_ctrl_agent_t;
  cptra_ctrl_agent_t cptra_ctrl_agent;

  typedef soc_ifc_status_agent  soc_ifc_status_agent_t;
  soc_ifc_status_agent_t soc_ifc_status_agent;

  typedef cptra_status_agent  cptra_status_agent_t;
  cptra_status_agent_t cptra_status_agent;




  typedef soc_ifc_predictor #(
                .CONFIG_T(CONFIG_T)
                )
 soc_ifc_pred_t;
  soc_ifc_pred_t soc_ifc_pred;
  typedef soc_ifc_scoreboard #(
                .CONFIG_T(CONFIG_T)
                )
 soc_ifc_sb_t;
  soc_ifc_sb_t soc_ifc_sb;


// UVMF_CHANGE_ME: QVIP_AGENT_USED_FOR_REG_MAP: 
// Identify the UVM reg adapter in the QVIP installation for the protocol agent.
// Change the typedef below to reflect the reg adapter class type and any parameters.
// Be sure to modify the envioronment package to import the QVIP protocol package 
// that contains the selected adapter.
   // Instantiate register model adapter and predictor
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

   typedef apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT,
                                        apb5_master_0_params::APB3_PADDR_BIT_WIDTH,
                                        apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,
                                        apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_reg_transfer_t;

   typedef caliptra_reg2apb_adapter #(apb_reg_transfer_t,
                             apb5_master_0_params::APB3_SLAVE_COUNT,
                             apb5_master_0_params::APB3_PADDR_BIT_WIDTH,
                             apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,
                             apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_reg_adapter_t;

   ahb_reg_adapter_t    ahb_reg_adapter;
   apb_reg_adapter_t    apb_reg_adapter;

   typedef ahb_reg_predictor #(ahb_reg_transfer_t,
                               ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                               ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                               ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                               ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                               ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                               ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_reg_predictor_t;

   typedef apb_reg_predictor #(apb_reg_transfer_t,
                               apb5_master_0_params::APB3_SLAVE_COUNT,
                               apb5_master_0_params::APB3_PADDR_BIT_WIDTH,
                               apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,
                               apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_reg_predictor_t;

   ahb_reg_predictor_t    ahb_reg_predictor;
   apb_reg_predictor_t    apb_reg_predictor;


  typedef uvmf_virtual_sequencer_base #(.CONFIG_T(soc_ifc_env_configuration)) soc_ifc_vsqr_t;
  soc_ifc_vsqr_t vsqr;

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
    qvip_apb5_slave_subenv = qvip_apb5_slave_environment#()::type_id::create("qvip_apb5_slave_subenv",this);
    qvip_apb5_slave_subenv.set_config(configuration.qvip_apb5_slave_subenv_config);
    soc_ifc_ctrl_agent = soc_ifc_ctrl_agent_t::type_id::create("soc_ifc_ctrl_agent",this);
    soc_ifc_ctrl_agent.set_config(configuration.soc_ifc_ctrl_agent_config);
    cptra_ctrl_agent = cptra_ctrl_agent_t::type_id::create("cptra_ctrl_agent",this);
    cptra_ctrl_agent.set_config(configuration.cptra_ctrl_agent_config);
    soc_ifc_status_agent = soc_ifc_status_agent_t::type_id::create("soc_ifc_status_agent",this);
    soc_ifc_status_agent.set_config(configuration.soc_ifc_status_agent_config);
    cptra_status_agent = cptra_status_agent_t::type_id::create("cptra_status_agent",this);
    cptra_status_agent.set_config(configuration.cptra_status_agent_config);
    soc_ifc_pred = soc_ifc_pred_t::type_id::create("soc_ifc_pred",this);
    soc_ifc_pred.configuration = configuration;
    soc_ifc_sb = soc_ifc_sb_t::type_id::create("soc_ifc_sb",this);
    soc_ifc_sb.configuration = configuration;
    soc_ifc_sb.enable_wait_for_scoreboard_empty();
// pragma uvmf custom reg_model_build_phase begin
  // Build register model predictor if prediction is enabled
  if (configuration.enable_reg_prediction) begin
    ahb_reg_predictor = ahb_reg_predictor_t::type_id::create("ahb_reg_predictor", this);
    apb_reg_predictor = apb_reg_predictor_t::type_id::create("apb_reg_predictor", this);
  end
// pragma uvmf custom reg_model_build_phase end

    vsqr = soc_ifc_vsqr_t::type_id::create("vsqr", this);
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
    soc_ifc_ctrl_agent.monitored_ap.connect(soc_ifc_pred.soc_ifc_ctrl_agent_ae);
    cptra_ctrl_agent.monitored_ap.connect(soc_ifc_pred.cptra_ctrl_agent_ae);
    soc_ifc_pred.soc_ifc_sb_ap.connect(soc_ifc_sb.expected_analysis_export);
    soc_ifc_pred.cptra_sb_ap.connect(soc_ifc_sb.expected_cptra_analysis_export);
    soc_ifc_pred.soc_ifc_sb_ahb_ap.connect(soc_ifc_sb.expected_ahb_analysis_export);
    soc_ifc_pred.soc_ifc_sb_apb_ap.connect(soc_ifc_sb.expected_apb_analysis_export);
    soc_ifc_status_agent.monitored_ap.connect(soc_ifc_sb.actual_analysis_export);
    cptra_status_agent.monitored_ap.connect(soc_ifc_sb.actual_cptra_analysis_export);
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap = qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.ap; 
    qvip_apb5_slave_subenv_apb5_master_0_ap = qvip_apb5_slave_subenv.apb5_master_0.ap; 
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap["burst_transfer"].connect(soc_ifc_pred.ahb_slave_0_ae);
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap["burst_transfer_sb"].connect(soc_ifc_sb.actual_ahb_analysis_export);
    qvip_apb5_slave_subenv_apb5_master_0_ap["trans_ap"].connect(soc_ifc_pred.apb5_slave_0_ae);
    qvip_apb5_slave_subenv_apb5_master_0_ap["trans_ap_sb"].connect(soc_ifc_sb.actual_apb_analysis_export);
    if ( configuration.qvip_ahb_lite_slave_subenv_interface_activity[0] == ACTIVE )
       uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,configuration.qvip_ahb_lite_slave_subenv_interface_names[0],qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer  );
    if ( configuration.qvip_apb5_slave_subenv_interface_activity[0] == ACTIVE )
       uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,configuration.qvip_apb5_slave_subenv_interface_names[0],qvip_apb5_slave_subenv.apb5_master_0.m_sequencer  );
    // pragma uvmf custom reg_model_connect_phase begin
    // Create register model adapter if required
    if (configuration.enable_reg_prediction ||
        configuration.enable_reg_adaptation) begin
      ahb_reg_adapter = ahb_reg_adapter_t::type_id::create("reg2ahb_adapter");
      ahb_reg_adapter.en_n_bits = 1; // This is to allow the adapter to generate addresses
                                     // that are not aligned to 64-bit width (the native AHB interface width)
      apb_reg_adapter = apb_reg_adapter_t::type_id::create("caliptra_reg2apb_adapter");
      configuration.apb_reg_adapter_h = apb_reg_adapter;
    end
    // Set sequencer and adapter in register model map
    if ((configuration.enable_reg_adaptation) && (qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer != null ))
      configuration.soc_ifc_rm.soc_ifc_AHB_map.set_sequencer(qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer, ahb_reg_adapter);
    if ((configuration.enable_reg_adaptation) && (qvip_apb5_slave_subenv.apb5_master_0.m_sequencer != null ))
      configuration.soc_ifc_rm.soc_ifc_APB_map.set_sequencer(qvip_apb5_slave_subenv.apb5_master_0.m_sequencer, apb_reg_adapter);
    // Set map and adapter handles within uvm predictor
    if (configuration.enable_reg_prediction) begin
      ahb_reg_predictor.map     = configuration.soc_ifc_rm.soc_ifc_AHB_map;
      apb_reg_predictor.map     = configuration.soc_ifc_rm.soc_ifc_APB_map;
      ahb_reg_predictor.adapter = ahb_reg_adapter;
      apb_reg_predictor.adapter = apb_reg_adapter;
      configuration.soc_ifc_rm.soc_ifc_AHB_map.set_auto_predict(1);
      configuration.soc_ifc_rm.soc_ifc_APB_map.set_auto_predict(1);
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
      qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.ap["burst_transfer"].connect(ahb_reg_predictor.bus_in);
      qvip_apb5_slave_subenv.apb5_master_0.ap["trans_ap"].connect(apb_reg_predictor.bus_in);
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
     configuration.soc_ifc_configuration_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

