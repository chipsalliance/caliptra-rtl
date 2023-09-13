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
// DESCRIPTION: Issue a reset in the soc_ifc environment
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_wdt_sequence_base extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


    `uvm_object_utils( soc_ifc_env_wdt_sequence_base )
  
      typedef soc_ifc_ctrl_sequence_base soc_ifc_ctrl_sequence_t;
      soc_ifc_ctrl_sequence_t soc_ifc_ctrl_seq;
  
    // caliptra_apb_user apb_user_obj;
  
    // typedef struct packed {
    //     bit              set_bootfsm_breakpoint;
    //     security_state_t security_state;
    // } ctrl_reset_seq_context_t;
  
    // rand uvm_reg_data_t uds_seed_rand      [12];
    // rand uvm_reg_data_t field_entropy_rand [32];
    // rand uvm_reg_data_t owner_pk_hash_rand [12];
    // rand uvm_reg_data_t key_manifest_pk_hash_rand [12];
    // rand uvm_reg_data_t idevid_cert_attr_rand [24];
    // rand uvm_reg_data_t soc_stepping_id_rand;
    // rand struct packed {
    //   bit uds;
    //   bit field_entropy;
    //   bit [0:11] key_manifest_pk_hash;
    //   bit [0:11] owner_pk_hash;
    //   bit soc_stepping_id;
    //   bit [0:23] idevid_cert_attr;
    //   bit lms_verify;
    // } fuses_to_set;
  
  
    //==========================================
    // Name:        new
    // Description: Constructor
    //==========================================
    function new(string name = "" );
      super.new(name);
      soc_ifc_ctrl_seq = soc_ifc_ctrl_sequence_t::type_id::create("soc_ifc_ctrl_seq");
        
      // Setup a User object to override PAUSER
    //   apb_user_obj = new();
  
    endfunction
  
  
    //==========================================
    // Name:        run_ctrl_seq
    // Description: Run low-level soc_ifc_ctrl sequence to wiggle gen input wires to let RT fw know which mode of WDT to enable
    //==========================================
    virtual task run_ctrl_seq();
      if ( configuration.soc_ifc_ctrl_agent_config.sequencer != null )
          soc_ifc_ctrl_seq.start(configuration.soc_ifc_ctrl_agent_config.sequencer);
      else
          `uvm_error("SOC_IFC_WDT", "soc_ifc_ctrl_agent_config.sequencer is null!")
  
    endtask
  
  
    
  
    //==========================================
    // Name:        pre_body
    // Description: Setup tasks to:
    //               - get a reg model handle
    //               - check for a valid responder handle
    //==========================================
    virtual task pre_body();
      super.pre_body();
      reg_model = configuration.soc_ifc_rm;
      if (soc_ifc_status_agent_rsp_seq == null)
          `uvm_fatal("SOC_IFC_WDT", "SOC_IFC ENV wdt sequence expected a handle to the soc_ifc status agent responder sequence (from bench-level sequence) but got null!")
    //   apb_user_obj.set_addr_user(reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_PAUSER[0].PAUSER.get_reset("HARD"));
    endtask
  
  
    //==========================================
    // Name:        body
    // Description: Run the main functionality
    //==========================================
    virtual task body();

  
      // Run ctrl seq
      run_ctrl_seq();
  
      
  
    endtask
  
  endclass
  
  