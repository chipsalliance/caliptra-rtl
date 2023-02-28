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

//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: Sequence to initiate (and respond) to mailbox command
//              "TOP" sequence because it invokes lower level env sequences
//              to facilitate the uC/SoC sides of mailbox command handling
//              and this sequence defines the whole mailbox flow.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_top_mbox_rand_pauser_sequence extends soc_ifc_env_top_mbox_sequence_base;


  `uvm_object_utils( soc_ifc_env_top_mbox_rand_pauser_sequence )

  soc_ifc_env_pauser_init_sequence_t          soc_ifc_env_pauser_init_seq;
  soc_ifc_env_mbox_rand_pauser_sequence_t     soc_ifc_env_mbox_pauser_seq;

  bit [4:0] [apb5_master_0_params::PAUSER_WIDTH-1:0] mbox_valid_users;

  extern virtual function      create_seqs();
  extern virtual function void connect_extra_soc_ifc_resp_seqs();
  extern virtual function      randomize_seqs();
  extern virtual task          start_seqs();

endclass

function soc_ifc_env_top_mbox_rand_pauser_sequence::create_seqs();
    uvm_object obj;
    obj = soc_ifc_env_mbox_rand_pauser_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
    if(!$cast(soc_ifc_env_mbox_seq,obj)) `uvm_fatal("SOC_IFC_TOP_MBOX_RAND_PAUSER", "soc_ifc_env_top_mbox_rand_pauser_sequence::create_seqs() - <seq_type>.create_object() failed")
    soc_ifc_env_cptra_handler_seq = soc_ifc_env_cptra_mbox_handler_sequence_t::type_id::create("soc_ifc_env_cptra_handler_seq");
    soc_ifc_env_pauser_init_seq = soc_ifc_env_pauser_init_sequence_t::type_id::create("soc_ifc_env_pauser_init_seq");
endfunction

function void soc_ifc_env_top_mbox_rand_pauser_sequence::connect_extra_soc_ifc_resp_seqs();
    soc_ifc_env_pauser_init_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_rsp_seq;
endfunction

function soc_ifc_env_top_mbox_rand_pauser_sequence::randomize_seqs();
    if(!soc_ifc_env_mbox_seq.randomize() with { mbox_op_rand.dlen <= 32'h0000_1000;
                                                mbox_op_rand.dlen >= 32'h0000_0200;
                                                mbox_resp_expected_dlen <= 32'h0000_0400;
                                                mbox_op_rand.cmd.cmd_s.resp_reqd -> mbox_resp_expected_dlen >= 32'h0000_0080; })
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rand_pauser_sequence::body() - %s randomization failed", soc_ifc_env_mbox_seq.get_type_name()));
    if(!soc_ifc_env_cptra_handler_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rand_pauser_sequence::body() - %s randomization failed", soc_ifc_env_cptra_handler_seq.get_type_name()));
    if(!soc_ifc_env_pauser_init_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rand_pauser_sequence::body() - %s randomization failed", soc_ifc_env_pauser_init_seq.get_type_name()));
endfunction

task soc_ifc_env_top_mbox_rand_pauser_sequence::start_seqs();
    soc_ifc_env_pauser_init_seq.start(configuration.vsqr);
    // Cast to the PAUSER specialization of mailbox sequence to expose the mbox_valid_users member for override
    if(!$cast(soc_ifc_env_mbox_pauser_seq,soc_ifc_env_mbox_seq)) `uvm_fatal("SOC_IFC_TOP_MBOX_RAND_PAUSER", "soc_ifc_env_top_mbox_rand_pauser_sequence::start_seqs() - cast to soc_ifc_env_mbox_pauser_seq failed")
    soc_ifc_env_mbox_pauser_seq.mbox_valid_users = soc_ifc_env_pauser_init_seq.mbox_valid_users;
    fork
        soc_ifc_env_mbox_pauser_seq.start(configuration.vsqr);
        soc_ifc_env_cptra_handler_seq.start(configuration.vsqr);
    join
endtask
