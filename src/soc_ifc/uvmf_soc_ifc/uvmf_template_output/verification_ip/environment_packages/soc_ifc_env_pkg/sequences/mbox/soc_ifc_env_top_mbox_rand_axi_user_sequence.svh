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
class soc_ifc_env_top_mbox_rand_axi_user_sequence extends soc_ifc_env_top_mbox_sequence_base;


  `uvm_object_utils( soc_ifc_env_top_mbox_rand_axi_user_sequence )

  soc_ifc_env_axi_user_init_sequence_t          soc_ifc_env_axi_user_init_seq;
  soc_ifc_env_mbox_rand_axi_user_sequence_t     soc_ifc_env_mbox_axi_user_seq;

  bit [aaxi_pkg::AAXI_AWUSER_WIDTH-1:0] mbox_valid_users [6];
  caliptra_axi_user axi_user_obj;

  extern virtual function      create_seqs();
  extern virtual function void connect_extra_soc_ifc_resp_seqs();
  extern virtual function      randomize_seqs();
  extern virtual task          start_seqs();

endclass

function soc_ifc_env_top_mbox_rand_axi_user_sequence::create_seqs();
    uvm_object obj;
    obj = soc_ifc_env_mbox_rand_axi_user_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
    if(!$cast(soc_ifc_env_mbox_seq,obj)) `uvm_fatal("SOC_IFC_TOP_MBOX_RAND_AXI_USER", "soc_ifc_env_top_mbox_rand_axi_user_sequence::create_seqs() - <seq_type>.create_object() failed")
    soc_ifc_env_cptra_handler_seq = soc_ifc_env_cptra_mbox_handler_sequence_t::type_id::create("soc_ifc_env_cptra_handler_seq");
    soc_ifc_env_axi_user_init_seq = soc_ifc_env_axi_user_init_sequence_t::type_id::create("soc_ifc_env_axi_user_init_seq");
endfunction

function void soc_ifc_env_top_mbox_rand_axi_user_sequence::connect_extra_soc_ifc_resp_seqs();
    soc_ifc_env_axi_user_init_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_rsp_seq;
endfunction

function soc_ifc_env_top_mbox_rand_axi_user_sequence::randomize_seqs();
    if(!soc_ifc_env_mbox_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rand_axi_user_sequence::body() - %s randomization failed", soc_ifc_env_mbox_seq.get_type_name()));
    if(!soc_ifc_env_cptra_handler_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rand_axi_user_sequence::body() - %s randomization failed", soc_ifc_env_cptra_handler_seq.get_type_name()));
    if(!soc_ifc_env_axi_user_init_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rand_axi_user_sequence::body() - %s randomization failed", soc_ifc_env_axi_user_init_seq.get_type_name()));
endfunction

task soc_ifc_env_top_mbox_rand_axi_user_sequence::start_seqs();
    bit mbox_valid_users_initialized = 1'b0;
    uvm_status_e sts;
    uvm_reg_data_t data;
    byte ii;

    axi_user_obj = new();
    axi_user_obj.set_addr_user(32'hFFFF_FFFF); // FIXME hardcoded value - where to get this from?

    for (ii=0; ii < 5; ii++) begin: AXI_USER_CHECK_LOOP
        reg_model.soc_ifc_reg_rm.CPTRA_MBOX_AXI_USER_LOCK[ii].read(sts, data, UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
        if (sts != UVM_IS_OK) `uvm_error("SOC_IFC_MBOX_TOP", $sformatf("Failed when reading CPTRA_AXI_USER_LOCK index %0d", ii))
        if (data[reg_model.soc_ifc_reg_rm.CPTRA_MBOX_AXI_USER_LOCK[ii].LOCK.get_lsb_pos()]) begin
            reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_AXI_USER[ii].read(sts, mbox_valid_users[ii], UVM_FRONTDOOR, reg_model.soc_ifc_AXI_map, this, .extension(axi_user_obj));
            if (sts != UVM_IS_OK) `uvm_error("SOC_IFC_MBOX_TOP", $sformatf("Failed when reading CPTRA_MBOX_VALID_AXI_USER index %0d", ii))
            mbox_valid_users_initialized = 1'b1;
        end
        else begin
            mbox_valid_users[ii] = reg_model.soc_ifc_reg_rm.CPTRA_MBOX_VALID_AXI_USER[ii].AXI_USER.get_reset();
        end
    end
    mbox_valid_users[5] = 32'hFFFF_FFFF; // FIXME hardcoded default valid AXI_USER

    if (!mbox_valid_users_initialized) begin
        soc_ifc_env_axi_user_init_seq.start(configuration.vsqr);
        mbox_valid_users_initialized = 1'b1;
        mbox_valid_users = {soc_ifc_env_axi_user_init_seq.mbox_valid_users, 32'hFFFF_FFFF}; // FIXME hardcoded
    end

    // Cast to the AXI_USER specialization of mailbox sequence to expose the mbox_valid_users member for override
    if(!$cast(soc_ifc_env_mbox_axi_user_seq,soc_ifc_env_mbox_seq)) `uvm_fatal("SOC_IFC_TOP_MBOX_RAND_AXI_USER", "soc_ifc_env_top_mbox_rand_axi_user_sequence::start_seqs() - cast to soc_ifc_env_mbox_axi_user_seq failed")
    soc_ifc_env_mbox_axi_user_seq.mbox_valid_users = mbox_valid_users;
    soc_ifc_env_mbox_axi_user_seq.mbox_valid_users_initialized = 1'b1;
    fork
        soc_ifc_env_mbox_axi_user_seq.start(configuration.vsqr);
        soc_ifc_env_cptra_handler_seq.start(configuration.vsqr);
    join
endtask
