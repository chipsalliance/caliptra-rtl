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
// DESCRIPTION: "TOP" level sequence provides a command and response flow
//              that executes a mailbox command and injects a reset randomly
//              during the operation.
//              This is facilitated by running the mailbox flow
//              and reset in a fork.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_top_mbox_rst_sequence extends soc_ifc_env_top_mbox_sequence_base;


  `uvm_object_utils( soc_ifc_env_top_mbox_rst_sequence )

  soc_ifc_env_reset_sequence_base_t     soc_ifc_env_rst_seq;
  soc_ifc_env_cptra_rst_wait_sequence_t soc_ifc_env_cptra_rst_wait_seq;

  extern virtual function      create_seqs();
  extern virtual function void connect_extra_soc_ifc_resp_seqs();
  extern virtual function void connect_extra_cptra_resp_seqs();
  extern virtual function      randomize_seqs();
  extern virtual task          start_seqs();

endclass

function soc_ifc_env_top_mbox_rst_sequence::create_seqs();
    uvm_object obj;
    obj = soc_ifc_env_mbox_sequence_base_t::get_type().create_object("soc_ifc_env_mbox_seq");
    if(!$cast(soc_ifc_env_mbox_seq,obj)) `uvm_fatal("SOC_IFC_TOP_MBOX_RST", "soc_ifc_env_top_mbox_rst_sequence::create_seqs() - <seq_type>.create_object() failed")
    soc_ifc_env_rst_seq             = soc_ifc_env_reset_sequence_base_t::type_id::create("soc_ifc_env_rst_seq");
    soc_ifc_env_cptra_handler_seq   = soc_ifc_env_cptra_mbox_interference_handler_sequence_t::type_id::create("soc_ifc_env_cptra_handler_seq");
    soc_ifc_env_cptra_rst_wait_seq  = soc_ifc_env_cptra_rst_wait_sequence_t::type_id::create("soc_ifc_env_cptra_rst_wait_seq");
endfunction

function void soc_ifc_env_top_mbox_rst_sequence::connect_extra_soc_ifc_resp_seqs();
    soc_ifc_env_rst_seq.soc_ifc_status_agent_rsp_seq = soc_ifc_status_agent_rsp_seq;
endfunction

function void soc_ifc_env_top_mbox_rst_sequence::connect_extra_cptra_resp_seqs();
    soc_ifc_env_cptra_rst_wait_seq.cptra_status_agent_rsp_seq = cptra_status_agent_rsp_seq;
endfunction

function soc_ifc_env_top_mbox_rst_sequence::randomize_seqs();
    if(!soc_ifc_env_mbox_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rst_sequence::body() - %s randomization failed", soc_ifc_env_mbox_seq.get_type_name()));
    if(!soc_ifc_env_rst_seq.randomize())                               
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rst_sequence::body() - %s randomization failed", soc_ifc_env_rst_seq.get_type_name()));
    if(!soc_ifc_env_cptra_handler_seq.randomize())
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rst_sequence::body() - %s randomization failed", soc_ifc_env_cptra_handler_seq.get_type_name()));
    soc_ifc_env_cptra_rst_wait_seq.wait_for_noncore_rst_assert   = 1'b1;
    soc_ifc_env_cptra_rst_wait_seq.wait_for_core_rst_assert      = 1'b0;
    soc_ifc_env_cptra_rst_wait_seq.wait_for_noncore_rst_deassert = 1'b0;
    soc_ifc_env_cptra_rst_wait_seq.wait_for_core_rst_deassert    = 1'b1;
endfunction

task soc_ifc_env_top_mbox_rst_sequence::start_seqs();
    int unsigned delay_clks; // Delay prior to system reset
    if (!std::randomize(delay_clks) with {delay_clks < 4*soc_ifc_env_mbox_seq.mbox_op_rand.dlen;}) begin
        `uvm_fatal("SOC_IFC_MBOX_TOP", $sformatf("soc_ifc_env_top_mbox_rst_sequence::body() - %s randomization failed", "delay_clks"));
    end
    fork
        begin
            soc_ifc_env_mbox_seq.start(configuration.vsqr);
        end
        begin
            soc_ifc_env_cptra_handler_seq.start(configuration.vsqr);
        end
        begin
            configuration.soc_ifc_ctrl_agent_config.wait_for_num_clocks(delay_clks);
            fork
                begin
                    `uvm_info("SOC_IFC_MBOX_TOP", "Starting rst sequence", UVM_HIGH)
                    soc_ifc_env_rst_seq.start(configuration.vsqr);
                end
                begin
                    `uvm_info("SOC_IFC_MBOX_TOP", "Killing mbox/cptra_handler sequences", UVM_HIGH)
                    soc_ifc_env_mbox_seq.kill();
                    soc_ifc_env_cptra_handler_seq.kill();
                    `uvm_info("SOC_IFC_MBOX_TOP", "Done: killing mbox/cptra_handler sequences", UVM_HIGH)
                end
                // FIXME - should probably not rely on this - instead, any subsequent sequence
                //         should check for ready_for_runtime to be set, and the cptra_handler should set it.
                begin
                    soc_ifc_env_cptra_rst_wait_seq.start(configuration.vsqr);
                    `uvm_info("SOC_IFC_MBOX_TOP", "Done: rst wait sequence", UVM_HIGH)
                end
            join
        end
    join
endtask
