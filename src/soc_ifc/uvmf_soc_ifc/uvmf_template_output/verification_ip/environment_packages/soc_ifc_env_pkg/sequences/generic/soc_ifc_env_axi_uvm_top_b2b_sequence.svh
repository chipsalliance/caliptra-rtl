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
// DESCRIPTION: Sequence to initiate (and respond) to mailbox command.
//              "TOP" sequence because it invokes lower level env sequences
//              to facilitate the uC/SoC sides of mailbox command handling
//              and this sequence defines the whole mailbox flow.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_axi_uvm_top_b2b_sequence extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


    `uvm_object_utils( soc_ifc_env_axi_uvm_top_b2b_sequence )

    soc_ifc_env_axi_uvm_gen_b2b_rand_sequence_t soc_ifc_env_axi_uvm_gen_b2b_rand_seq;
    // aaxi_uvm_seq_write_ctrl_AW_W outstanding_write_seq;
    // aaxi_uvm_seq_basic_write aaxi_write_seq, aaxi_write_seq2;
    // aaxi_uvm_seq_write_ctrl_nonblocking aaxi_write_nb_seq, aaxi_write_nb_seq2;
    // soc_ifc_env_axi_uvm_nonblocking_write_sequence_t aaxi_write_nb_seq;

    extern virtual function create_seqs();

    function new(string name = "");
        super.new(name);
        create_seqs();
        // aaxi_write_seq.base_addr = 'h300e0; //aaxi_addr_t'('h0000_0000_0000_0000);
        // aaxi_write_seq.limit_addr = 'h300e0; //aaxi_addr_t'(1 << SOC_IFC_ADDR_W)-1;
        // aaxi_write_seq2.base_addr = 'h30000;
        // aaxi_write_seq2.limit_addr = 'h30000;
        // aaxi_write_nb_seq.base_addr = 'h300e0;
        // aaxi_write_nb_seq.limit_addr = 'h300e0;
        // aaxi_write_nb_seq2.base_addr = 'h30000;
        // aaxi_write_nb_seq2.limit_addr = 'h300e0;
        // outstanding_write_seq.base_addr = 'h30000;
        // outstanding_write_seq.limit_addr = 'h30000;

        
    endfunction

    virtual task body();
        reg_model = configuration.soc_ifc_rm;

        // configuration.aaxi_ci.uvm_resp = 0;
        configuration.aaxi_ci.maxwaits = 100;
        configuration.aaxi_ci.total_outstanding_depth = 10;
        configuration.aaxi_ci.id_outstanding_depth = 10;
        
        soc_ifc_env_axi_uvm_gen_b2b_rand_seq.aaxi_ci = configuration.aaxi_ci;
        `uvm_info("[TOP b2b]", $sformatf("maxwait = %d, outstanding depth = %d", configuration.aaxi_ci.maxwaits, configuration.aaxi_ci.total_outstanding_depth), UVM_MEDIUM)
        soc_ifc_env_axi_uvm_gen_b2b_rand_seq.start(reg_model.soc_ifc_AXI_map.get_sequencer());
        // repeat(4) begin
        //     outstanding_write_seq.start(reg_model.soc_ifc_AXI_map.get_sequencer());
        //     outstanding_write_seq.req.len = 0;
        //     outstanding_write_seq.req.burst = 0;
        // end
        // fork
        //     begin
                // aaxi_write_nb_seq.start(reg_model.soc_ifc_AXI_map.get_sequencer());
        //     end
        //     begin
        //         aaxi_write_nb_seq2.start(reg_model.soc_ifc_AXI_map.get_sequencer());
        //     end
        // join

    endtask

endclass

function soc_ifc_env_axi_uvm_top_b2b_sequence::create_seqs();
    soc_ifc_env_axi_uvm_gen_b2b_rand_seq = soc_ifc_env_axi_uvm_gen_b2b_rand_sequence_t::type_id::create("soc_ifc_env_axi_uvm_gen_b2b_rand_seq");
    // outstanding_write_seq = aaxi_uvm_seq_write_ctrl_AW_W::type_id::create("outstanding_write_seq");
    // aaxi_write_nb_seq = soc_ifc_env_axi_uvm_nonblocking_write_sequence_t::type_id::create("aaxi_write_nb_seq");
    // aaxi_write_nb_seq2 = aaxi_uvm_seq_write_ctrl_nonblocking::type_id::create("aaxi_write_nb_seq2");
endfunction
