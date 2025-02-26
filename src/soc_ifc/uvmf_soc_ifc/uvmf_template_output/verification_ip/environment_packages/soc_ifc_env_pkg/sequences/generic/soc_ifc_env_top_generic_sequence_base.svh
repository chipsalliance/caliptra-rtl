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
class soc_ifc_env_top_generic_sequence_base extends soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


    `uvm_object_utils( soc_ifc_env_top_generic_sequence_base )

    soc_ifc_env_gen_rand_rw_sequence_t soc_ifc_env_gen_rand_rw_seq;


    extern virtual function create_seqs();

    function new(string name = "");
        super.new(name);
        create_seqs();
    endfunction

    virtual task body();
        reg_model = configuration.soc_ifc_rm;
        soc_ifc_env_gen_rand_rw_seq.aaxi_ci = configuration.aaxi_ci;

        soc_ifc_env_gen_rand_rw_seq.reg_model = configuration.soc_ifc_rm;
        
        soc_ifc_env_gen_rand_rw_seq.start(reg_model.soc_ifc_AXI_map.get_sequencer());
        // soc_ifc_env_gen_rand_rw_seq.start(configuration.vsqr);

    endtask

endclass

function soc_ifc_env_top_generic_sequence_base::create_seqs();
    soc_ifc_env_gen_rand_rw_seq = soc_ifc_env_gen_rand_rw_sequence_t::type_id::create("soc_ifc_env_gen_rand_rw_seq");
    soc_ifc_env_gen_rand_rw_seq.randomize();
endfunction