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
// DESCRIPTION: Extended from generic sequence base to exercise b2b read.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class soc_ifc_env_b2b_read_sequence_old_dont_use extends soc_ifc_env_generic_2_sequence_base;
    `uvm_object_utils( soc_ifc_env_b2b_read_sequence )

    // typedef soc_ifc_env_b2b_read_sequence soc_ifc_env_b2b_read_sequence_t;
    // soc_ifc_env_b2b_read_sequence_t soc_ifc_env_b2b_read_seq;

    // aaxi_uvm_sequencer uvm_test_top_environment_aaxi_tb_env0_master_0_sqr;

    // extern virtual task read_reg();

    function new(string name = "");
        super.new(name);
        // super.axi_user_obj.set_addr_user('hFFFF_FFFF);
        // soc_ifc_env_b2b_read_seq = soc_ifc_env_b2b_read_sequence_t::type_id::create("soc_ifc_env_b2b_read_seq");
        
    endfunction

    // virtual task pre_body();
    //     super.pre_body();
    // endtask

    // virtual task body();
    //     reg_model = configuration.soc_ifc_rm;
    // endtask

endclass

// task soc_ifc_env_b2b_read_sequence::read_reg();
//     int addr;
//     addr = reg_model.soc_ifc_reg_rm.CPTRA_HW_CAPABILITIES.get_address(reg_model.soc_ifc_AXI_map);
// endtask