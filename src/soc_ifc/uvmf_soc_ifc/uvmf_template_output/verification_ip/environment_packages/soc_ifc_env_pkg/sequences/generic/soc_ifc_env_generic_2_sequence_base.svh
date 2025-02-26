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
// DESCRIPTION: Base sequence to perform a mailbox command within the
//              soc_ifc environment.
//              Extended to provide additional functionality.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_env_generic_2_sequence_base extends aaxi_uvm_seq_base; //soc_ifc_env_sequence_base #(.CONFIG_T(soc_ifc_env_configuration_t));


    `uvm_object_utils( soc_ifc_env_generic_2_sequence_base )
  
    uvm_status_e reg_sts;

    extern virtual task read_reg();
    extern virtual task write_reg();
    extern virtual task outstanding_write_reg();

    function new(string name = "");
        super.new(name);
    endfunction

    virtual task pre_body();
        super.pre_body();
        // if (configuration == null)
        //     `uvm_info("KNU_CONFIG", "config is null inside generic2 seq", UVM_MEDIUM)
        // reg_model = configuration.soc_ifc_rm;
    endtask

    virtual task body();
        
        // fork
        //     begin
        //         `uvm_info("KNU_GEN2", "Starting write task", UVM_MEDIUM)
        //         write_reg();
        //         #10;
        //     end
        //     begin
        //         `uvm_info("KNU_GEN2", "Starting read task", UVM_MEDIUM)
        //         read_reg();
        //         #10;
        //     end
        // join
        
        // write_reg();
        // read_reg();

        outstanding_write_reg();
        
    endtask
  
endclass

task soc_ifc_env_generic_2_sequence_base::read_reg();
endtask

task soc_ifc_env_generic_2_sequence_base::write_reg();
endtask

task soc_ifc_env_generic_2_sequence_base::outstanding_write_reg();
endtask

