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
class soc_ifc_env_generic_2_sequence_base extends aaxi_uvm_seq_base;


    `uvm_object_utils( soc_ifc_env_generic_2_sequence_base )
  
    uvm_status_e reg_sts;

    extern virtual task read_reg();
    extern virtual task write_reg();

    function new(string name = "");
        super.new(name);
    endfunction

    virtual task pre_body();
        super.pre_body();
    endtask

    virtual task body();    
        write_reg();
        read_reg();
    endtask
  
endclass

task soc_ifc_env_generic_2_sequence_base::read_reg();
endtask

task soc_ifc_env_generic_2_sequence_base::write_reg();
endtask


