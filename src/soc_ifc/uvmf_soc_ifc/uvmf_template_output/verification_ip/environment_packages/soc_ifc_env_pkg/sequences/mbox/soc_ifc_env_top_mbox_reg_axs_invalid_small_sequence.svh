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
class soc_ifc_env_top_mbox_reg_axs_invalid_small_sequence extends soc_ifc_env_top_mbox_sequence_base;


  `uvm_object_utils( soc_ifc_env_top_mbox_reg_axs_invalid_small_sequence )

  extern virtual function      create_seqs();

endclass

function soc_ifc_env_top_mbox_reg_axs_invalid_small_sequence::create_seqs();
    uvm_object obj;
    enum {
        BASE,
        INTRFR
    } handler_type;
    obj = soc_ifc_env_mbox_reg_axs_invalid_small_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
    if(!$cast(soc_ifc_env_mbox_seq,obj)) `uvm_fatal("SOC_IFC_TOP_MBOX_REG_AXS_INVALID", "soc_ifc_env_top_mbox_reg_axs_invalid_small_sequence::create_seqs() - <seq_type>.create_object() failed")
    void'(std::randomize(handler_type));
    case (handler_type) inside
        BASE:    obj = soc_ifc_env_cptra_mbox_handler_sequence_t::get_type().create_object("soc_ifc_env_cptra_handler_seq");
        INTRFR:  obj = soc_ifc_env_cptra_mbox_interference_handler_sequence_t::get_type().create_object("soc_ifc_env_cptra_handler_seq");
        default: `uvm_fatal("SOC_IFC_TOP_MBOX_REG_AXS_INVALID", $sformatf("Bad handler type - %p", handler_type))
    endcase
    if(!$cast(soc_ifc_env_cptra_handler_seq,obj)) `uvm_fatal("SOC_IFC_TOP_MBOX_REG_AXS_INVALID", "soc_ifc_env_top_mbox_reg_axs_invalid_large_sequence::create_seqs() - <seq_type>.create_object() failed")
endfunction
