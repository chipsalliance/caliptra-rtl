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
class soc_ifc_env_top_mbox_dlen_violation_sequence extends soc_ifc_env_top_mbox_sequence_base;


  `uvm_object_utils( soc_ifc_env_top_mbox_dlen_violation_sequence )

  extern virtual function create_seqs();

endclass

function soc_ifc_env_top_mbox_dlen_violation_sequence::create_seqs();
    uvm_object obj;

    enum {
        MBOX_UNDERFLOW,
        MBOX_OVERFLOW
    } mbox_sel;
    enum {
        CPTRA_UNDERREAD,
        CPTRA_OVERREAD
    } cptra_sel;

    if (!std::randomize(mbox_sel,cptra_sel))
        `uvm_fatal("SOC_IFC_MBOX_TOP", "Failed to randomize sub-sequence types")

    case (mbox_sel) inside
        MBOX_UNDERFLOW:
            obj = soc_ifc_env_mbox_dlen_underflow_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
        MBOX_OVERFLOW:
            obj = soc_ifc_env_mbox_dlen_overflow_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
        default: `uvm_fatal("SOC_IFC_MBOX_TOP","Bad mbox_sel")
    endcase
    if(!$cast(soc_ifc_env_mbox_seq,obj)) `uvm_fatal("SOC_IFC_TOP_MBOX", "soc_ifc_env_top_mbox_dlen_violation::create_seqs() - <seq_type>.create_object() failed")

    case (cptra_sel) inside
        CPTRA_UNDERREAD:
            obj = soc_ifc_env_cptra_mbox_dlen_underread_handler_sequence_t::get_type().create_object("soc_ifc_env_cptra_handler_seq");
        CPTRA_OVERREAD:
            obj = soc_ifc_env_cptra_mbox_dlen_overread_handler_sequence_t::get_type().create_object("soc_ifc_env_cptra_handler_seq");
        default: `uvm_fatal("SOC_IFC_MBOX_TOP","Bad cptra_sel")
    endcase
    if(!$cast(soc_ifc_env_cptra_handler_seq,obj)) `uvm_fatal("SOC_IFC_TOP_MBOX", "soc_ifc_env_top_mbox_dlen_violation::create_seqs() - <seq_type>.create_object() failed")
endfunction
