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
        MBOX_MIN,
        MBOX_MAX,
        MBOX_UNDERFLOW_SMALL,
        MBOX_UNDERFLOW_MEDIUM,
        MBOX_UNDERFLOW_LARGE,
        MBOX_OVERFLOW_SMALL,
        MBOX_OVERFLOW_MEDIUM,
        MBOX_OVERFLOW_LARGE,
        MBOX_INVALID
    } mbox_sel;
    enum {
        CPTRA_STANDARD,
        CPTRA_UNDERREAD,
        CPTRA_OVERREAD
    } cptra_sel;

    if (!std::randomize(mbox_sel,cptra_sel) with {mbox_sel dist {MBOX_MIN              :/ 100,
                                                                 MBOX_MAX              :/ 100,
                                                                 MBOX_UNDERFLOW_SMALL  :/ 100,
                                                                 MBOX_UNDERFLOW_MEDIUM :/ 100,
                                                                 MBOX_UNDERFLOW_LARGE  :/ 10,
                                                                 MBOX_OVERFLOW_SMALL   :/ 100,
                                                                 MBOX_OVERFLOW_MEDIUM  :/ 100,
                                                                 MBOX_OVERFLOW_LARGE   :/ 10,
                                                                 MBOX_INVALID          :/ 10};})
        `uvm_fatal("SOC_IFC_MBOX_TOP", "Failed to randomize sub-sequence types")

    case (mbox_sel) inside
        MBOX_MIN:
            obj = soc_ifc_env_mbox_min_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
        MBOX_MAX:
            obj = soc_ifc_env_mbox_max_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
        MBOX_UNDERFLOW_SMALL:
            obj = soc_ifc_env_mbox_dlen_underflow_small_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
        MBOX_UNDERFLOW_MEDIUM:
            obj = soc_ifc_env_mbox_dlen_underflow_medium_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
        MBOX_UNDERFLOW_LARGE:
            obj = soc_ifc_env_mbox_dlen_underflow_large_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
        MBOX_OVERFLOW_SMALL:
            obj = soc_ifc_env_mbox_dlen_overflow_small_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
        MBOX_OVERFLOW_MEDIUM:
            obj = soc_ifc_env_mbox_dlen_overflow_medium_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
        MBOX_OVERFLOW_LARGE:
            obj = soc_ifc_env_mbox_dlen_overflow_large_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
        MBOX_INVALID:
            obj = soc_ifc_env_mbox_dlen_invalid_sequence_t::get_type().create_object("soc_ifc_env_mbox_seq");
        default: `uvm_fatal("SOC_IFC_MBOX_TOP","Bad mbox_sel")
    endcase
    if(!$cast(soc_ifc_env_mbox_seq,obj)) `uvm_fatal("SOC_IFC_TOP_MBOX", "soc_ifc_env_top_mbox_dlen_violation::create_seqs() - <seq_type>.create_object() failed")

    case (cptra_sel) inside
        CPTRA_STANDARD:
            obj = soc_ifc_env_cptra_mbox_handler_sequence_t::get_type().create_object("soc_ifc_env_cptra_handler_seq");
        CPTRA_UNDERREAD:
            obj = soc_ifc_env_cptra_mbox_dlen_underread_handler_sequence_t::get_type().create_object("soc_ifc_env_cptra_handler_seq");
        CPTRA_OVERREAD:
            obj = soc_ifc_env_cptra_mbox_dlen_overread_handler_sequence_t::get_type().create_object("soc_ifc_env_cptra_handler_seq");
        default: `uvm_fatal("SOC_IFC_MBOX_TOP","Bad cptra_sel")
    endcase
    if(!$cast(soc_ifc_env_cptra_handler_seq,obj)) `uvm_fatal("SOC_IFC_TOP_MBOX", "soc_ifc_env_top_mbox_dlen_violation::create_seqs() - <seq_type>.create_object() failed")
endfunction
