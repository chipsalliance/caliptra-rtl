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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This file contains macros used with the soc_ifc_ctrl package.
//   These macros include packed struct definitions.  These structs are
//   used to pass data between classes, hvl, and BFM's, hdl.  Use of 
//   structs are more efficient and simpler to modify.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_struct
//      and from_struct methods defined in the macros below that are used in  
//      the soc_ifc_ctrl_configuration class.
//
  `define soc_ifc_ctrl_CONFIGURATION_STRUCT \
typedef struct packed  { \
     uvmf_active_passive_t active_passive; \
     uvmf_initiator_responder_t initiator_responder; \
     } soc_ifc_ctrl_configuration_s;

  `define soc_ifc_ctrl_CONFIGURATION_TO_STRUCT_FUNCTION \
  virtual function soc_ifc_ctrl_configuration_s to_struct();\
    soc_ifc_ctrl_configuration_struct = \
       {\
       this.active_passive,\
       this.initiator_responder\
       };\
    return ( soc_ifc_ctrl_configuration_struct );\
  endfunction

  `define soc_ifc_ctrl_CONFIGURATION_FROM_STRUCT_FUNCTION \
  virtual function void from_struct(soc_ifc_ctrl_configuration_s soc_ifc_ctrl_configuration_struct);\
      {\
      this.active_passive,\
      this.initiator_responder  \
      } = soc_ifc_ctrl_configuration_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_monitor_struct
//      and from_monitor_struct methods of the soc_ifc_ctrl_transaction class.
//
  `define soc_ifc_ctrl_MONITOR_STRUCT typedef struct packed  { \
  bit [7:0] [31:0] cptra_obf_key_rand ; \
  bit set_pwrgood ; \
  bit assert_rst ; \
  int unsigned wait_cycles ; \
  bit [63:0] generic_input_val ; \
     } soc_ifc_ctrl_monitor_s;

  `define soc_ifc_ctrl_TO_MONITOR_STRUCT_FUNCTION \
  virtual function soc_ifc_ctrl_monitor_s to_monitor_struct();\
    soc_ifc_ctrl_monitor_struct = \
            { \
            this.cptra_obf_key_rand , \
            this.set_pwrgood , \
            this.assert_rst , \
            this.wait_cycles , \
            this.generic_input_val  \
            };\
    return ( soc_ifc_ctrl_monitor_struct);\
  endfunction\

  `define soc_ifc_ctrl_FROM_MONITOR_STRUCT_FUNCTION \
  virtual function void from_monitor_struct(soc_ifc_ctrl_monitor_s soc_ifc_ctrl_monitor_struct);\
            {\
            this.cptra_obf_key_rand , \
            this.set_pwrgood , \
            this.assert_rst , \
            this.wait_cycles , \
            this.generic_input_val  \
            } = soc_ifc_ctrl_monitor_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_initiator_struct
//      and from_initiator_struct methods of the soc_ifc_ctrl_transaction class.
//      Also update the comments in the driver BFM.
//
  `define soc_ifc_ctrl_INITIATOR_STRUCT typedef struct packed  { \
  bit [7:0] [31:0] cptra_obf_key_rand ; \
  bit set_pwrgood ; \
  bit assert_rst ; \
  int unsigned wait_cycles ; \
  bit [63:0] generic_input_val ; \
     } soc_ifc_ctrl_initiator_s;

  `define soc_ifc_ctrl_TO_INITIATOR_STRUCT_FUNCTION \
  virtual function soc_ifc_ctrl_initiator_s to_initiator_struct();\
    soc_ifc_ctrl_initiator_struct = \
           {\
           this.cptra_obf_key_rand , \
           this.set_pwrgood , \
           this.assert_rst , \
           this.wait_cycles , \
           this.generic_input_val  \
           };\
    return ( soc_ifc_ctrl_initiator_struct);\
  endfunction

  `define soc_ifc_ctrl_FROM_INITIATOR_STRUCT_FUNCTION \
  virtual function void from_initiator_struct(soc_ifc_ctrl_initiator_s soc_ifc_ctrl_initiator_struct);\
           {\
           this.cptra_obf_key_rand , \
           this.set_pwrgood , \
           this.assert_rst , \
           this.wait_cycles , \
           this.generic_input_val  \
           } = soc_ifc_ctrl_initiator_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_responder_struct
//      and from_responder_struct methods of the soc_ifc_ctrl_transaction class.
//      Also update the comments in the driver BFM.
//
  `define soc_ifc_ctrl_RESPONDER_STRUCT typedef struct packed  { \
  bit [7:0] [31:0] cptra_obf_key_rand ; \
  bit set_pwrgood ; \
  bit assert_rst ; \
  int unsigned wait_cycles ; \
  bit [63:0] generic_input_val ; \
     } soc_ifc_ctrl_responder_s;

  `define soc_ifc_ctrl_TO_RESPONDER_STRUCT_FUNCTION \
  virtual function soc_ifc_ctrl_responder_s to_responder_struct();\
    soc_ifc_ctrl_responder_struct = \
           {\
           this.cptra_obf_key_rand , \
           this.set_pwrgood , \
           this.assert_rst , \
           this.wait_cycles , \
           this.generic_input_val  \
           };\
    return ( soc_ifc_ctrl_responder_struct);\
  endfunction

  `define soc_ifc_ctrl_FROM_RESPONDER_STRUCT_FUNCTION \
  virtual function void from_responder_struct(soc_ifc_ctrl_responder_s soc_ifc_ctrl_responder_struct);\
           {\
           this.cptra_obf_key_rand , \
           this.set_pwrgood , \
           this.assert_rst , \
           this.wait_cycles , \
           this.generic_input_val  \
           } = soc_ifc_ctrl_responder_struct;\
  endfunction
// pragma uvmf custom additional begin
// pragma uvmf custom additional end
