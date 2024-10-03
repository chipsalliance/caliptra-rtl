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
// DESCRIPTION: This file contains macros used with the core_axi_write_out_if package.
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
//      the core_axi_write_out_if_configuration class.
//
  `define core_axi_write_out_if_CONFIGURATION_STRUCT \
typedef struct packed  { \
     uvmf_active_passive_t active_passive; \
     uvmf_initiator_responder_t initiator_responder; \
     } core_axi_write_out_if_configuration_s;

  `define core_axi_write_out_if_CONFIGURATION_TO_STRUCT_FUNCTION \
  virtual function core_axi_write_out_if_configuration_s to_struct();\
    core_axi_write_out_if_configuration_struct = \
       {\
       this.active_passive,\
       this.initiator_responder\
       };\
    return ( core_axi_write_out_if_configuration_struct );\
  endfunction

  `define core_axi_write_out_if_CONFIGURATION_FROM_STRUCT_FUNCTION \
  virtual function void from_struct(core_axi_write_out_if_configuration_s core_axi_write_out_if_configuration_struct);\
      {\
      this.active_passive,\
      this.initiator_responder  \
      } = core_axi_write_out_if_configuration_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_monitor_struct
//      and from_monitor_struct methods of the core_axi_write_out_if_transaction class.
//
  `define core_axi_write_out_if_MONITOR_STRUCT typedef struct packed  { \
  logic core_awready ; \
  logic core_wready ; \
  axi_pkg::axi_burst_e core_bresp ; \
  logic core_bid ; \
  logic core_bvalid ; \
     } core_axi_write_out_if_monitor_s;

  `define core_axi_write_out_if_TO_MONITOR_STRUCT_FUNCTION \
  virtual function core_axi_write_out_if_monitor_s to_monitor_struct();\
    core_axi_write_out_if_monitor_struct = \
            { \
            this.core_awready , \
            this.core_wready , \
            this.core_bresp , \
            this.core_bid , \
            this.core_bvalid  \
            };\
    return ( core_axi_write_out_if_monitor_struct);\
  endfunction\

  `define core_axi_write_out_if_FROM_MONITOR_STRUCT_FUNCTION \
  virtual function void from_monitor_struct(core_axi_write_out_if_monitor_s core_axi_write_out_if_monitor_struct);\
            {\
            this.core_awready , \
            this.core_wready , \
            this.core_bresp , \
            this.core_bid , \
            this.core_bvalid  \
            } = core_axi_write_out_if_monitor_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_initiator_struct
//      and from_initiator_struct methods of the core_axi_write_out_if_transaction class.
//      Also update the comments in the driver BFM.
//
  `define core_axi_write_out_if_INITIATOR_STRUCT typedef struct packed  { \
  logic core_awready ; \
  logic core_wready ; \
  axi_pkg::axi_burst_e core_bresp ; \
  logic core_bid ; \
  logic core_bvalid ; \
     } core_axi_write_out_if_initiator_s;

  `define core_axi_write_out_if_TO_INITIATOR_STRUCT_FUNCTION \
  virtual function core_axi_write_out_if_initiator_s to_initiator_struct();\
    core_axi_write_out_if_initiator_struct = \
           {\
           this.core_awready , \
           this.core_wready , \
           this.core_bresp , \
           this.core_bid , \
           this.core_bvalid  \
           };\
    return ( core_axi_write_out_if_initiator_struct);\
  endfunction

  `define core_axi_write_out_if_FROM_INITIATOR_STRUCT_FUNCTION \
  virtual function void from_initiator_struct(core_axi_write_out_if_initiator_s core_axi_write_out_if_initiator_struct);\
           {\
           this.core_awready , \
           this.core_wready , \
           this.core_bresp , \
           this.core_bid , \
           this.core_bvalid  \
           } = core_axi_write_out_if_initiator_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_responder_struct
//      and from_responder_struct methods of the core_axi_write_out_if_transaction class.
//      Also update the comments in the driver BFM.
//
  `define core_axi_write_out_if_RESPONDER_STRUCT typedef struct packed  { \
  logic core_awready ; \
  logic core_wready ; \
  axi_pkg::axi_burst_e core_bresp ; \
  logic core_bid ; \
  logic core_bvalid ; \
     } core_axi_write_out_if_responder_s;

  `define core_axi_write_out_if_TO_RESPONDER_STRUCT_FUNCTION \
  virtual function core_axi_write_out_if_responder_s to_responder_struct();\
    core_axi_write_out_if_responder_struct = \
           {\
           this.core_awready , \
           this.core_wready , \
           this.core_bresp , \
           this.core_bid , \
           this.core_bvalid  \
           };\
    return ( core_axi_write_out_if_responder_struct);\
  endfunction

  `define core_axi_write_out_if_FROM_RESPONDER_STRUCT_FUNCTION \
  virtual function void from_responder_struct(core_axi_write_out_if_responder_s core_axi_write_out_if_responder_struct);\
           {\
           this.core_awready , \
           this.core_wready , \
           this.core_bresp , \
           this.core_bid , \
           this.core_bvalid  \
           } = core_axi_write_out_if_responder_struct;\
  endfunction
// pragma uvmf custom additional begin
// pragma uvmf custom additional end
