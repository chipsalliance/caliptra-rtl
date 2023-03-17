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
// DESCRIPTION: This file contains macros used with the pv_write package.
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
//      the pv_write_configuration class.
//
  `define pv_write_CONFIGURATION_STRUCT \
typedef struct packed  { \
     uvmf_active_passive_t active_passive; \
     uvmf_initiator_responder_t initiator_responder; \
     } pv_write_configuration_s;

  `define pv_write_CONFIGURATION_TO_STRUCT_FUNCTION \
  virtual function pv_write_configuration_s to_struct();\
    pv_write_configuration_struct = \
       {\
       this.active_passive,\
       this.initiator_responder\
       };\
    return ( pv_write_configuration_struct );\
  endfunction

  `define pv_write_CONFIGURATION_FROM_STRUCT_FUNCTION \
  virtual function void from_struct(pv_write_configuration_s pv_write_configuration_struct);\
      {\
      this.active_passive,\
      this.initiator_responder  \
      } = pv_write_configuration_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_monitor_struct
//      and from_monitor_struct methods of the pv_write_transaction class.
//
  `define pv_write_MONITOR_STRUCT typedef struct packed  { \
  logic write_en ; \
  logic   [PV_ENTRY_ADDR_W-1:0] write_entry ; \
  logic   [PV_ENTRY_SIZE_WIDTH-1:0] write_offset ; \
  logic   [PV_DATA_W-1:0] write_data ; \
  logic error ; \
     } pv_write_monitor_s;

  `define pv_write_TO_MONITOR_STRUCT_FUNCTION \
  virtual function pv_write_monitor_s to_monitor_struct();\
    pv_write_monitor_struct = \
            { \
            this.write_en , \
            this.write_entry , \
            this.write_offset , \
            this.write_data , \
            this.error  \
            };\
    return ( pv_write_monitor_struct);\
  endfunction\

  `define pv_write_FROM_MONITOR_STRUCT_FUNCTION \
  virtual function void from_monitor_struct(pv_write_monitor_s pv_write_monitor_struct);\
            {\
            this.write_en , \
            this.write_entry , \
            this.write_offset , \
            this.write_data , \
            this.error  \
            } = pv_write_monitor_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_initiator_struct
//      and from_initiator_struct methods of the pv_write_transaction class.
//      Also update the comments in the driver BFM.
//
  `define pv_write_INITIATOR_STRUCT typedef struct packed  { \
  logic write_en ; \
  logic   [PV_ENTRY_ADDR_W-1:0] write_entry ; \
  logic   [PV_ENTRY_SIZE_WIDTH-1:0] write_offset ; \
  logic   [PV_DATA_W-1:0] write_data ; \
  logic error ; \
     } pv_write_initiator_s;

  `define pv_write_TO_INITIATOR_STRUCT_FUNCTION \
  virtual function pv_write_initiator_s to_initiator_struct();\
    pv_write_initiator_struct = \
           {\
           this.write_en , \
           this.write_entry , \
           this.write_offset , \
           this.write_data , \
           this.error  \
           };\
    return ( pv_write_initiator_struct);\
  endfunction

  `define pv_write_FROM_INITIATOR_STRUCT_FUNCTION \
  virtual function void from_initiator_struct(pv_write_initiator_s pv_write_initiator_struct);\
           {\
           this.write_en , \
           this.write_entry , \
           this.write_offset , \
           this.write_data , \
           this.error  \
           } = pv_write_initiator_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_responder_struct
//      and from_responder_struct methods of the pv_write_transaction class.
//      Also update the comments in the driver BFM.
//
  `define pv_write_RESPONDER_STRUCT typedef struct packed  { \
  logic write_en ; \
  logic   [PV_ENTRY_ADDR_W-1:0] write_entry ; \
  logic   [PV_ENTRY_SIZE_WIDTH-1:0] write_offset ; \
  logic   [PV_DATA_W-1:0] write_data ; \
  logic error ; \
     } pv_write_responder_s;

  `define pv_write_TO_RESPONDER_STRUCT_FUNCTION \
  virtual function pv_write_responder_s to_responder_struct();\
    pv_write_responder_struct = \
           {\
           this.write_en , \
           this.write_entry , \
           this.write_offset , \
           this.write_data , \
           this.error  \
           };\
    return ( pv_write_responder_struct);\
  endfunction

  `define pv_write_FROM_RESPONDER_STRUCT_FUNCTION \
  virtual function void from_responder_struct(pv_write_responder_s pv_write_responder_struct);\
           {\
           this.write_en , \
           this.write_entry , \
           this.write_offset , \
           this.write_data , \
           this.error  \
           } = pv_write_responder_struct;\
  endfunction
// pragma uvmf custom additional begin
// pragma uvmf custom additional end
