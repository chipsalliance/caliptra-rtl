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
// DESCRIPTION: This file contains macros used with the soc_ifc_status package.
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
//      the soc_ifc_status_configuration class.
//
  `define soc_ifc_status_CONFIGURATION_STRUCT \
typedef struct packed  { \
     uvmf_active_passive_t active_passive; \
     uvmf_initiator_responder_t initiator_responder; \
     } soc_ifc_status_configuration_s;

  `define soc_ifc_status_CONFIGURATION_TO_STRUCT_FUNCTION \
  virtual function soc_ifc_status_configuration_s to_struct();\
    soc_ifc_status_configuration_struct = \
       {\
       this.active_passive,\
       this.initiator_responder\
       };\
    return ( soc_ifc_status_configuration_struct );\
  endfunction

  `define soc_ifc_status_CONFIGURATION_FROM_STRUCT_FUNCTION \
  virtual function void from_struct(soc_ifc_status_configuration_s soc_ifc_status_configuration_struct);\
      {\
      this.active_passive,\
      this.initiator_responder  \
      } = soc_ifc_status_configuration_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_monitor_struct
//      and from_monitor_struct methods of the soc_ifc_status_transaction class.
//
  `define soc_ifc_status_MONITOR_STRUCT typedef struct packed  { \
  bit ready_for_fuses ; \
  bit ready_for_mb_processing ; \
  bit ready_for_runtime ; \
  bit mailbox_data_avail ; \
  bit mailbox_flow_done ; \
  bit cptra_error_fatal_intr_pending ; \
  bit cptra_error_non_fatal_intr_pending ; \
  bit trng_req_pending ; \
  bit [63:0] generic_output_val ; \
     } soc_ifc_status_monitor_s;

  `define soc_ifc_status_TO_MONITOR_STRUCT_FUNCTION \
  virtual function soc_ifc_status_monitor_s to_monitor_struct();\
    soc_ifc_status_monitor_struct = \
            { \
            this.ready_for_fuses , \
            this.ready_for_mb_processing , \
            this.ready_for_runtime , \
            this.mailbox_data_avail , \
            this.mailbox_flow_done , \
            this.cptra_error_fatal_intr_pending , \
            this.cptra_error_non_fatal_intr_pending , \
            this.trng_req_pending , \
            this.generic_output_val  \
            };\
    return ( soc_ifc_status_monitor_struct);\
  endfunction\

  `define soc_ifc_status_FROM_MONITOR_STRUCT_FUNCTION \
  virtual function void from_monitor_struct(soc_ifc_status_monitor_s soc_ifc_status_monitor_struct);\
            {\
            this.ready_for_fuses , \
            this.ready_for_mb_processing , \
            this.ready_for_runtime , \
            this.mailbox_data_avail , \
            this.mailbox_flow_done , \
            this.cptra_error_fatal_intr_pending , \
            this.cptra_error_non_fatal_intr_pending , \
            this.trng_req_pending , \
            this.generic_output_val  \
            } = soc_ifc_status_monitor_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_initiator_struct
//      and from_initiator_struct methods of the soc_ifc_status_transaction class.
//      Also update the comments in the driver BFM.
//
  `define soc_ifc_status_INITIATOR_STRUCT typedef struct packed  { \
  bit ready_for_fuses ; \
  bit ready_for_mb_processing ; \
  bit ready_for_runtime ; \
  bit mailbox_data_avail ; \
  bit mailbox_flow_done ; \
  bit cptra_error_fatal_intr_pending ; \
  bit cptra_error_non_fatal_intr_pending ; \
  bit trng_req_pending ; \
  bit [63:0] generic_output_val ; \
     } soc_ifc_status_initiator_s;

  `define soc_ifc_status_TO_INITIATOR_STRUCT_FUNCTION \
  virtual function soc_ifc_status_initiator_s to_initiator_struct();\
    soc_ifc_status_initiator_struct = \
           {\
           this.ready_for_fuses , \
           this.ready_for_mb_processing , \
           this.ready_for_runtime , \
           this.mailbox_data_avail , \
           this.mailbox_flow_done , \
           this.cptra_error_fatal_intr_pending , \
           this.cptra_error_non_fatal_intr_pending , \
           this.trng_req_pending , \
           this.generic_output_val  \
           };\
    return ( soc_ifc_status_initiator_struct);\
  endfunction

  `define soc_ifc_status_FROM_INITIATOR_STRUCT_FUNCTION \
  virtual function void from_initiator_struct(soc_ifc_status_initiator_s soc_ifc_status_initiator_struct);\
           {\
           this.ready_for_fuses , \
           this.ready_for_mb_processing , \
           this.ready_for_runtime , \
           this.mailbox_data_avail , \
           this.mailbox_flow_done , \
           this.cptra_error_fatal_intr_pending , \
           this.cptra_error_non_fatal_intr_pending , \
           this.trng_req_pending , \
           this.generic_output_val  \
           } = soc_ifc_status_initiator_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_responder_struct
//      and from_responder_struct methods of the soc_ifc_status_transaction class.
//      Also update the comments in the driver BFM.
//
  `define soc_ifc_status_RESPONDER_STRUCT typedef struct packed  { \
  bit ready_for_fuses ; \
  bit ready_for_mb_processing ; \
  bit ready_for_runtime ; \
  bit mailbox_data_avail ; \
  bit mailbox_flow_done ; \
  bit cptra_error_fatal_intr_pending ; \
  bit cptra_error_non_fatal_intr_pending ; \
  bit trng_req_pending ; \
  bit [63:0] generic_output_val ; \
     } soc_ifc_status_responder_s;

  `define soc_ifc_status_TO_RESPONDER_STRUCT_FUNCTION \
  virtual function soc_ifc_status_responder_s to_responder_struct();\
    soc_ifc_status_responder_struct = \
           {\
           this.ready_for_fuses , \
           this.ready_for_mb_processing , \
           this.ready_for_runtime , \
           this.mailbox_data_avail , \
           this.mailbox_flow_done , \
           this.cptra_error_fatal_intr_pending , \
           this.cptra_error_non_fatal_intr_pending , \
           this.trng_req_pending , \
           this.generic_output_val  \
           };\
    return ( soc_ifc_status_responder_struct);\
  endfunction

  `define soc_ifc_status_FROM_RESPONDER_STRUCT_FUNCTION \
  virtual function void from_responder_struct(soc_ifc_status_responder_s soc_ifc_status_responder_struct);\
           {\
           this.ready_for_fuses , \
           this.ready_for_mb_processing , \
           this.ready_for_runtime , \
           this.mailbox_data_avail , \
           this.mailbox_flow_done , \
           this.cptra_error_fatal_intr_pending , \
           this.cptra_error_non_fatal_intr_pending , \
           this.trng_req_pending , \
           this.generic_output_val  \
           } = soc_ifc_status_responder_struct;\
  endfunction
// pragma uvmf custom additional begin
// pragma uvmf custom additional end
