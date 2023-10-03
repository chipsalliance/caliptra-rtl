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
// DESCRIPTION: This file contains macros used with the cptra_status package.
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
//      the cptra_status_configuration class.
//
  `define cptra_status_CONFIGURATION_STRUCT \
typedef struct packed  { \
     uvmf_active_passive_t active_passive; \
     uvmf_initiator_responder_t initiator_responder; \
     } cptra_status_configuration_s;

  `define cptra_status_CONFIGURATION_TO_STRUCT_FUNCTION \
  virtual function cptra_status_configuration_s to_struct();\
    cptra_status_configuration_struct = \
       {\
       this.active_passive,\
       this.initiator_responder\
       };\
    return ( cptra_status_configuration_struct );\
  endfunction

  `define cptra_status_CONFIGURATION_FROM_STRUCT_FUNCTION \
  virtual function void from_struct(cptra_status_configuration_s cptra_status_configuration_struct);\
      {\
      this.active_passive,\
      this.initiator_responder  \
      } = cptra_status_configuration_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_monitor_struct
//      and from_monitor_struct methods of the cptra_status_transaction class.
//
  `define cptra_status_MONITOR_STRUCT typedef struct packed  { \
  bit soc_ifc_err_intr_pending ; \
  bit soc_ifc_notif_intr_pending ; \
  bit sha_err_intr_pending ; \
  bit sha_notif_intr_pending ; \
  bit timer_intr_pending ; \
  bit noncore_rst_asserted ; \
  bit uc_rst_asserted ; \
  bit fw_update_rst_window ; \
  bit [`CLP_OBF_KEY_DWORDS-1:0] [31:0] cptra_obf_key_reg ; \
  bit [`CLP_OBF_FE_DWORDS-1:0] [31:0] obf_field_entropy ; \
  bit [`CLP_OBF_UDS_DWORDS-1:0] [31:0] obf_uds_seed ; \
  bit [31:0] nmi_vector ; \
  bit nmi_intr_pending ; \
  bit iccm_locked ; \
     } cptra_status_monitor_s;

  `define cptra_status_TO_MONITOR_STRUCT_FUNCTION \
  virtual function cptra_status_monitor_s to_monitor_struct();\
    cptra_status_monitor_struct = \
            { \
            this.soc_ifc_err_intr_pending , \
            this.soc_ifc_notif_intr_pending , \
            this.sha_err_intr_pending , \
            this.sha_notif_intr_pending , \
            this.timer_intr_pending , \
            this.noncore_rst_asserted , \
            this.uc_rst_asserted , \
            this.fw_update_rst_window , \
            this.cptra_obf_key_reg , \
            this.obf_field_entropy , \
            this.obf_uds_seed , \
            this.nmi_vector , \
            this.nmi_intr_pending , \
            this.iccm_locked  \
            };\
    return ( cptra_status_monitor_struct);\
  endfunction\

  `define cptra_status_FROM_MONITOR_STRUCT_FUNCTION \
  virtual function void from_monitor_struct(cptra_status_monitor_s cptra_status_monitor_struct);\
            {\
            this.soc_ifc_err_intr_pending , \
            this.soc_ifc_notif_intr_pending , \
            this.sha_err_intr_pending , \
            this.sha_notif_intr_pending , \
            this.timer_intr_pending , \
            this.noncore_rst_asserted , \
            this.uc_rst_asserted , \
            this.fw_update_rst_window , \
            this.cptra_obf_key_reg , \
            this.obf_field_entropy , \
            this.obf_uds_seed , \
            this.nmi_vector , \
            this.nmi_intr_pending , \
            this.iccm_locked  \
            } = cptra_status_monitor_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_initiator_struct
//      and from_initiator_struct methods of the cptra_status_transaction class.
//      Also update the comments in the driver BFM.
//
  `define cptra_status_INITIATOR_STRUCT typedef struct packed  { \
  bit soc_ifc_err_intr_pending ; \
  bit soc_ifc_notif_intr_pending ; \
  bit sha_err_intr_pending ; \
  bit sha_notif_intr_pending ; \
  bit timer_intr_pending ; \
  bit noncore_rst_asserted ; \
  bit uc_rst_asserted ; \
  bit fw_update_rst_window ; \
  bit [`CLP_OBF_KEY_DWORDS-1:0] [31:0] cptra_obf_key_reg ; \
  bit [`CLP_OBF_FE_DWORDS-1:0] [31:0] obf_field_entropy ; \
  bit [`CLP_OBF_UDS_DWORDS-1:0] [31:0] obf_uds_seed ; \
  bit [31:0] nmi_vector ; \
  bit nmi_intr_pending ; \
  bit iccm_locked ; \
     } cptra_status_initiator_s;

  `define cptra_status_TO_INITIATOR_STRUCT_FUNCTION \
  virtual function cptra_status_initiator_s to_initiator_struct();\
    cptra_status_initiator_struct = \
           {\
           this.soc_ifc_err_intr_pending , \
           this.soc_ifc_notif_intr_pending , \
           this.sha_err_intr_pending , \
           this.sha_notif_intr_pending , \
           this.timer_intr_pending , \
           this.noncore_rst_asserted , \
           this.uc_rst_asserted , \
           this.fw_update_rst_window , \
           this.cptra_obf_key_reg , \
           this.obf_field_entropy , \
           this.obf_uds_seed , \
           this.nmi_vector , \
           this.nmi_intr_pending , \
           this.iccm_locked  \
           };\
    return ( cptra_status_initiator_struct);\
  endfunction

  `define cptra_status_FROM_INITIATOR_STRUCT_FUNCTION \
  virtual function void from_initiator_struct(cptra_status_initiator_s cptra_status_initiator_struct);\
           {\
           this.soc_ifc_err_intr_pending , \
           this.soc_ifc_notif_intr_pending , \
           this.sha_err_intr_pending , \
           this.sha_notif_intr_pending , \
           this.timer_intr_pending , \
           this.noncore_rst_asserted , \
           this.uc_rst_asserted , \
           this.fw_update_rst_window , \
           this.cptra_obf_key_reg , \
           this.obf_field_entropy , \
           this.obf_uds_seed , \
           this.nmi_vector , \
           this.nmi_intr_pending , \
           this.iccm_locked  \
           } = cptra_status_initiator_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_responder_struct
//      and from_responder_struct methods of the cptra_status_transaction class.
//      Also update the comments in the driver BFM.
//
  `define cptra_status_RESPONDER_STRUCT typedef struct packed  { \
  bit soc_ifc_err_intr_pending ; \
  bit soc_ifc_notif_intr_pending ; \
  bit sha_err_intr_pending ; \
  bit sha_notif_intr_pending ; \
  bit timer_intr_pending ; \
  bit noncore_rst_asserted ; \
  bit uc_rst_asserted ; \
  bit fw_update_rst_window ; \
  bit [`CLP_OBF_KEY_DWORDS-1:0] [31:0] cptra_obf_key_reg ; \
  bit [`CLP_OBF_FE_DWORDS-1:0] [31:0] obf_field_entropy ; \
  bit [`CLP_OBF_UDS_DWORDS-1:0] [31:0] obf_uds_seed ; \
  bit [31:0] nmi_vector ; \
  bit nmi_intr_pending ; \
  bit iccm_locked ; \
     } cptra_status_responder_s;

  `define cptra_status_TO_RESPONDER_STRUCT_FUNCTION \
  virtual function cptra_status_responder_s to_responder_struct();\
    cptra_status_responder_struct = \
           {\
           this.soc_ifc_err_intr_pending , \
           this.soc_ifc_notif_intr_pending , \
           this.sha_err_intr_pending , \
           this.sha_notif_intr_pending , \
           this.timer_intr_pending , \
           this.noncore_rst_asserted , \
           this.uc_rst_asserted , \
           this.fw_update_rst_window , \
           this.cptra_obf_key_reg , \
           this.obf_field_entropy , \
           this.obf_uds_seed , \
           this.nmi_vector , \
           this.nmi_intr_pending , \
           this.iccm_locked  \
           };\
    return ( cptra_status_responder_struct);\
  endfunction

  `define cptra_status_FROM_RESPONDER_STRUCT_FUNCTION \
  virtual function void from_responder_struct(cptra_status_responder_s cptra_status_responder_struct);\
           {\
           this.soc_ifc_err_intr_pending , \
           this.soc_ifc_notif_intr_pending , \
           this.sha_err_intr_pending , \
           this.sha_notif_intr_pending , \
           this.timer_intr_pending , \
           this.noncore_rst_asserted , \
           this.uc_rst_asserted , \
           this.fw_update_rst_window , \
           this.cptra_obf_key_reg , \
           this.obf_field_entropy , \
           this.obf_uds_seed , \
           this.nmi_vector , \
           this.nmi_intr_pending , \
           this.iccm_locked  \
           } = cptra_status_responder_struct;\
  endfunction
// pragma uvmf custom additional begin
// pragma uvmf custom additional end
