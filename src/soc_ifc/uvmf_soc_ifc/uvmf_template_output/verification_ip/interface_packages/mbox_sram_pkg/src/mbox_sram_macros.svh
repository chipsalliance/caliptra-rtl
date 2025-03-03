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
// DESCRIPTION: This file contains macros used with the mbox_sram package.
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
//      the mbox_sram_configuration class.
//
  `define mbox_sram_CONFIGURATION_STRUCT \
typedef struct packed  { \
     bit [1:0] inject_ecc_error;\
     bit auto_clear_ecc_error_injection;\
     uvmf_active_passive_t active_passive; \
     uvmf_initiator_responder_t initiator_responder; \
     } mbox_sram_configuration_s;

  `define mbox_sram_CONFIGURATION_TO_STRUCT_FUNCTION \
  virtual function mbox_sram_configuration_s to_struct();\
    mbox_sram_configuration_struct = \
       {\
       this.inject_ecc_error,\
       this.auto_clear_ecc_error_injection,\
       this.active_passive,\
       this.initiator_responder\
       };\
    return ( mbox_sram_configuration_struct );\
  endfunction

  `define mbox_sram_CONFIGURATION_FROM_STRUCT_FUNCTION \
  virtual function void from_struct(mbox_sram_configuration_s mbox_sram_configuration_struct);\
      {\
      this.inject_ecc_error,\
      this.auto_clear_ecc_error_injection,\
      this.active_passive,\
      this.initiator_responder  \
      } = mbox_sram_configuration_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_monitor_struct
//      and from_monitor_struct methods of the mbox_sram_transaction class.
//
  `define mbox_sram_MONITOR_STRUCT typedef struct packed  { \
  bit is_read ; \
  bit [CPTRA_MBOX_ADDR_W-1:0] address ; \
  bit [CPTRA_MBOX_DATA_W-1:0] data ; \
  bit [CPTRA_MBOX_ECC_DATA_W-1:0] data_ecc ; \
  bit ecc_single_bit_error ; \
  bit ecc_double_bit_error ; \
     } mbox_sram_monitor_s;

  `define mbox_sram_TO_MONITOR_STRUCT_FUNCTION \
  virtual function mbox_sram_monitor_s to_monitor_struct();\
    mbox_sram_monitor_struct = \
            { \
            this.is_read , \
            this.address , \
            this.data , \
            this.data_ecc , \
            this.ecc_single_bit_error , \
            this.ecc_double_bit_error  \
            };\
    return ( mbox_sram_monitor_struct);\
  endfunction\

  `define mbox_sram_FROM_MONITOR_STRUCT_FUNCTION \
  virtual function void from_monitor_struct(mbox_sram_monitor_s mbox_sram_monitor_struct);\
            {\
            this.is_read , \
            this.address , \
            this.data , \
            this.data_ecc , \
            this.ecc_single_bit_error , \
            this.ecc_double_bit_error  \
            } = mbox_sram_monitor_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_initiator_struct
//      and from_initiator_struct methods of the mbox_sram_transaction class.
//      Also update the comments in the driver BFM.
//
  `define mbox_sram_INITIATOR_STRUCT typedef struct packed  { \
  bit is_read ; \
  bit [CPTRA_MBOX_ADDR_W-1:0] address ; \
  bit [CPTRA_MBOX_DATA_W-1:0] data ; \
  bit [CPTRA_MBOX_ECC_DATA_W-1:0] data_ecc ; \
  bit ecc_single_bit_error ; \
  bit ecc_double_bit_error ; \
     } mbox_sram_initiator_s;

  `define mbox_sram_TO_INITIATOR_STRUCT_FUNCTION \
  virtual function mbox_sram_initiator_s to_initiator_struct();\
    mbox_sram_initiator_struct = \
           {\
           this.is_read , \
           this.address , \
           this.data , \
           this.data_ecc , \
           this.ecc_single_bit_error , \
           this.ecc_double_bit_error  \
           };\
    return ( mbox_sram_initiator_struct);\
  endfunction

  `define mbox_sram_FROM_INITIATOR_STRUCT_FUNCTION \
  virtual function void from_initiator_struct(mbox_sram_initiator_s mbox_sram_initiator_struct);\
           {\
           this.is_read , \
           this.address , \
           this.data , \
           this.data_ecc , \
           this.ecc_single_bit_error , \
           this.ecc_double_bit_error  \
           } = mbox_sram_initiator_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_responder_struct
//      and from_responder_struct methods of the mbox_sram_transaction class.
//      Also update the comments in the driver BFM.
//
  `define mbox_sram_RESPONDER_STRUCT typedef struct packed  { \
  bit is_read ; \
  bit [CPTRA_MBOX_ADDR_W-1:0] address ; \
  bit [CPTRA_MBOX_DATA_W-1:0] data ; \
  bit [CPTRA_MBOX_ECC_DATA_W-1:0] data_ecc ; \
  bit ecc_single_bit_error ; \
  bit ecc_double_bit_error ; \
     } mbox_sram_responder_s;

  `define mbox_sram_TO_RESPONDER_STRUCT_FUNCTION \
  virtual function mbox_sram_responder_s to_responder_struct();\
    mbox_sram_responder_struct = \
           {\
           this.is_read , \
           this.address , \
           this.data , \
           this.data_ecc , \
           this.ecc_single_bit_error , \
           this.ecc_double_bit_error  \
           };\
    return ( mbox_sram_responder_struct);\
  endfunction

  `define mbox_sram_FROM_RESPONDER_STRUCT_FUNCTION \
  virtual function void from_responder_struct(mbox_sram_responder_s mbox_sram_responder_struct);\
           {\
           this.is_read , \
           this.address , \
           this.data , \
           this.data_ecc , \
           this.ecc_single_bit_error , \
           this.ecc_double_bit_error  \
           } = mbox_sram_responder_struct;\
  endfunction
// pragma uvmf custom additional begin
// pragma uvmf custom additional end
