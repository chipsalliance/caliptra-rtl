//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This file contains macros used with the AES_out package.
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
//      the AES_out_configuration class.
//
  `define AES_out_CONFIGURATION_STRUCT \
typedef struct packed  { \
     uvmf_active_passive_t active_passive; \
     uvmf_initiator_responder_t initiator_responder; \
     } AES_out_configuration_s;

  `define AES_out_CONFIGURATION_TO_STRUCT_FUNCTION \
  virtual function AES_out_configuration_s to_struct();\
    AES_out_configuration_struct = \
       {\
       this.active_passive,\
       this.initiator_responder\
       };\
    return ( AES_out_configuration_struct );\
  endfunction

  `define AES_out_CONFIGURATION_FROM_STRUCT_FUNCTION \
  virtual function void from_struct(AES_out_configuration_s AES_out_configuration_struct);\
      {\
      this.active_passive,\
      this.initiator_responder  \
      } = AES_out_configuration_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_monitor_struct
//      and from_monitor_struct methods of the AES_out_transaction class.
//
  `define AES_out_MONITOR_STRUCT typedef struct packed  { \
  bit [OUTPUT_TEXT_WIDTH-1:0] result ; \
     } AES_out_monitor_s;

  `define AES_out_TO_MONITOR_STRUCT_FUNCTION \
  virtual function AES_out_monitor_s to_monitor_struct();\
    AES_out_monitor_struct = \
            { \
            this.result  \
            };\
    return ( AES_out_monitor_struct);\
  endfunction\

  `define AES_out_FROM_MONITOR_STRUCT_FUNCTION \
  virtual function void from_monitor_struct(AES_out_monitor_s AES_out_monitor_struct);\
            {\
            this.result  \
            } = AES_out_monitor_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_initiator_struct
//      and from_initiator_struct methods of the AES_out_transaction class.
//      Also update the comments in the driver BFM.
//
  `define AES_out_INITIATOR_STRUCT typedef struct packed  { \
  bit [OUTPUT_TEXT_WIDTH-1:0] result ; \
     } AES_out_initiator_s;

  `define AES_out_TO_INITIATOR_STRUCT_FUNCTION \
  virtual function AES_out_initiator_s to_initiator_struct();\
    AES_out_initiator_struct = \
           {\
           this.result  \
           };\
    return ( AES_out_initiator_struct);\
  endfunction

  `define AES_out_FROM_INITIATOR_STRUCT_FUNCTION \
  virtual function void from_initiator_struct(AES_out_initiator_s AES_out_initiator_struct);\
           {\
           this.result  \
           } = AES_out_initiator_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_responder_struct
//      and from_responder_struct methods of the AES_out_transaction class.
//      Also update the comments in the driver BFM.
//
  `define AES_out_RESPONDER_STRUCT typedef struct packed  { \
  bit [OUTPUT_TEXT_WIDTH-1:0] result ; \
     } AES_out_responder_s;

  `define AES_out_TO_RESPONDER_STRUCT_FUNCTION \
  virtual function AES_out_responder_s to_responder_struct();\
    AES_out_responder_struct = \
           {\
           this.result  \
           };\
    return ( AES_out_responder_struct);\
  endfunction

  `define AES_out_FROM_RESPONDER_STRUCT_FUNCTION \
  virtual function void from_responder_struct(AES_out_responder_s AES_out_responder_struct);\
           {\
           this.result  \
           } = AES_out_responder_struct;\
  endfunction
// pragma uvmf custom additional begin
// pragma uvmf custom additional end
