//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This file contains macros used with the ECC_in package.
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
//      the ECC_in_configuration class.
//
  `define ECC_in_CONFIGURATION_STRUCT \
typedef struct packed  { \
     uvmf_active_passive_t active_passive; \
     uvmf_initiator_responder_t initiator_responder; \
     } ECC_in_configuration_s;

  `define ECC_in_CONFIGURATION_TO_STRUCT_FUNCTION \
  virtual function ECC_in_configuration_s to_struct();\
    ECC_in_configuration_struct = \
       {\
       this.active_passive,\
       this.initiator_responder\
       };\
    return ( ECC_in_configuration_struct );\
  endfunction

  `define ECC_in_CONFIGURATION_FROM_STRUCT_FUNCTION \
  virtual function void from_struct(ECC_in_configuration_s ECC_in_configuration_struct);\
      {\
      this.active_passive,\
      this.initiator_responder  \
      } = ECC_in_configuration_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_monitor_struct
//      and from_monitor_struct methods of the ECC_in_transaction class.
//
  `define ECC_in_MONITOR_STRUCT typedef struct packed  { \
  ecc_in_test_transactions test ; \
  ecc_in_op_transactions op ; \
  bit [7:0] test_case_sel ; \
     } ECC_in_monitor_s;

  `define ECC_in_TO_MONITOR_STRUCT_FUNCTION \
  virtual function ECC_in_monitor_s to_monitor_struct();\
    ECC_in_monitor_struct = \
            { \
            this.test , \
            this.op , \
            this.test_case_sel  \
            };\
    return ( ECC_in_monitor_struct);\
  endfunction\

  `define ECC_in_FROM_MONITOR_STRUCT_FUNCTION \
  virtual function void from_monitor_struct(ECC_in_monitor_s ECC_in_monitor_struct);\
            {\
            this.test , \
            this.op , \
            this.test_case_sel  \
            } = ECC_in_monitor_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_initiator_struct
//      and from_initiator_struct methods of the ECC_in_transaction class.
//      Also update the comments in the driver BFM.
//
  `define ECC_in_INITIATOR_STRUCT typedef struct packed  { \
  ecc_in_test_transactions test ; \
  ecc_in_op_transactions op ; \
  bit [7:0] test_case_sel ; \
     } ECC_in_initiator_s;

  `define ECC_in_TO_INITIATOR_STRUCT_FUNCTION \
  virtual function ECC_in_initiator_s to_initiator_struct();\
    ECC_in_initiator_struct = \
           {\
           this.test , \
           this.op , \
           this.test_case_sel  \
           };\
    return ( ECC_in_initiator_struct);\
  endfunction

  `define ECC_in_FROM_INITIATOR_STRUCT_FUNCTION \
  virtual function void from_initiator_struct(ECC_in_initiator_s ECC_in_initiator_struct);\
           {\
           this.test , \
           this.op , \
           this.test_case_sel  \
           } = ECC_in_initiator_struct;\
  endfunction

// ****************************************************************************
// When changing the contents of this struct, be sure to update the to_responder_struct
//      and from_responder_struct methods of the ECC_in_transaction class.
//      Also update the comments in the driver BFM.
//
  `define ECC_in_RESPONDER_STRUCT typedef struct packed  { \
  ecc_in_test_transactions test ; \
  ecc_in_op_transactions op ; \
  bit [7:0] test_case_sel ; \
     } ECC_in_responder_s;

  `define ECC_in_TO_RESPONDER_STRUCT_FUNCTION \
  virtual function ECC_in_responder_s to_responder_struct();\
    ECC_in_responder_struct = \
           {\
           this.test , \
           this.op , \
           this.test_case_sel  \
           };\
    return ( ECC_in_responder_struct);\
  endfunction

  `define ECC_in_FROM_RESPONDER_STRUCT_FUNCTION \
  virtual function void from_responder_struct(ECC_in_responder_s ECC_in_responder_struct);\
           {\
           this.test , \
           this.op , \
           this.test_case_sel  \
           } = ECC_in_responder_struct;\
  endfunction
// pragma uvmf custom additional begin
// pragma uvmf custom additional end
