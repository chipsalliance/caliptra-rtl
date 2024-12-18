// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package caliptra_tlul_pkg;

  localparam int TL_AW=32;
  localparam int TL_DW=32;    // = TL_DBW * 8; TL_DBW must be a power-of-two
  localparam int TL_AIW=8;    // a_source, d_source
  localparam int TL_DIW=1;    // d_sink
  localparam int TL_AUW=23;   // a_user
  localparam int TL_DUW=14;   // d_user
  localparam int TL_DBW=(TL_DW>>3);
  localparam int TL_SZW=$clog2($clog2(TL_DBW)+1);

  // this can be either PPC or BINTREE
  // there is no functional difference, but timing and area behavior is different
  // between the two instances. PPC can result in smaller implementations when timing
  // is not critical, whereas BINTREE is favorable when timing pressure is high (but this
  // may also result in a larger implementation). on FPGA targets, BINTREE is favorable
  // both in terms of area and timing.
  parameter ArbiterImpl = "PPC";

  typedef enum logic [2:0] {
    PutFullData    = 3'h 0,
    PutPartialData = 3'h 1,
    Get            = 3'h 4
  } tl_a_op_e;

  typedef enum logic [2:0] {
    AccessAck     = 3'h 0,
    AccessAckData = 3'h 1
  } tl_d_op_e;

  parameter int H2DCmdMaxWidth  = 57;
  parameter int H2DCmdIntgWidth = 7;
  parameter int H2DCmdFullWidth = H2DCmdMaxWidth + H2DCmdIntgWidth;
  parameter int D2HRspMaxWidth  = 57;
  parameter int D2HRspIntgWidth = 7;
  parameter int D2HRspFullWidth = D2HRspMaxWidth + D2HRspIntgWidth;
  parameter int DataMaxWidth    = 32;
  parameter int DataIntgWidth   = 7;
  parameter int DataFullWidth   = DataMaxWidth + DataIntgWidth;
  parameter int RsvdWidth       = TL_AUW - caliptra_prim_mubi_pkg::MuBi4Width -
                                  H2DCmdIntgWidth - DataIntgWidth;

  // Data that is returned upon an a TL-UL error belonging to an instruction fetch.
  // Note that this data will be returned with the correct bus integrity value.
  parameter logic [TL_DW-1:0] DataWhenInstrError = '0;
  // Data that is returned upon an a TL-UL error not belonging to an instruction fetch.
  // Note that this data will be returned with the correct bus integrity value.
  parameter logic [TL_DW-1:0] DataWhenError      = {TL_DW{1'b1}};

  typedef struct packed {
    logic [RsvdWidth-1:0]       rsvd;
    caliptra_prim_mubi_pkg::mubi4_t      instr_type;
    logic [H2DCmdIntgWidth-1:0] cmd_intg;
    logic [DataIntgWidth-1:0]   data_intg;
  } tl_a_user_t;

  parameter tl_a_user_t TL_A_USER_DEFAULT = '{
    rsvd: '0,
    instr_type: caliptra_prim_mubi_pkg::MuBi4False,
    cmd_intg:  {H2DCmdIntgWidth{1'b1}},
    data_intg: {DataIntgWidth{1'b1}}
  };

  typedef struct packed {
    caliptra_prim_mubi_pkg::mubi4_t        instr_type;
    logic   [TL_AW-1:0]  addr;
    tl_a_op_e                     opcode;
    logic  [TL_DBW-1:0]  mask;
  } tl_h2d_cmd_intg_t;

  typedef struct packed {
    logic                         a_valid;
    tl_a_op_e                     a_opcode;
    logic                  [2:0]  a_param;
    logic  [TL_SZW-1:0]  a_size;
    logic  [TL_AIW-1:0]  a_source;
    logic   [TL_AW-1:0]  a_address;
    logic  [TL_DBW-1:0]  a_mask;
    logic   [TL_DW-1:0]  a_data;
    tl_a_user_t                   a_user;

    logic                         d_ready;
  } tl_h2d_t;

  // The choice of all 1's as the blanked value is deliberate.
  // It is assumed that most security features of the design are opt-in instead
  // of opt-out.
  // Given the opt-in nature, if a 0 were to propagate, the feature would be turned
  // off.  Whereas if a 1 were to propagate, it would either stay on or be turned on.
  // There is however no perfect value for this purpose.
  localparam logic [TL_DW-1:0] BlankedAData = {TL_DW{1'b1}};

  localparam tl_h2d_t TL_H2D_DEFAULT = '{
    d_ready:  1'b1,
    a_opcode: tl_a_op_e'('0),
    a_user:   TL_A_USER_DEFAULT,
    a_data:   BlankedAData,
    default:  '0
  };

  typedef struct packed {
    logic [D2HRspIntgWidth-1:0]    rsp_intg;
    logic [DataIntgWidth-1:0]      data_intg;
  } tl_d_user_t;

  parameter tl_d_user_t TL_D_USER_DEFAULT = '{
    rsp_intg: {D2HRspIntgWidth{1'b1}},
    data_intg: {DataIntgWidth{1'b1}}
  };

  typedef struct packed {
    logic                         d_valid;
    tl_d_op_e                     d_opcode;
    logic                  [2:0]  d_param;
    logic  [TL_SZW-1:0]  d_size;   // Bouncing back a_size
    logic  [TL_AIW-1:0]  d_source;
    logic  [TL_DIW-1:0]  d_sink;
    logic   [TL_DW-1:0]  d_data;
    tl_d_user_t                   d_user;
    logic                         d_error;

    logic                         a_ready;

  } tl_d2h_t;

  typedef struct packed {
    tl_d_op_e                     opcode;
    logic  [TL_SZW-1:0]  size;
    // Temporarily removed because source changes throughout the fabric
    // and thus cannot be used for end-to-end checking.
    // A different PR will propose a work-around (a hoaky one) to see if
    // it gets the job done.
    //logic  [TL_AIW-1:0]  source;
    logic                         error;
  } tl_d2h_rsp_intg_t;

  localparam tl_d2h_t TL_D2H_DEFAULT = '{
    a_ready:  1'b1,
    d_opcode: tl_d_op_e'('0),
    d_user:   TL_D_USER_DEFAULT,
    default:  '0
  };

  // Check user for unsupported values
  function automatic logic tl_a_user_chk(tl_a_user_t user);
    logic malformed_err;
    logic unused_user;
    unused_user = |user;
    malformed_err = caliptra_prim_mubi_pkg::mubi4_test_invalid(user.instr_type);
    return malformed_err;
  endfunction // tl_a_user_chk

  // extract variables used for command checking
  function automatic tl_h2d_cmd_intg_t extract_h2d_cmd_intg(tl_h2d_t tl);
    tl_h2d_cmd_intg_t payload;
    logic unused_tlul;
    unused_tlul = ^tl;
    payload.addr = tl.a_address;
    payload.opcode = tl.a_opcode;
    payload.mask = tl.a_mask;
    payload.instr_type = tl.a_user.instr_type;
    return payload;
  endfunction // extract_h2d_payload

  // extract variables used for response checking
  function automatic tl_d2h_rsp_intg_t extract_d2h_rsp_intg(tl_d2h_t tl);
    tl_d2h_rsp_intg_t payload;
    logic unused_tlul;
    unused_tlul = ^tl;
    payload.opcode = tl.d_opcode;
    payload.size   = tl.d_size;
    //payload.source = tl.d_source;
    payload.error  = tl.d_error;
    return payload;
  endfunction // extract_d2h_rsp_intg

  // calculate ecc for command checking
  function automatic logic [H2DCmdIntgWidth-1:0] get_cmd_intg(tl_h2d_t tl);
    logic [H2DCmdIntgWidth-1:0] cmd_intg;
    logic [H2DCmdMaxWidth-1:0] unused_cmd_payload;
    tl_h2d_cmd_intg_t cmd;
    cmd = extract_h2d_cmd_intg(tl);
    {cmd_intg, unused_cmd_payload} =
        caliptra_prim_secded_pkg::caliptra_prim_secded_inv_64_57_enc(H2DCmdMaxWidth'(cmd));
   return cmd_intg;
  endfunction  // get_cmd_intg

  // calculate ecc for data checking
  function automatic logic [DataIntgWidth-1:0] get_data_intg(logic [TL_DW-1:0] data);
    logic [DataIntgWidth-1:0] data_intg;
    logic [TL_DW-1:0] unused_data;
    logic [DataIntgWidth + TL_DW - 1 : 0] enc_data;
    enc_data = caliptra_prim_secded_pkg::caliptra_prim_secded_inv_39_32_enc(data);
    data_intg = enc_data[DataIntgWidth + TL_DW - 1 : TL_DW];
    unused_data = enc_data[TL_DW - 1 : 0];
    return data_intg;
  endfunction  // get_data_intg

  // return inverted integrity for command payload
  function automatic logic [H2DCmdIntgWidth-1:0] get_bad_cmd_intg(tl_h2d_t tl);
    logic [H2DCmdIntgWidth-1:0] cmd_intg;
    cmd_intg = get_cmd_intg(tl);
    return ~cmd_intg;
  endfunction // get_bad_cmd_intg

  // return inverted integrity for data payload
  function automatic logic [H2DCmdIntgWidth-1:0] get_bad_data_intg(logic [TL_DW-1:0] data);
    logic [H2DCmdIntgWidth-1:0] data_intg;
    data_intg = get_data_intg(data);
    return ~data_intg;
  endfunction // get_bad_data_intg

endpackage
