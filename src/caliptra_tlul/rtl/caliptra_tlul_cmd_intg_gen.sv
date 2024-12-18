// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "caliptra_prim_assert.sv"

/**
 * Tile-Link UL command integrity generator
 */

module caliptra_tlul_cmd_intg_gen import caliptra_tlul_pkg::*; #(
  parameter bit EnableDataIntgGen = 1'b1
) (
  // TL-UL interface
  input  tl_h2d_t tl_i,
  output tl_h2d_t tl_o
);

  tl_h2d_cmd_intg_t cmd;
  assign cmd = extract_h2d_cmd_intg(tl_i);
  logic [H2DCmdMaxWidth-1:0] unused_cmd_payload;

  logic [H2DCmdIntgWidth-1:0] cmd_intg;
  caliptra_prim_secded_inv_64_57_enc u_cmd_gen (
    .data_i(H2DCmdMaxWidth'(cmd)),
    .data_o({cmd_intg, unused_cmd_payload})
  );

  logic [TL_DW-1:0] data_final;
  logic [DataIntgWidth-1:0] data_intg;

  if (EnableDataIntgGen) begin : gen_data_intg
    assign data_final = tl_i.a_data;

    logic [DataMaxWidth-1:0] unused_data;
    caliptra_prim_secded_inv_39_32_enc u_data_gen (
      .data_i(DataMaxWidth'(data_final)),
      .data_o({data_intg, unused_data})
    );
  end else begin : gen_passthrough_data_intg
    assign data_final = tl_i.a_data;
    assign data_intg = tl_i.a_user.data_intg;
  end

  always_comb begin
    tl_o = tl_i;
    tl_o.a_data = data_final;
    tl_o.a_user.cmd_intg = cmd_intg;
    tl_o.a_user.data_intg = data_intg;
  end


  logic unused_tl;
  assign unused_tl = ^tl_i;

  `CALIPTRA_ASSERT_INIT(PayMaxWidthCheck_A, $bits(tl_h2d_cmd_intg_t) <= H2DCmdMaxWidth)

endmodule : caliptra_tlul_cmd_intg_gen
