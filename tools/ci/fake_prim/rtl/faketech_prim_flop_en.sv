// SPDX-License-Identifier: Apache-2.0
//
// CI test fixture only -- NOT a real technology-specific cell.
//
// Functionally identical, renamed stand-in for
// caliptra_prim_generic_flop_en. This is one of the four primitives shared
// with Adams Bridge's abr_prim (buf/flop/flop_en/xor2): when `CALIPTRA is
// defined, abr_prim's `ABR_PRIM_MODULE_NAME(flop_en)` resolves to this same
// faketech_prim_flop_en module via an explicit `.rst_ni(rst_b)` connection
// in abr_prim_flop_en.sv, so this file deliberately keeps the `rst_ni` port
// name (not abr_prim's own `rst_b`) to prove that port-naming bridge is
// wired correctly. caliptra_prim_sec_anchor_buf is intentionally referenced
// unchanged here: it is the always-present abstraction layer (itself
// swappable via caliptra_prim_buf), not part of this generic/tech swap.

`include "caliptra_prim_assert.sv"

module faketech_prim_flop_en #(
  parameter int               Width      = 1,
  parameter bit               EnSecBuf   = 0,
  parameter logic [Width-1:0] ResetValue = 0
) (
  input                    clk_i,
  input                    rst_ni,
  input                    en_i,
  input        [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  logic en;
  if (EnSecBuf) begin : gen_en_sec_buf
    caliptra_prim_sec_anchor_buf #(
      .Width(1)
    ) u_en_buf (
      .in_i(en_i),
      .out_o(en)
    );
  end else begin : gen_en_no_sec_buf
    assign en = en_i;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      q_o <= ResetValue;
    end else if (en) begin
      q_o <= d_i;
    end
  end

endmodule
