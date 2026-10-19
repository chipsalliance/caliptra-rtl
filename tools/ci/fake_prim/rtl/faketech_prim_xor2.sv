// SPDX-License-Identifier: Apache-2.0
//
// CI test fixture only -- NOT a real technology-specific cell.
//
// Functionally identical, renamed stand-in for caliptra_prim_generic_xor2.
// This is one of the four primitives shared with Adams Bridge's abr_prim
// (buf/flop/flop_en/xor2): when `CALIPTRA` is defined, abr_prim's
// `ABR_PRIM_MODULE_NAME(xor2)` resolves to this same faketech_prim_xor2
// module, so .github/workflows/verify-prim-swap.yml elaborating cleanly
// proves Adams Bridge's automatic reuse of Caliptra's tech-cell prefix
// actually works, not just Caliptra's own swap mechanism.

`include "caliptra_prim_assert.sv"

module faketech_prim_xor2 #(
  parameter int Width = 1
) (
  input        [Width-1:0] in0_i,
  input        [Width-1:0] in1_i,
  output logic [Width-1:0] out_o
);

  assign out_o = in0_i ^ in1_i;

endmodule
