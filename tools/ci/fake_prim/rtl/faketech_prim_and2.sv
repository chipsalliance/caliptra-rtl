// SPDX-License-Identifier: Apache-2.0
//
// CI test fixture only -- NOT a real technology-specific cell.
//
// Functionally identical, renamed stand-in for caliptra_prim_generic_and2,
// used by .github/workflows/verify-prim-swap.yml to prove that
// CALIPTRA_PRIM_ROOT/CALIPTRA_PRIM_MODULE_PREFIX overrides are correctly
// honored (by both caliptra_prim and Adams Bridge's abr_prim) and elaborate
// cleanly under a genuinely different root directory and module name prefix.

`include "caliptra_prim_assert.sv"

module faketech_prim_and2 #(
  parameter int Width = 1
) (
  input        [Width-1:0] in0_i,
  input        [Width-1:0] in1_i,
  output logic [Width-1:0] out_o
);

  assign out_o = in0_i & in1_i;

endmodule
