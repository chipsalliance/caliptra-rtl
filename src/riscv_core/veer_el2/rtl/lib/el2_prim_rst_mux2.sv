// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Standalone default. Integrators (e.g. Caliptra) redirect this to their own
// glitchless reset mux primitive by defining RV_PRIM_RST_MUX2_IMPL (same
// rst0_i/rst1_i/sel_i/rst_o interface).
`ifndef RV_PRIM_RST_MUX2_IMPL
  `define RV_PRIM_RST_MUX2_IMPL el2_prim_generic_rst_mux2
`endif

module el2_prim_rst_mux2 (
  input        rst0_i,
  input        rst1_i,
  input        sel_i,
  output logic rst_o
);
  `RV_PRIM_RST_MUX2_IMPL u_impl (.rst0_i(rst0_i), .rst1_i(rst1_i), .sel_i(sel_i), .rst_o(rst_o));
endmodule
