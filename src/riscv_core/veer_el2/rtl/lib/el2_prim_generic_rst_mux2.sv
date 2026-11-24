// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Generic reset multiplexor that is the default implementation behind
// el2_prim_rst_mux2.
//
// WARNING: This is a plain combinational AND/OR mux. It is NOT guaranteed to
// be glitchless after synthesis: toggling sel_i while both active-low resets
// are deasserted may produce a spurious reset pulse.
//
// Integrators targeting silicon MUST either:
//   * replace this module with a qualified glitchless reset mux cell or
//   * override RV_PRIM_RST_MUX2_IMPL with an already-mapped primitive
//     (e.g. caliptra_prim_rst_mux2).

module el2_prim_generic_rst_mux2 (
  input        rst0_i,
  input        rst1_i,
  input        sel_i,
  output logic rst_o
);

  assign rst_o = (sel_i & rst1_i) | (~sel_i & rst0_i);

endmodule
