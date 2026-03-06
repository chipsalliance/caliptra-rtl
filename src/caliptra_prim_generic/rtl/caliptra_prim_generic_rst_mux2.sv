// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "caliptra_prim_assert.sv"
`include "caliptra_prim_module_name_macros.svh"

module caliptra_prim_generic_rst_mux2 #(
  parameter bit NoFpgaBufG = 1'b0 // this parameter serves no function in the generic model
) (
  input        rst0_i,
  input        rst1_i,
  input        sel_i,
  output logic rst_o
);

  // We model the mux with logic operations
  assign rst_o = (sel_i & rst1_i) | (~sel_i & rst0_i);

  // make sure sel is never X (including during reset)
  // need to use ##1 as this could break with inverted clocks that
  // start with a rising edge at the beginning of the simulation.
  `CALIPTRA_ASSERT(selKnown0, ##1 !$isunknown(sel_i), rst0_i, 0)
  `CALIPTRA_ASSERT(selKnown1, ##1 !$isunknown(sel_i), rst1_i, 0)

endmodule : caliptra_prim_generic_rst_mux2
