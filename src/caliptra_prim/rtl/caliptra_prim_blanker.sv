// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "caliptra_prim_module_name_macros.svh"

// Convenience module for wrapping caliptra_prim_and2 for use in blanking.
// When en_i == 1 the input is fed through to the output.
// When en_i == 0 the output is 0.
module caliptra_prim_blanker #(
  parameter int Width = 1
) (
  input  logic [Width-1:0] in_i,
  input  logic             en_i,
  output logic [Width-1:0] out_o
);
  `CALIPTRA_PRIM_MODULE_NAME(and2) #(.Width(Width)) u_blank_and (
    .in0_i(in_i),
    .in1_i({Width{en_i}}),
    .out_o
  );
endmodule
