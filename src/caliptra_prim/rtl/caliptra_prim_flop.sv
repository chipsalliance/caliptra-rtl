// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.
// Used parser: Fallback (regex)

`include "caliptra_prim_module_name_macros.svh"

`ifndef CALIPTRA_PRIM_DEFAULT_IMPL
  `define CALIPTRA_PRIM_DEFAULT_IMPL caliptra_prim_pkg::ImplGeneric
`endif

// This is to prevent AscentLint warnings in the generated
// abstract prim wrapper. These warnings occur due to the .*
// use. TODO: we may want to move these inline waivers
// into a separate, generated waiver file for consistency.
//ri lint_check_off OUTPUT_NOT_DRIVEN INPUT_NOT_READ HIER_BRANCH_NOT_READ
module caliptra_prim_flop

#(

  parameter int               Width      = 1,
  parameter logic [Width-1:0] ResetValue = 0

) (
  input                    clk_i,
  input                    rst_ni,
  input        [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);
  parameter caliptra_prim_pkg::impl_e Impl = `CALIPTRA_PRIM_DEFAULT_IMPL;

if (Impl == caliptra_prim_pkg::ImplXilinx) begin : gen_xilinx
    caliptra_prim_xilinx_flop #(
      .ResetValue(ResetValue),
      .Width(Width)
    ) u_impl_xilinx (
      .*
    );
end else begin : gen_generic
    `CALIPTRA_PRIM_MODULE_NAME(flop) #(
      .ResetValue(ResetValue),
      .Width(Width)
    ) u_impl_generic (
      .*
    );
end

endmodule
//ri lint_check_on OUTPUT_NOT_DRIVEN INPUT_NOT_READ HIER_BRANCH_NOT_READ
