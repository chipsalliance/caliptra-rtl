// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Clock inverter
//   Varies on the process

`include "caliptra_prim_module_name_macros.svh"

module caliptra_prim_generic_clock_inv #(
  parameter bit HasScanMode = 1'b1,
  parameter bit NoFpgaBufG  = 1'b0 // only used in FPGA case
) (
  input        clk_i,
  input        scanmode_i,
  output logic clk_no      // Inverted
);

  if (HasScanMode) begin : gen_scan
    `CALIPTRA_PRIM_MODULE_NAME(clock_mux2) #(
      .NoFpgaBufG(NoFpgaBufG)
    ) i_dft_tck_mux (
      .clk0_i ( ~clk_i     ),
      .clk1_i ( clk_i      ), // bypass the inverted clock for testing
      .sel_i  ( scanmode_i ),
      .clk_o  ( clk_no     )
    );
  end else begin : gen_noscan
    logic unused_scanmode;
    assign unused_scanmode = scanmode_i;
    assign clk_no = ~clk_i;
  end

endmodule : caliptra_prim_generic_clock_inv
