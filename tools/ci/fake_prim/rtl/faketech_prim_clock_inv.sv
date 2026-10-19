// SPDX-License-Identifier: Apache-2.0
//
// CI test fixture only -- NOT a real technology-specific cell.
//
// Functionally identical, renamed stand-in for
// caliptra_prim_generic_clock_inv, used by
// .github/workflows/verify-prim-swap.yml to prove that
// CALIPTRA_PRIM_ROOT/CALIPTRA_PRIM_MODULE_PREFIX overrides are correctly
// honored and elaborate cleanly under a genuinely different root directory
// and module name prefix. Mirrors the generic reference's own use of
// `CALIPTRA_PRIM_MODULE_NAME(clock_mux2) so the nested resolution (to
// faketech_prim_clock_mux2) is exercised too.

`include "caliptra_prim_module_name_macros.svh"

module faketech_prim_clock_inv #(
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

endmodule : faketech_prim_clock_inv
