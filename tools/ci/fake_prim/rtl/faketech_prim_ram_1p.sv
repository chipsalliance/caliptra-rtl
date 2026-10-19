// SPDX-License-Identifier: Apache-2.0
//
// CI test fixture only -- NOT a real technology-specific cell.
//
// Functionally identical, renamed stand-in for caliptra_prim_generic_ram_1p,
// used by .github/workflows/verify-prim-swap.yml to prove that
// CALIPTRA_PRIM_ROOT/CALIPTRA_PRIM_MODULE_PREFIX overrides are correctly
// honored and elaborate cleanly under a genuinely different root directory
// and module name prefix. The caliptra_prim_ram_1p_pkg import and
// caliptra_prim_util_memload.svh include are intentionally unchanged: they
// are the always-present package/utility layer, not part of the swappable
// generic/tech-cell boundary itself.

`include "caliptra_prim_assert.sv"

module faketech_prim_ram_1p import caliptra_prim_ram_1p_pkg::*; #(
  parameter  int Width           = 32, // bit
  parameter  int Depth           = 128,
  parameter  int DataBitsPerMask = 1, // Number of data bits per bit of write mask
  parameter      MemInitFile     = "", // VMEM file to initialize the memory with

  localparam int Aw              = $clog2(Depth)  // derived parameter
) (
  input  logic             clk_i,

  input  logic             req_i,
  input  logic             write_i,
  input  logic [Aw-1:0]    addr_i,
  input  logic [Width-1:0] wdata_i,
  input  logic [Width-1:0] wmask_i,
  output logic [Width-1:0] rdata_o, // Read data. Data is returned one cycle after req_i is high.
  input ram_1p_cfg_t       cfg_i
);

`ifndef SYNTHESIS_MEMORY_BLACK_BOXING

  `CALIPTRA_ASSERT_INIT(DataBitsPerMaskCheck_A, (Width % DataBitsPerMask) == 0)

  logic unused_cfg;
  assign unused_cfg = ^cfg_i;

  localparam int MaskWidth = Width / DataBitsPerMask;

  logic [Width-1:0]     mem [Depth];
  logic [MaskWidth-1:0] wmask;

  for (genvar k = 0; k < MaskWidth; k++) begin : gen_wmask
    assign wmask[k] = &wmask_i[k*DataBitsPerMask +: DataBitsPerMask];

    `CALIPTRA_ASSERT(MaskCheck_A, req_i && write_i |->
        wmask_i[k*DataBitsPerMask +: DataBitsPerMask] inside {{DataBitsPerMask{1'b1}}, '0},
        clk_i, '0)
  end

  // using always instead of always_ff to avoid 'ICPD  - illegal combination of drivers' error
  // thrown when using $readmemh system task to backdoor load an image
  always @(posedge clk_i) begin
    if (req_i) begin
      if (write_i) begin
        for (int i=0; i < MaskWidth; i = i + 1) begin
          if (wmask[i]) begin
            mem[addr_i][i*DataBitsPerMask +: DataBitsPerMask] <=
              wdata_i[i*DataBitsPerMask +: DataBitsPerMask];
          end
        end
      end else begin
        rdata_o <= mem[addr_i];
      end
    end
  end

  `include "caliptra_prim_util_memload.svh"
`endif
endmodule
