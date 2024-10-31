// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

// -------------------------------------------------------------
// AXI Subordinate
// -------------------------------------------------------------
// Description:
//   Subordinate to convert AXI protocol transactions into internal component accesses
//   Includes an arbiter to squash duplex AXI transactions into simplex component operations
//   May optionally include an Exclusive Access monitor (AxLOCK signal)
//
// Limitations:
//   - When multiple ID tracking is enabled, write responses are returned in the
//     same order they are received, regardless of ID.
//
// -------------------------------------------------------------

module axi_sub_tb();

// Allow testbench configuration to be overridden per-compile ///////
`ifdef CALIPTRA_AXI_SUB_AW                                         //
localparam AW = `CALIPTRA_AXI_SUB_AW;                              //
`else                                                              //
localparam AW = 48;                                                //
`endif                                                             //
`ifdef CALIPTRA_AXI_SUB_DW                                         //
localparam DW = `CALIPTRA_AXI_SUB_DW;                              //
`else                                                              //
localparam DW = 32;                                                //
`endif                                                             //
`ifdef CALIPTRA_AXI_SUB_UW                                         //
localparam UW = `CALIPTRA_AXI_SUB_UW;                              //
`else                                                              //
localparam UW = 32;                                                //
`endif                                                             //
`ifdef CALIPTRA_AXI_SUB_IW                                         //
localparam IW = `CALIPTRA_AXI_SUB_IW;                              //
`else                                                              //
localparam IW = 32;                                                //
`endif                                                             //
`ifdef CALIPTRA_AXI_SUB_C_LAT                                      //
localparam C_LAT = `CALIPTRA_AXI_SUB_C_LAT;                        //
`else                                                              //
localparam C_LAT = 0;                                              //
`endif                                                             //
`ifdef CALIPTRA_AXI_SUB_EX_EN                                      //
localparam EX_EN = `CALIPTRA_AXI_SUB_EX_EN;                        //
`else                                                              //
localparam EX_EN = 0;                                              //
`endif                                                             //
/////////////////////////////////////////////////////////////////////

axi_if axi_sub_if();

// Clock and Reset
logic clk;
logic rst_n;

// Component Signals
logic dv;
logic [AW-1:0] addr;
logic [DW-1:0] wdata;
logic [DW/8-1:0] wstrb;
logic [DW-1:0] rdata;
logic last;
logic hld;
logic err;
logic [UW-1:0] user;

// 100 MHz clock
initial begin
  clk = 1'b0;
  forever #5 clk = ~clk;
end

// Reset
initial begin
  rst_n = 1'b0;
  #10;
  rst_n = 1'b1;
end

// Instantiate the AXI Subordinate
axi_sub #(
  .AW(AW),
  .DW(DW),
  .UW(UW),
  .IW(IW),
  .C_LAT(C_LAT),
  .EX_EN(EX_EN)
) axi_sub_inst (
  .clk(clk),
  .rst_n(rst_n),
  // AXI INF
  .s_axi_w_if(axi_sub_if.w_sub),
  .s_axi_r_if(axi_sub_if.r_sub),
  // COMPONENT INF
  .dv(dv),
  .addr(addr),
  .user(user),
  .wdata(wdata),
  .wstrb(wstrb),
  .rdata(rdata),
  .last(last),
  .hld(hld),
  .err(err)
);

// Register backend

// SRAM backend


endmodule
