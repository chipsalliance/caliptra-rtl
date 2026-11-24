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
// CI test fixture only -- NOT a real technology-specific cell.
//
// Functionally identical, renamed stand-in for caliptra_prim_generic_flop.
// This is one of the four primitives shared with Adams Bridge's abr_prim
// (buf/flop/flop_en/xor2): when `CALIPTRA` is defined, abr_prim's
// `ABR_PRIM_MODULE_NAME(flop)` resolves to this same faketech_prim_flop
// module via an explicit `.rst_ni(rst_b)` connection in abr_prim_flop.sv,
// so this file deliberately keeps the `rst_ni` port name (not abr_prim's own
// `rst_b`) to prove that port-naming bridge is wired correctly.

`include "caliptra_prim_assert.sv"

module faketech_prim_flop #(
  parameter int               Width      = 1,
  parameter logic [Width-1:0] ResetValue = 0
) (
  input                    clk_i,
  input                    rst_ni,
  input        [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      q_o <= ResetValue;
    end else begin
      q_o <= d_i;
    end
  end

endmodule
