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
// Functionally identical, renamed stand-in for
// caliptra_prim_generic_clock_mux2, used by
// .github/workflows/verify-prim-swap.yml to prove that
// CALIPTRA_PRIM_ROOT/CALIPTRA_PRIM_MODULE_PREFIX overrides are correctly
// honored (by both caliptra_prim and Adams Bridge's abr_prim) and elaborate
// cleanly under a genuinely different root directory and module name prefix.

`include "caliptra_prim_assert.sv"

module faketech_prim_clock_mux2 #(
  parameter bit NoFpgaBufG = 1'b0 // unused here, mirrors the generic parameter
) (
  input        clk0_i,
  input        clk1_i,
  input        sel_i,
  output logic clk_o
);

  assign clk_o = (sel_i & clk1_i) | (~sel_i & clk0_i);

  // make sure sel is never X (including during reset)
  `CALIPTRA_ASSERT(selKnown0, ##1 !$isunknown(sel_i), clk0_i, 0)
  `CALIPTRA_ASSERT(selKnown1, ##1 !$isunknown(sel_i), clk1_i, 0)

endmodule : faketech_prim_clock_mux2
