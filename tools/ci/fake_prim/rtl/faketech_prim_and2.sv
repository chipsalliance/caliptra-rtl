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
// Functionally identical, renamed stand-in for caliptra_prim_generic_and2,
// used by .github/workflows/verify-prim-swap.yml to prove that
// CALIPTRA_PRIM_ROOT/CALIPTRA_PRIM_MODULE_PREFIX overrides are correctly
// honored (by both caliptra_prim and Adams Bridge's abr_prim) and elaborate
// cleanly under a genuinely different root directory and module name prefix.

`include "caliptra_prim_assert.sv"

module faketech_prim_and2 #(
  parameter int Width = 1
) (
  input        [Width-1:0] in0_i,
  input        [Width-1:0] in1_i,
  output logic [Width-1:0] out_o
);

  assign out_o = in0_i & in1_i;

endmodule
