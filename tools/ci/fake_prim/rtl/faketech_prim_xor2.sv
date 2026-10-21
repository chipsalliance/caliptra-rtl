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
// Functionally identical, renamed stand-in for caliptra_prim_generic_xor2.
// This is one of the four primitives shared with Adams Bridge's abr_prim
// (buf/flop/flop_en/xor2): when `CALIPTRA` is defined, abr_prim's
// `ABR_PRIM_MODULE_NAME(xor2)` resolves to this same faketech_prim_xor2
// module, so .github/workflows/verify-prim-swap.yml elaborating cleanly
// proves Adams Bridge's automatic reuse of Caliptra's tech-cell prefix
// actually works, not just Caliptra's own swap mechanism.

`include "caliptra_prim_assert.sv"

module faketech_prim_xor2 #(
  parameter int Width = 1
) (
  input        [Width-1:0] in0_i,
  input        [Width-1:0] in1_i,
  output logic [Width-1:0] out_o
);

  assign out_o = in0_i ^ in1_i;

endmodule
