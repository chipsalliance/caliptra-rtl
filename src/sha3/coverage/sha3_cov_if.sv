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
// Functional coverage of the SHA3 core (ot_sha3) of the SHA3 accelerator.

`ifndef VERILATOR

interface sha3_cov_if (
  input logic                             clk_i,
  input logic                             rst_ni,
  input logic                             zeroize,
  input ot_sha3_pkg::sha3_st_sparse_e     sha3_st
);

  logic zeroize_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) zeroize_q <= 1'b0;
    else         zeroize_q <= zeroize;
  end

  covergroup sha3_zeroize_cov_grp @(posedge clk_i iff (rst_ni && zeroize && !zeroize_q));
    sha3_st_cp: coverpoint sha3_st {
      ignore_bins error = {ot_sha3_pkg::StTerminalError_sparse};
      // StFlush only lasts one cycle after DONE and cannot be hit by firmware
      ignore_bins flush = {ot_sha3_pkg::StFlush_sparse};
    }
  endgroup

  sha3_zeroize_cov_grp sha3_zeroize_cov_grp1 = new();

endinterface

`endif
