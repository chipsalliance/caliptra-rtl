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
// Functional coverage of entropy_combiner.

`ifndef VERILATOR

interface entropy_combiner_cov_if (
  input logic                                     clk,
  input logic                                     reset_n,
  input logic                                     zeroize,
  // Plain vector: when RTL and TB are compiled into separate libraries, each has
  // its own copy of entropy_combiner_pkg and the enum types do not match.
  input logic [$bits(entropy_combiner_pkg::entropy_combiner_state_e)-1:0] state,
  input logic                                     op_is_kat,    // KAT in progress
  input logic                                     es0_pending,  // ES0 request outstanding
  input logic                                     es1_pending   // ES1 request outstanding
);

  logic zeroize_q;

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) zeroize_q <= 1'b0;
    else          zeroize_q <= zeroize;
  end

  // Phase of a combine, derived from the FSM state and the pending ES requests
  typedef enum logic [2:0] {
    PhaseIdle,           // idle
    PhaseBothEsPending,  // both ES requests outstanding
    PhaseEs0Pending,     // ES1 delivered, ES0 outstanding
    PhaseEs1Pending,     // ES0 delivered, ES1 outstanding
    PhaseAckPending,     // both seeds delivered, ack to CSRNG outstanding
    PhaseOther           // KAT, waiting for the CSRNG request to drop, error
  } phase_e;

  phase_e phase;

  always_comb begin
    unique case (state)
      entropy_combiner_pkg::combiner_st_idle:
        phase = PhaseIdle;
      entropy_combiner_pkg::combiner_st_req_entropy:
        phase = (es0_pending && es1_pending) ? PhaseBothEsPending :
                es0_pending                  ? PhaseEs0Pending    : PhaseEs1Pending;
      entropy_combiner_pkg::combiner_st_sha_start,
      entropy_combiner_pkg::combiner_st_sha_feed,
      entropy_combiner_pkg::combiner_st_sha_process,
      entropy_combiner_pkg::combiner_st_sha_wait,
      entropy_combiner_pkg::combiner_st_comb_ack:
        phase = op_is_kat ? PhaseOther : PhaseAckPending;
      default:
        phase = PhaseOther;
    endcase
  end

  covergroup entropy_combiner_zeroize_cov_grp @(posedge clk iff (reset_n && zeroize && !zeroize_q));
    phase_cp: coverpoint phase {
      ignore_bins other = {PhaseOther};
    }
  endgroup

  entropy_combiner_zeroize_cov_grp entropy_combiner_zeroize_cov_grp1 = new();

endinterface

`endif
