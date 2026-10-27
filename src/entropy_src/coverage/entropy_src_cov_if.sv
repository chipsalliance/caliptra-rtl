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
// Functional coverage of entropy_src.

`ifndef VERILATOR

interface entropy_src_cov_if (
  input logic                                   clk_i,
  input logic                                   rst_ni,
  input logic                                   zeroize,
  input logic                                   zeroize_reg,  // ENTROPY_SRC_CTRL.ZEROIZE
  input logic                                   zeroize_pin,  // debugUnlock_or_scan_mode_switch
  input logic [$bits(entropy_src_main_sm_pkg::state_e)-1:0] main_sm_state,
  input logic [$bits(entropy_src_ack_sm_pkg::state_e)-1:0]  ack_sm_state
);

  // The FSM states cross the bind as plain vectors: when RTL and TB are compiled
  // into separate libraries, each has its own copy of the packages and the enum
  // types do not match. Cast back to the enums here.
  entropy_src_main_sm_pkg::state_e main_sm_state_e;
  entropy_src_ack_sm_pkg::state_e  ack_sm_state_e;

  assign main_sm_state_e = entropy_src_main_sm_pkg::state_e'(main_sm_state);
  assign ack_sm_state_e  = entropy_src_ack_sm_pkg::state_e'(ack_sm_state);

  logic zeroize_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) zeroize_q <= 1'b0;
    else         zeroize_q <= zeroize;
  end

  covergroup entropy_src_zeroize_cov_grp @(posedge clk_i iff (rst_ni && zeroize && !zeroize_q));
    // All main SM states except the illegal Error state
    main_sm_state_cp: coverpoint main_sm_state_e {
      ignore_bins illegal = {entropy_src_main_sm_pkg::Error};
    }
    ack_sm_state_cp: coverpoint ack_sm_state_e {
      ignore_bins illegal = {entropy_src_ack_sm_pkg::Error};
    }
    source_cp: coverpoint {zeroize_reg, zeroize_pin} {
      bins via_reg = {2'b10};
      bins via_pin = {2'b01};
    }
  endgroup

  entropy_src_zeroize_cov_grp entropy_src_zeroize_cov_grp1 = new();

endinterface

`endif
