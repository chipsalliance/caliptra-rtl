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

`ifndef VERILATOR

interface hmac256_drbg_cov_if
    (
    input logic           clk,
    input logic           reset_n
);

    logic init;
    logic next;
    logic zeroize;
    logic ready;
    logic valid;

    logic [1 : 0] hmac256_drbg_cmd;
    logic [4 : 0] drbg_state;
    logic [255 : 0] prime;
    logic [255 : 0] drbg;
    logic failure_check;
    logic [255 : 0] hmac_tag;
    logic [1 : 0] failure_reason;
    logic [1 : 0] active_mode;

    parameter logic [255:0] HMAC_DRBG_PRIME = hmac256_drbg.HMAC_DRBG_PRIME;

    assign init = hmac256_drbg.init_cmd;
    assign next = hmac256_drbg.next_cmd;
    assign zeroize = hmac256_drbg.zeroize;
    assign ready = hmac256_drbg.ready_reg;
    assign valid = hmac256_drbg.valid_reg;

    assign hmac256_drbg_cmd = {next, init};

    assign drbg_state = hmac256_drbg.drbg_st_reg;
    assign drbg = hmac256_drbg.drbg;
    assign failure_check = hmac256_drbg.failure_check;
    assign hmac_tag = hmac256_drbg.HMAC_tag;

    assign failure_reason = (hmac_tag == '0)              ? 2'd1 :
                            (hmac_tag >= HMAC_DRBG_PRIME) ? 2'd2 : 2'd0;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)                                     active_mode <= 2'd0;
        else if (zeroize)                                 active_mode <= 2'd0;
        else if (ready && (drbg_state == 5'd0) && init)   active_mode <= 2'd1;
        else if (ready && (drbg_state == 5'd0) && next)   active_mode <= 2'd2;
    end

    covergroup hmac256_drbg_control_cg @(posedge clk);
        reset_cp: coverpoint reset_n;

        init_cp: coverpoint init;
        next_cp: coverpoint next;
        zeroize_cp: coverpoint zeroize;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;

        hmac_cmd_cp: coverpoint hmac256_drbg_cmd  {bins cmd[]   = (0, 0 => 1, 2 => 0, 0);}

        // T rejected (T == 0 or T >= HMAC_DRBG_PRIME) sampled at CHCK_ST so
        // both accept and reject paths are covered.
        failure_check_cp: coverpoint failure_check iff (drbg_state == 5'd11);

        // Separate the two reject conditions so a broken comparator is caught.
        failure_reason_cp: coverpoint failure_reason iff (drbg_state == 5'd11) {
            bins accepted_in_range = {2'd0};
            bins rejected_zero     = {2'd1};
            bins rejected_ge_prime = {2'd2};
        }

        hmac_tag_boundary_cp: coverpoint hmac_tag iff (drbg_state == 5'd11) {
            bins zero      = {256'd0};
            bins q_minus_1 = {HMAC_DRBG_PRIME - 256'd1};
            bins q         = {HMAC_DRBG_PRIME};
            bins max       = {{256{1'b1}}};
        }

        // Rejection outcomes attributed to originating command (INIT vs NEXT).
        mode_at_chck_cp: coverpoint active_mode iff (drbg_state == 5'd11) {
            bins init_mode = {2'd1};
            bins next_mode = {2'd2};
        }

        // Zeroize timing at representative busy states: K11 (init phase),
        // T (generate phase), and K3 (retry phase).
        zeroize_state_cp: coverpoint drbg_state iff (zeroize) {
            bins idle       = {5'd0};
            bins init_phase = {5'd4};
            bins gen_phase  = {5'd10};
            bins retry      = {5'd12};
        }

        init_ready_cp: cross ready, init {
            illegal_bins illegal_init_when_ready_low = binsof(init) intersect {1} && binsof(ready) intersect {0};
        }

        next_ready_cp: cross ready, next {
            illegal_bins illegal_next_when_ready_low = binsof(next) intersect {1} && binsof(ready) intersect {0};
        }
        zeroize_ready_cp: cross ready, zeroize;
        zeroize_init_cp: cross zeroize, init;
        zeroize_next_cp: cross zeroize, next;

        failure_by_mode_x: cross mode_at_chck_cp, failure_check_cp;

    endgroup

    covergroup hmac256_drbg_state_cg @(posedge clk);
        drbg_state_cp: coverpoint drbg_state {
            bins all_states[] = {[0:14]};
        }
    endgroup

    hmac256_drbg_state_cg hmac256_drbg_state_cov = new();
    hmac256_drbg_control_cg hmac256_drbg_control_cov = new();

endinterface

`endif
