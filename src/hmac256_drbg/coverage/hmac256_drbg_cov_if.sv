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

    parameter logic [255:0] HMAC_DRBG_PRIME = hmac256_drbg.HMAC_DRBG_PRIME;

    assign init = hmac256_drbg.init_cmd;
    assign next = hmac256_drbg.next_cmd;
    assign zeroize = hmac256_drbg.zeroize;
    assign ready = hmac256_drbg.ready_reg;
    assign valid = hmac256_drbg.valid_reg;

    assign hmac256_drbg_cmd = {next, init};

    assign drbg_state = hmac256_drbg.drbg_st_reg;
    assign drbg = hmac256_drbg.drbg;

    covergroup hmac256_drbg_control_cg @(posedge clk);
        reset_cp: coverpoint reset_n;

        init_cp: coverpoint init;
        next_cp: coverpoint next;
        zeroize_cp: coverpoint zeroize;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;

        hmac_cmd_cp: coverpoint hmac256_drbg_cmd  {bins cmd[]   = (0, 0 => 1, 2 => 0, 0);}

        init_ready_cp: cross ready, init {
            illegal_bins illegal_init_when_ready_low = binsof(init) intersect {1} && binsof(ready) intersect {0};
        }

        next_ready_cp: cross ready, next {
            illegal_bins illegal_next_when_ready_low = binsof(next) intersect {1} && binsof(ready) intersect {0};
        }
        zeroize_ready_cp: cross ready, zeroize;
        zeroize_init_cp: cross zeroize, init;
        zeroize_next_cp: cross zeroize, next;

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
