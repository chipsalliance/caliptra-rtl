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

interface sha256_ctrl_cov_if     
    (
    input logic           clk,
    input logic           reset_n,
    input logic           cptra_pwrgood

);

    logic init;
    logic next;
    logic mode;
    logic zeroize;
    logic ready;
    logic valid;
    logic wntz_mode;
    logic [3:0] wntz_w;
    logic wntz_n_mode;


    logic [1 : 0] hash_cmd;

    logic wntz_w_invalid;
    logic wntz_mode_invalid;
    logic wntz_j_invalid;
    
    assign init = sha256_ctrl.sha256_inst.init_reg;
    assign next = sha256_ctrl.sha256_inst.next_reg;
    assign mode = sha256_ctrl.sha256_inst.mode_reg;
    assign zeroize = sha256_ctrl.sha256_inst.zeroize_reg;
    assign ready = sha256_ctrl.sha256_inst.ready_reg;
    assign valid = sha256_ctrl.sha256_inst.digest_valid_reg;

    assign wntz_mode = sha256_ctrl.sha256_inst.wntz_mode;
    assign wntz_w = sha256_ctrl.sha256_inst.wntz_w;
    assign wntz_n_mode = sha256_ctrl.sha256_inst.wntz_n_mode;

    assign hash_cmd = {next, init};

    assign wntz_w_invalid = sha256_ctrl.sha256_inst.wntz_w_invalid;
    assign wntz_mode_invalid = sha256_ctrl.sha256_inst.wntz_mode_invalid;
    assign wntz_j_invalid = sha256_ctrl.sha256_inst.wntz_j_invalid;

    covergroup sha256_ctrl_cov_grp @(posedge clk);
        reset_cp: coverpoint reset_n;
        // cptra_pwrgood_cp: coverpoint cptra_pwrgood;

        init_cp: coverpoint init;
        next_cp: coverpoint next;
        mode_cp: coverpoint mode;
        zeroize_cp: coverpoint zeroize;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;
        wntz_mode_cp: coverpoint wntz_mode;
        wntz_n_mode_cp: coverpoint wntz_n_mode;
        wntz_w_cp: coverpoint wntz_w { bins wntz_w_bin[] = {4'd1, 4'd2, 4'd4, 4'd8}; }

        hash_cmd_cp: coverpoint hash_cmd  {bins cmd[]   = (0, 0 => 1, 2 => 0, 0);}

        wntz_w_invalid_cp: coverpoint wntz_w_invalid;
        wntz_mode_invalid_cp: coverpoint wntz_mode_invalid;
        wntz_j_invalid_cp: coverpoint wntz_j_invalid;

        init_ready_cp: cross ready, init;
        // next_ready_cp: cross ready, next;
        zeroize_ready_cp: cross ready, zeroize;
        mode_ready_cp: cross ready, mode;
        zeroize_init_cp: cross zeroize, init;
        zeroize_next_cp: cross zeroize, next;

        wntzmode_init_cp: cross wntz_mode, init{
            ignore_bins invalid_case = binsof(wntz_mode) intersect {1} && binsof(init) intersect {0};
        }
        wntzmode_ready_cp: cross ready, wntz_mode;
        wntzmode_zeroize_cp: cross zeroize, wntz_mode;
        wntz_n_w_cp: cross wntz_n_mode, wntz_w_cp;


    endgroup

    sha256_ctrl_cov_grp sha256_ctrl_cov_grp1 = new();

endinterface

`endif