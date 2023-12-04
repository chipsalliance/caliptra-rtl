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


    logic [1 : 0] hash_cmd;
    
    assign init = sha256_ctrl.sha256_inst.init_reg;
    assign next = sha256_ctrl.sha256_inst.next_reg;
    assign mode = sha256_ctrl.sha256_inst.mode_reg;
    assign zeroize = sha256_ctrl.sha256_inst.zeroize_reg;
    assign ready = sha256_ctrl.sha256_inst.ready_reg;
    assign valid = sha256_ctrl.sha256_inst.digest_valid_reg;

    assign hash_cmd = {next, init};

    covergroup sha256_ctrl_cov_grp @(posedge clk);
        reset_cp: coverpoint reset_n;
        cptra_pwrgood_cp: coverpoint cptra_pwrgood;

        init_cp: coverpoint init;
        next_cp: coverpoint next;
        mode_cp: coverpoint mode;
        zeroize_cp: coverpoint zeroize;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;

        hash_cmd_cp: coverpoint hash_cmd  {bins cmd[]   = (0, 0 => 1, 2 => 0, 0);}

        init_ready_cp: cross ready, init;
        next_ready_cp: cross ready, next;
        zeroize_ready_cp: cross ready, zeroize;
        mode_ready_cp: cross ready, mode;
        zeroize_init_cp: cross zeroize, init;
        zeroize_next_cp: cross zeroize, next;

    endgroup

    sha256_ctrl_cov_grp sha256_ctrl_cov_grp1 = new();

endinterface

`endif