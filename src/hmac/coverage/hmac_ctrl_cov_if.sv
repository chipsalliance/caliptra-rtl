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

interface hmac_ctrl_cov_if     
    (
    input logic           clk,
    input logic           reset_n,
    input logic           cptra_pwrgood

);

    logic init;
    logic next;
    logic zeroize;
    logic ready;
    logic valid;
    
    logic core_tag_we;

    logic [1 : 0] hmac_cmd;
    
    assign init = hmac_ctrl.hmac_inst.init_reg;
    assign next = hmac_ctrl.hmac_inst.next_reg;
    assign zeroize = hmac_ctrl.hmac_inst.zeroize_reg;
    assign ready = hmac_ctrl.hmac_inst.ready_reg;
    assign valid = hmac_ctrl.hmac_inst.tag_valid_reg;

    assign core_tag_we = hmac_ctrl.hmac_inst.core_tag_we;

    assign hmac_cmd = {next, init};

    covergroup hmac_ctrl_cov_grp @(posedge clk);
        reset_cp: coverpoint reset_n;
        cptra_pwrgood_cp: coverpoint cptra_pwrgood;

        init_cp: coverpoint init;
        next_cp: coverpoint next;
        zeroize_cp: coverpoint zeroize;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;

        core_tag_we_cp: coverpoint core_tag_we;

        hmac_cmd_cp: coverpoint hmac_cmd  {bins cmd[]   = (0, 0 => 1, 2 => 0, 0);}

        init_ready_cp: cross ready, init;
        next_ready_cp: cross ready, next;
        zeroize_ready_cp: cross ready, zeroize;
        zeroize_init_cp: cross zeroize, init;
        zeroize_next_cp: cross zeroize, next;

    endgroup

    hmac_ctrl_cov_grp hmac_ctrl_cov_grp1 = new();

endinterface

`endif