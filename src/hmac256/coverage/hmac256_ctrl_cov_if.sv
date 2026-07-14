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

interface hmac256_ctrl_cov_if
    (
    input logic           clk,
    input logic           reset_n,
    input logic           cptra_pwrgood
);

    logic init;
    logic next;
    logic zeroize;
    logic mode;
    logic last;
    logic ready;
    logic valid;
    logic restore;
    logic is_last_op;

    logic core_tag_we;

    logic [3 : 0] hmac256_cmd;

    assign init       = hmac256_ctrl.hmac256_inst.init_reg;
    assign next       = hmac256_ctrl.hmac256_inst.next_reg;
    assign zeroize    = hmac256_ctrl.hmac256_inst.zeroize_reg;
    assign mode       = hmac256_ctrl.hmac256_inst.mode_reg;
    assign last       = hmac256_ctrl.hmac256_inst.last_reg;
    assign ready      = hmac256_ctrl.hmac256_inst.ready_reg;
    assign valid      = hmac256_ctrl.hmac256_inst.tag_valid_reg;
    assign restore    = hmac256_ctrl.hmac256_inst.restore_reg;
    assign is_last_op = hmac256_ctrl.hmac256_inst.is_last_op_reg;

    assign core_tag_we = hmac256_ctrl.hmac256_inst.core_tag_we;

    // hmac256_cmd bit layout: {restore, last, next, init}.
    assign hmac256_cmd = {hmac256_ctrl.hmac256_inst.hwif_out.HMAC256_CTRL.RESTORE.value,
                          hmac256_ctrl.hmac256_inst.hwif_out.HMAC256_CTRL.LAST.value,
                          hmac256_ctrl.hmac256_inst.hwif_out.HMAC256_CTRL.NEXT.value,
                          hmac256_ctrl.hmac256_inst.hwif_out.HMAC256_CTRL.INIT.value};

    covergroup hmac256_ctrl_cov_grp @(posedge clk);
        reset_cp: coverpoint reset_n;

        zeroize_cp: coverpoint zeroize;
        mode_cp: coverpoint mode;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;
        is_last_op_cp: coverpoint is_last_op;

        core_tag_we_cp: coverpoint core_tag_we;

        hmac256_cmd_cp: coverpoint hmac256_cmd {
            bins init          = (0 => 'h1 => 0);
            bins next          = (0 => 'h2 => 0);
            bins last_alone    = (0 => 'h4 => 0);
            bins init_last     = (0 => 'h5 => 0);
            bins next_last     = (0 => 'h6 => 0);
            bins restore_alone = (0 => 'h8 => 0);
            bins restore_next  = (0 => 'hA => 0);
            bins restore_last  = (0 => 'hC => 0);
        }

        mode_ready_cp: cross ready, mode;
        zeroize_ready_cp: cross ready, zeroize;
        zeroize_init_cp: cross zeroize, init;
        zeroize_next_cp: cross zeroize, next;
        init_mode_cp: cross init, mode;
        next_mode_cp: cross next, mode;

    endgroup

    hmac256_ctrl_cov_grp hmac256_ctrl_cov_grp1 = new();

endinterface

`endif
