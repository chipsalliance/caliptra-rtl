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

    logic awaiting_zeroize;
    logic invalid_cmd_error_edge;

    logic [4:0] hmac256_cmd;

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

    assign awaiting_zeroize       = hmac256_ctrl.hmac256_inst.awaiting_zeroize;
    assign invalid_cmd_error_edge = hmac256_ctrl.hmac256_inst.invalid_cmd_error_edge;

    // hmac256_cmd bit layout: {restore, last, next, init, zeroize}.
    assign hmac256_cmd = {hmac256_ctrl.hmac256_inst.hwif_out.HMAC256_CTRL.RESTORE.value,
                          hmac256_ctrl.hmac256_inst.hwif_out.HMAC256_CTRL.LAST.value,
                          hmac256_ctrl.hmac256_inst.hwif_out.HMAC256_CTRL.NEXT.value,
                          hmac256_ctrl.hmac256_inst.hwif_out.HMAC256_CTRL.INIT.value,
                          hmac256_ctrl.hmac256_inst.hwif_out.HMAC256_CTRL.ZEROIZE.value};

    covergroup hmac256_ctrl_cov_grp @(posedge clk);
        reset_cp: coverpoint reset_n;
        //cptra_pwrgood_cp: coverpoint cptra_pwrgood;

        init_cp: coverpoint init;
        next_cp: coverpoint next;
        zeroize_cp: coverpoint zeroize;
        mode_cp: coverpoint mode;
        last_cp: coverpoint last;
        restore_cp: coverpoint restore;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;
        is_last_op_cp: coverpoint is_last_op;
        awaiting_zeroize_cp: coverpoint awaiting_zeroize;

        core_tag_we_cp: coverpoint core_tag_we;

        // error0_sts is hwset by invalid_cmd_error_edge. error1/2/3 are
        // reserved slots with no hardware source in hmac256.
        error0_sts_cp: coverpoint invalid_cmd_error_edge { bins fired = {1'b1}; }

        // Every combination of {restore, last, next, init, zeroize}.
        hmac256_cmd_cp: coverpoint hmac256_cmd {
            bins cmd[] = {[0:31]};
        }

        // Every CTRL encoding crossed with MODE (HMAC-224 x HMAC-256).
        hmac256_cmd_x_mode: cross hmac256_cmd_cp, mode_cp;

        mode_ready_cp:    cross ready, mode;
        zeroize_ready_cp: cross ready, zeroize;

        // Did zeroize, restore, and error0 all fire in both modes.
        zeroize_x_mode_cp: cross zeroize_cp, mode_cp;
        restore_x_mode_cp: cross restore_cp, mode_cp;
        error0_x_mode_cp:  cross error0_sts_cp, mode_cp;

    endgroup

    hmac256_ctrl_cov_grp hmac256_ctrl_cov_grp1 = new();

endinterface

`endif
