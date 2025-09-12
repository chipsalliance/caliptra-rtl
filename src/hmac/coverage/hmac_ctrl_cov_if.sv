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
    import kv_defines_pkg::*;  
    (
    input logic           clk,
    input logic           reset_n,
    input logic           cptra_pwrgood,

    input logic           ocp_lock_in_progress

);

    logic init;
    logic next;
    logic zeroize;
    logic mode;
    logic ready;
    logic valid;
    
    logic core_tag_we;

    logic [1 : 0] hmac_cmd;

    kv_write_filter_metrics_t kv_write_metrics;
    kv_write_ctrl_reg_t kv_write_ctrl_reg;

    assign init = hmac_ctrl.hmac_inst.init_reg;
    assign next = hmac_ctrl.hmac_inst.next_reg;
    assign zeroize = hmac_ctrl.hmac_inst.zeroize_reg;
    assign mode = hmac_ctrl.hmac_inst.mode_reg;
    assign ready = hmac_ctrl.hmac_inst.ready_reg;
    assign valid = hmac_ctrl.hmac_inst.tag_valid_reg;

    assign core_tag_we = hmac_ctrl.hmac_inst.core_tag_we;

    assign hmac_cmd = {next, init};

    assign kv_write_metrics = hmac_ctrl.hmac_inst.kv_write_metrics;
    assign kv_write_ctrl_reg = hmac_ctrl.hmac_inst.kv_write_ctrl_reg;

    covergroup hmac_ctrl_cov_grp @(posedge clk);
        reset_cp: coverpoint reset_n;
        //cptra_pwrgood_cp: coverpoint cptra_pwrgood;

        init_cp: coverpoint init;
        next_cp: coverpoint next;
        zeroize_cp: coverpoint zeroize;
        mode_cp: coverpoint mode;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;

        core_tag_we_cp: coverpoint core_tag_we;

        hmac_cmd_cp: coverpoint hmac_cmd  {bins cmd[]   = (0, 0 => 1, 2 => 0, 0);}

        //init_ready_cp: cross ready, init;
        //next_ready_cp: cross ready, next;
        mode_ready_cp: cross ready, mode;
        zeroize_ready_cp: cross ready, zeroize;
        zeroize_init_cp: cross zeroize, init;
        zeroize_next_cp: cross zeroize, next;
        init_mode_cp: cross init, mode;
        next_mode_cp: cross next, mode;

    endgroup

    covergroup hmac_ocp_lock_cov_grp @(posedge clk);

        ocp_lock_in_progress_cp: coverpoint ocp_lock_in_progress;

        kv_read_entry_0_cp: coverpoint {kv_write_metrics.kv_data0_present, kv_write_metrics.kv_data0_entry} 
        iff (init | next) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        kv_read_entry_1_cp: coverpoint {kv_write_metrics.kv_data1_present, kv_write_metrics.kv_data1_entry} 
        iff (init | next) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        kv_write_entry_cp: coverpoint {kv_write_ctrl_reg.write_en, kv_write_metrics.kv_write_entry}
        iff (init | next) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        ocp_lock_X_kv_entry: cross ocp_lock_in_progress_cp, kv_write_entry_cp, kv_read_entry_0_cp, kv_read_entry_1_cp;

    endgroup    

    hmac_ctrl_cov_grp hmac_ctrl_cov_grp1 = new();

    hmac_ocp_lock_cov_grp hmac_ocp_lock_cov_grp1 = new();

endinterface

`endif