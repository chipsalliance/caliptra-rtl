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

interface sha512_ctrl_cov_if     
    (
    input logic           clk,
    input logic           reset_n,
    input logic           cptra_pwrgood

);

    logic init;
    logic next;
    logic [1 : 0] mode;
    logic zeroize;
    logic restore;
    logic ready;
    logic valid;
    
    logic pcr_sign_we;
    logic gen_hash_start;
    logic gen_hash_ip;
    logic dest_data_avail;

    logic [1 : 0] hash_cmd;
    
    assign init = sha512_ctrl.sha512_inst.init_reg;
    assign next = sha512_ctrl.sha512_inst.next_reg;
    assign mode = sha512_ctrl.sha512_inst.mode_reg;
    assign restore = sha512_ctrl.sha512_inst.restore_reg;
    assign zeroize = sha512_ctrl.sha512_inst.zeroize_reg;
    assign ready = sha512_ctrl.sha512_inst.ready_reg;
    assign valid = sha512_ctrl.sha512_inst.digest_valid_reg;

    assign pcr_sign_we = sha512_ctrl.sha512_inst.pcr_sign_we;
    assign gen_hash_start = sha512_ctrl.sha512_inst.gen_hash_start;
    assign gen_hash_ip = sha512_ctrl.sha512_inst.gen_hash_ip;
    assign dest_data_avail = sha512_ctrl.sha512_inst.dest_data_avail;

    assign hash_cmd = {next, init};

    covergroup sha512_ctrl_cov_grp @(posedge clk);
        reset_cp: coverpoint reset_n;
        // cptra_pwrgood_cp: coverpoint cptra_pwrgood;

        init_cp: coverpoint init;
        next_cp: coverpoint next;
        mode_cp: coverpoint mode; //TB
        restore_cp: coverpoint restore;
        zeroize_cp: coverpoint zeroize;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;

        pcr_sign_we_cp: coverpoint pcr_sign_we;
        gen_hash_start_cp: coverpoint gen_hash_start;
        gen_hash_ip_cp: coverpoint gen_hash_ip;
        dest_data_avail_cp: coverpoint dest_data_avail;

        hash_cmd_cp: coverpoint hash_cmd  {bins cmd[]   = (0, 0 => 1, 2 => 0, 0);}

        init_ready_cp: cross ready, init; //TB
        next_ready_cp: cross ready, next; //TB
        zeroize_ready_cp: cross ready, zeroize;
        mode_ready_cp: cross ready, mode;
        pcr_ready_cp: cross ready, gen_hash_start; //TB
        pcr_init_cp: cross gen_hash_ip_cp, init; 
        pcr_next_cp: cross gen_hash_ip_cp, next; 
        zeroize_pcr_cp: cross zeroize, gen_hash_ip_cp;
        zeroize_init_cp: cross zeroize, init; //TB
        zeroize_next_cp: cross zeroize, next; //TB
        zeroize_restore_cp: cross zeroize, restore;

    endgroup

    sha512_ctrl_cov_grp sha512_ctrl_cov_grp1 = new();

endinterface

`endif