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

interface doe_cov_if    
    import kv_defines_pkg::*;   
    import doe_defines_pkg::*;
    (
    input logic           clk,
    input logic           reset_n,
    input logic           cptra_pwrgood,
    input logic           ocp_lock_en,
    input kv_write_t      kv_write
    );

    logic running_uds, running_fe, running_hek;
    doe_cmd_e doe_cmd;

    assign running_uds = doe_ctrl.doe_inst.doe_fsm1.running_uds;
    assign running_fe = doe_ctrl.doe_inst.doe_fsm1.running_fe;
    assign running_hek = doe_ctrl.doe_inst.doe_fsm1.running_hek;
    assign doe_cmd = doe_cmd_e'(doe_ctrl.doe_inst.doe_cmd_reg.cmd);
    
    covergroup doe_cov_grp @(posedge clk);
        running_uds_cp: coverpoint running_uds;
        running_fe_cp: coverpoint running_fe;
        running_hek_cp: coverpoint running_hek;

        ocp_lock_en_cp: coverpoint ocp_lock_en;

        dest_addr_cp: coverpoint kv_write.write_entry  iff (doe_cmd inside {DOE_UDS, DOE_FE, DOE_HEK}) {
            bins lower_slots = {[0:15]};
            bins upper_slots = {[16:22]};
            bins slot_23 = {23};
        }

        dest_addr_X_ocp_lock_en: cross dest_addr_cp, ocp_lock_en_cp;
        
    endgroup

    doe_cov_grp doe_cov_grp1 = new();

endinterface

`endif