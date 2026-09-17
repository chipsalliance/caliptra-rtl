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

interface pcrvault_cov_if     
    import pv_defines_pkg::*;
    (
    input logic clk,
    input logic rst_b,
    input logic core_only_rst_b,
    input logic cptra_pwrgood,
    input logic fw_update_rst_window
);

    logic [PV_NUM_PCR-1:0] pcr_ctrl_lock;
    logic [PV_NUM_PCR-1:0] pcr_ctrl_clear;

    logic [PV_NUM_WRITE-1:0] pv_write_en;

    // Latched version of lock — captures that lock was set before an async reset clears it.
    // lock is async-cleared by core_only_rst_b, so a sampled cross would never see
    // lock=1 and core_only_rst_b=0 simultaneously. This signal holds the pre-reset state.
    logic lock_was_set;
    always_ff @(posedge clk or negedge cptra_pwrgood) begin
        if (!cptra_pwrgood)
            lock_was_set <= 1'b0;
        else if (|pcr_ctrl_lock)
            lock_was_set <= 1'b1;
        else if (core_only_rst_b && rst_b)
            lock_was_set <= 1'b0;
    end
    
    //Assign clear and locks of each PCR_CTRL reg to corresponding bit in the intermediate bus
    generate
        for(genvar i = 0; i < PV_NUM_PCR; i++) begin
            assign pcr_ctrl_lock[i]  = pv.pv_reg_hwif_out.PCR_CTRL[i].lock;
            assign pcr_ctrl_clear[i] = pv.pv_reg_hwif_out.PCR_CTRL[i].clear;
        end
    endgenerate

    generate
        for(genvar client = 0; client < PV_NUM_WRITE; client++) begin
            assign pv_write_en[client] = pv.pv_write[client].write_en;
        end
    endgenerate

    covergroup pcrvault_top_cov_grp @(posedge clk);
        option.per_instance = 1;

        lock: coverpoint (|pcr_ctrl_lock) {
            bins unlocked = {1'b0};
            bins locked   = {1'b1};
        }
        clear: coverpoint (|pcr_ctrl_clear) {
            bins inactive = {1'b0};
            bins active   = {1'b1};
        }

        //Cover warm reset assertion while regs are locked/cleared
        lockXwarm_rst:      cross lock, rst_b;
        clearXwarm_rst:     cross clear, rst_b;

        //Cover cold reset assertion while regs are locked/cleared
        lockXcold_rst:      cross lock, cptra_pwrgood;
        clearXcold_rst:     cross clear, cptra_pwrgood;

        //Cover core reset with lock_was_set — verifies lock survives warm reset
        //but clears on core_only_rst_b. Uses latched signal because lock is
        //async-cleared by core_only_rst_b (can't sample both high simultaneously).
        cp_lock_was_set: coverpoint lock_was_set;
        cp_core_rst:     coverpoint core_only_rst_b;
        lock_was_setXcore_rst: cross cp_lock_was_set, cp_core_rst;
        clearXcore_rst:        cross clear, cp_core_rst;

        //Cover fw_update_rst_window — security bypass that re-enables clear when locked
        cp_fw_update_window: coverpoint fw_update_rst_window;
        lock_was_setXfw_update_window: cross cp_lock_was_set, cp_fw_update_window;

        //Cover crypto writes to locked/cleared regs
        lockXpv_write:      cross lock, pv_write_en;
        clearXpv_write:     cross clear, pv_write_en;

    endgroup

    pcrvault_top_cov_grp pcrvault_top_cov_grp1 = new();
    
endinterface

`endif
