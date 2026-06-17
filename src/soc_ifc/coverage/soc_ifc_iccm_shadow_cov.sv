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
//
// Covergroup for ICCM shadow register operations (boot flow enforcement)

`ifndef VERILATOR

module soc_ifc_iccm_shadow_cov (
    input logic clk,
    input logic cptra_rst_b,

    // Shadow register write/read enables (4 registers: fmc_start, fmc_end, rt_start, rt_end)
    input logic [3:0] iccm_shadow_we,
    input logic [3:0] iccm_shadow_re,

    // Shadow register state
    input logic [3:0] iccm_shadow_qe,
    input logic [3:0] iccm_shadow_committed,
    input logic [3:0] iccm_shadow_err_update,
    input logic [3:0] iccm_shadow_err_storage,

    // Lock signal
    input logic       iccm_region_lock
);

    // Detect any write or read event
    logic shadow_write_event, shadow_read_event;
    assign shadow_write_event = |iccm_shadow_we;
    assign shadow_read_event  = |iccm_shadow_re;

    // Register index being accessed
    typedef enum logic [1:0] {
        FMC_START = 0,
        FMC_END   = 1,
        RT_START  = 2,
        RT_END    = 3
    } shadow_reg_t;

    shadow_reg_t active_reg;
    always_comb begin
        if (iccm_shadow_we[0] || iccm_shadow_re[0])      active_reg = FMC_START;
        else if (iccm_shadow_we[1] || iccm_shadow_re[1])  active_reg = FMC_END;
        else if (iccm_shadow_we[2] || iccm_shadow_re[2])  active_reg = RT_START;
        else                                               active_reg = RT_END;
    end

    // =========================================================================
    // cg_iccm_shadow_reg
    // Sampled on any shadow register write or read
    // =========================================================================
    covergroup cg_iccm_shadow_reg @(posedge clk iff (shadow_write_event || shadow_read_event));
        option.per_instance = 1;
        option.name = "cg_iccm_shadow_reg";

        cp_register: coverpoint active_reg {
            bins fmc_start = {FMC_START};
            bins fmc_end   = {FMC_END};
            bins rt_start  = {RT_START};
            bins rt_end    = {RT_END};
        }

        cp_operation: coverpoint {shadow_write_event, shadow_read_event} {
            bins write = {2'b10};
            bins read  = {2'b01};
        }

        cp_locked: coverpoint iccm_region_lock {
            bins unlocked = {1'b0};
            bins locked   = {1'b1};
        }

        cp_committed: coverpoint iccm_shadow_committed[active_reg] {
            bins not_committed = {1'b0};
            bins committed     = {1'b1};
        }

        cp_err_update: coverpoint |iccm_shadow_err_update {
            bins no_error = {1'b0};
            bins error    = {1'b1};
        }

        cp_err_storage: coverpoint |iccm_shadow_err_storage {
            bins no_error = {1'b0};
            bins error    = {1'b1};
        }

        // Key crosses
        reg_X_op: cross cp_register, cp_operation;
        reg_X_locked: cross cp_register, cp_locked;
        op_X_committed: cross cp_operation, cp_committed;
        op_X_err_storage: cross cp_operation, cp_err_storage;
    endgroup

    cg_iccm_shadow_reg cg_iccm_shadow_reg_inst = new();

endmodule

`endif
