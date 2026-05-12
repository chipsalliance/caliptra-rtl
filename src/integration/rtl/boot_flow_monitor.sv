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
// Boot Flow Monitor
// Monitors ICCM fetch activity to detect ROM->FMC and FMC->RT transitions.
// Outputs mubi4 signals consumed by the keyvault enforcement logic.

module boot_flow_monitor
    import caliptra_prim_mubi_pkg::*;
    import el2_pkg::*;
    #(
    `include "el2_param.vh"
    )
    (
        input logic clk,
        input logic cptra_uc_rst_b,

        // ICCM memory interface (from el2_mem_export)
        input logic [pt.ICCM_NUM_BANKS-1:0]                                        iccm_clken,
        input logic [pt.ICCM_NUM_BANKS-1:0]                                        iccm_wren_bank,
        input logic [pt.ICCM_NUM_BANKS-1:0][pt.ICCM_BITS-1:pt.ICCM_BANK_INDEX_LO] iccm_addr_bank,

        // Region bounds (from shadow registers)
        input logic [pt.ICCM_BITS-1:0] iccm_fmc_start_addr,
        input logic [pt.ICCM_BITS-1:0] iccm_fmc_end_addr,
        input logic [pt.ICCM_BITS-1:0] iccm_rt_start_addr,
        input logic [pt.ICCM_BITS-1:0] iccm_rt_end_addr,

        // Control
        input logic iccm_region_lock,
        input logic boot_flow_monitor_en,
        input logic fw_update_rst_window,

        // Outputs
        output mubi4_t boot_flow_fmc_o,
        output mubi4_t boot_flow_rt_o,
        output mubi4_t boot_flow_error_o
    );

    // Internal signals
    logic [pt.ICCM_NUM_BANKS-1:0]                   iccm_read_en;
    logic [pt.ICCM_NUM_BANKS-1:0][pt.ICCM_BITS-1:0] iccm_read_addr;
    logic iccm_read_fmc;
    logic iccm_read_rt;
    logic iccm_read_any;

    mubi4_t boot_flow_fmc_q;
    mubi4_t boot_flow_rt_q;
    mubi4_t boot_flow_error_q;

    // ICCM fetch region detection
    // Reconstruct full byte address from per-bank row address + bank index
    always_comb begin
        iccm_read_fmc = '0;
        iccm_read_rt  = '0;
        iccm_read_any = '0;
        for (int bank = 0; bank < pt.ICCM_NUM_BANKS; bank++) begin
            iccm_read_en[bank] = iccm_clken[bank] && ~iccm_wren_bank[bank];
            iccm_read_addr[bank] = {iccm_addr_bank[bank], pt.ICCM_BANK_BITS'(bank), {(pt.ICCM_BANK_INDEX_LO - pt.ICCM_BANK_BITS){1'b0}}};

            iccm_read_fmc |= iccm_read_en[bank] && (iccm_read_addr[bank] inside {[iccm_fmc_start_addr:iccm_fmc_end_addr]});
            iccm_read_rt  |= iccm_read_en[bank] && (iccm_read_addr[bank] inside {[iccm_rt_start_addr:iccm_rt_end_addr]});
            iccm_read_any |= iccm_read_en[bank];
        end
    end

    // Boot flow state machine
    // Synchronous soft-reset via fw_update_rst_window clears boot_flow flops cleanly
    // on posedge clk before cptra_uc_rst_b deasserts. This eliminates RDC metastability
    // from the async reset path into the cptra_noncore_rst_b domain.
    always_ff @(posedge clk or negedge cptra_uc_rst_b) begin
        if (!cptra_uc_rst_b) begin
            boot_flow_fmc_q   <= MuBi4False;
            boot_flow_rt_q    <= MuBi4False;
            boot_flow_error_q <= MuBi4False;
        end else if (fw_update_rst_window) begin
            boot_flow_fmc_q   <= MuBi4False;
            boot_flow_rt_q    <= MuBi4False;
            boot_flow_error_q <= MuBi4False;
        end else if (boot_flow_monitor_en) begin
            // Transition from ROM to FMC: first fetch from FMC region after lock
            if (iccm_region_lock && mubi4_test_false_strict(boot_flow_fmc_q) && iccm_read_fmc) begin
                boot_flow_fmc_q <= MuBi4True;
            end

            // Transition from FMC to RT: first fetch from RT region after lock
            if (iccm_region_lock && mubi4_test_false_strict(boot_flow_rt_q) && iccm_read_rt) begin
                boot_flow_rt_q <= MuBi4True;
            end

            // Error conditions
            boot_flow_error_q <= (iccm_read_any && !iccm_region_lock) ||
                                 (mubi4_test_false_strict(boot_flow_fmc_q) && mubi4_test_true_strict(boot_flow_rt_q)) ||
                                 mubi4_test_invalid(boot_flow_fmc_q) || mubi4_test_invalid(boot_flow_rt_q) || mubi4_test_invalid(boot_flow_error_q)
                                 ? MuBi4True : boot_flow_error_q;
        end
    end

    assign boot_flow_fmc_o   = boot_flow_fmc_q;
    assign boot_flow_rt_o    = boot_flow_rt_q;
    assign boot_flow_error_o = boot_flow_error_q;

endmodule
