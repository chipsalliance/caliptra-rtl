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

interface caliptra_top_cov_if   
    import soc_ifc_pkg::*;  
    (
    input logic clk,
    //SoC AXI Interface
    axi_if.w_sub s_axi_w_if,
    axi_if.r_sub s_axi_r_if,
    input logic [63:0] generic_input_wires,
    input logic cptra_rst_b,
    input logic cptra_pwrgood,
    input logic scan_mode,
    input security_state_t security_state,
    input logic cptra_error_fatal
);
    
    logic clk_gating_en;
    logic cpu_halt_status;
    logic wdt_timer1_en;
    logic wdt_timer2_en;
    logic nmi_int;

    assign clk_gating_en = caliptra_top.cg.clk_gate_en;
    assign cpu_halt_status = caliptra_top.cg.cpu_halt_status;
    assign wdt_timer1_en = caliptra_top.soc_ifc_top1.i_wdt.timer1_en;
    assign wdt_timer2_en = caliptra_top.soc_ifc_top1.i_wdt.timer2_en;
    assign nmi_int = caliptra_top.nmi_int;
    

    covergroup caliptra_top_cov_grp @(posedge clk);
        option.per_instance = 1;

        //-----------------------------------------
        //WDT coverpoints
        //-----------------------------------------
        wdt_t1: coverpoint wdt_timer1_en;
        wdt_t2: coverpoint wdt_timer2_en;
        wdt_t1Xt2: cross wdt_t1, wdt_t2;
        // wdt_t1t2Xwarmrst: cross wdt_t1Xt2, cptra_rst_b;
        // wdt_t1t2Xcoldrst: cross wdt_t1Xt2, cptra_pwrgood;

        //-----------------------------------------
        //CLK GATING coverpoints
        //-----------------------------------------
        axi_rd_txn:         coverpoint s_axi_r_if.arvalid && s_axi_r_if.arready {
            bins single_axi_rd_txn = (0 => 1 => 0);
            bins b2b_axi_rd_txn = (1 [*5]); //5 rd txns in a row
        }
        axi_rd_rsp:         coverpoint s_axi_r_if.rvalid && s_axi_r_if.rready {
            bins axi_rd_hshake = {1'b1};
            bins single_axi_rd_rsp = (0 => 1 => 0);
        }
        axi_wr_txn:         coverpoint s_axi_w_if.awvalid && s_axi_w_if.awready {
            bins single_axi_wr_txn = (0 => 1 => 0);
            bins b2b_axi_wr_txn = (1 [*5]); //5 wr txns in a row
        }
        axi_wr_rsp:         coverpoint s_axi_w_if.bvalid && s_axi_w_if.bready {
            bins axi_wr_hshake = {1'b1};
            bins single_axi_wr_rsp = (0 => 1 => 0);
        }
        axi_any_txn:        coverpoint (s_axi_r_if.arvalid && s_axi_r_if.arready) || (s_axi_w_if.awvalid && s_axi_w_if.awready) {
            bins single_axi_txn = (0 => 1 => 0);
            bins b2b_axi_txn = (1 [*5]); //5 txns in a row
        }
        cg_en:              coverpoint clk_gating_en;
        core_asleep_value:  coverpoint cpu_halt_status;
        core_asleep_trans:  coverpoint cpu_halt_status {
            bins bin01 = (0 => 1);
            bins bin10 = (1 => 0);
        }
        warm_rst:           coverpoint cptra_rst_b;

        scan:               coverpoint scan_mode;
        debug:              coverpoint security_state.debug_locked;
        fatal_error:        coverpoint cptra_error_fatal;
        nmi:                coverpoint nmi_int;
        generic:            coverpoint generic_input_wires {
            bins byte0_active  = generic with (|(item & (64'hFF <<  0)));
            bins byte1_active  = generic with (|(item & (64'hFF <<  8)));
            bins byte2_active  = generic with (|(item & (64'hFF << 16)));
            bins byte3_active  = generic with (|(item & (64'hFF << 24)));
            bins byte4_active  = generic with (|(item & (64'hFF << 32)));
            bins byte5_active  = generic with (|(item & (64'hFF << 40)));
            bins byte6_active  = generic with (|(item & (64'hFF << 48)));
            bins byte7_active  = generic with (|(item & (64'hFF << 56)));
        }

        enXcore_asleep:             cross cg_en, core_asleep_value {
            ignore_bins b0 = enXcore_asleep with ((cg_en == 0) && (core_asleep_value == 1));
        }
        enXcore_asleepXwarm_rst:    cross enXcore_asleep, warm_rst;
        enXcore_asleepXcold_rst:    cross enXcore_asleep, cptra_pwrgood;
        // {
        //     ignore_bins b0 = enXcore_asleepXwarm_rst with ((cg_en == 1) && (core_asleep_value == 1) && (warm_rst == 0));
        // }
        enXcore_asleepXwdt1:        cross enXcore_asleep, wdt_t1;
        enXcore_asleepXwdt2:        cross enXcore_asleep, wdt_t2;

        enXcore_asleepXscan:        cross enXcore_asleep, scan;
        enXcore_asleepXdebug:       cross enXcore_asleep, debug;
        enXcore_asleepXfatalerr:    cross enXcore_asleep, fatal_error;
        enXcore_asleepXnmi:         cross enXcore_asleep, nmi;
        enXcore_asleepXaxi:         cross enXcore_asleep, axi_any_txn;
        enXcore_asleepXgeneric:     cross enXcore_asleep, generic;
    endgroup

    covergroup generic_input_wires_cg(input int index) @(posedge clk);
        option.per_instance = 1;
        value:      coverpoint generic_input_wires[index];
        transition: coverpoint generic_input_wires[index] {
            bins bin01 = (0 => 1);
            bins bin10 = (1 => 0);
        }
    endgroup

    // CLK_GATING_cov_grp CLK_GATING_cov_grp1 = new();
    // WDT_cov_grp WDT_cov_grp1 = new();
    caliptra_top_cov_grp caliptra_top_cov_grp1 = new();
    
//    generic_input_wires_cg giw_cg[64];
    //foreach(giw_cg[i]) giw_cg[i] = new(generic_input_wires[i]);
    generate
        for(genvar i = 0; i < 64; i++) begin: GIW_LOOP
            generic_input_wires_cg giw_cg = new(i);
        end
    endgenerate

endinterface

`endif
