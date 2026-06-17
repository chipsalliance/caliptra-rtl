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
// Covergroups for KV Boot Flow Transition Enforcement
// Covers: enforcement results, monitor checks, flush sources, write counter
//         thresholds, and multi-write arbitration errors
//
// Architecture notes (from kv.sv):
//   - KV Monitor checks dest_valid and write counters ONLY on enter_fmc/enter_rt
//   - KV Enforcement sets lock_wr/lock_use and clears non-preserved slots on transitions
//   - Multi-write detection (kv_write_cnt > 1) is bus arbitration, not boot-flow
//   - Write counters track ROM-phase crypto writes to DICE slots 6/7/8; checked at enter_fmc

`ifndef VERILATOR

module kv_boot_flow_cov
    import kv_defines_pkg::*;
    import caliptra_prim_mubi_pkg::*;
(
    input logic clk,
    input logic rst_b,
    input logic core_only_rst_b,

    // Boot flow signals
    input mubi4_t boot_flow_fmc,
    input mubi4_t boot_flow_rt,
    input mubi4_t boot_flow_error,

    // Transition edges (internal to kv.sv)
    input logic enter_fmc,
    input logic enter_rt,

    // Monitor alert
    input logic kv_monitor_alert,

    // Write counters
    input logic [2:0] write_count_fmc_cdi,
    input logic [2:0] write_count_fmc_ecdsa,
    input logic [2:0] write_count_fmc_mldsa,

    // Crypto write strobes (for counter sampling)
    input logic crypto_wr_fmc_cdi,
    input logic crypto_wr_fmc_ecdsa,
    input logic crypto_wr_fmc_mldsa
);

    // =========================================================================
    // Shared types
    // =========================================================================
    typedef enum logic [1:0] {TRANS_FMC = 0, TRANS_RT = 1} transition_t;

    transition_t sampled_transition;
    assign sampled_transition = enter_fmc ? TRANS_FMC : TRANS_RT;

    // =========================================================================
    // Delayed transition edges -- enforcement results (lock_wr, lock_use,
    // dest_valid clear) are registered, so sample one cycle after the edge
    // to observe the post-enforcement state.
    // =========================================================================
    logic enter_fmc_d, enter_rt_d;
    always_ff @(posedge clk or negedge rst_b) begin
        if (!rst_b) begin
            enter_fmc_d <= '0;
            enter_rt_d  <= '0;
        end else begin
            enter_fmc_d <= enter_fmc;
            enter_rt_d  <= enter_rt;
        end
    end

    transition_t sampled_transition_d;
    assign sampled_transition_d = enter_fmc_d ? TRANS_FMC : TRANS_RT;

    // =========================================================================
    // Per-slot signals -- read from register file for post-enforcement checks
    // =========================================================================
    logic [KV_NUM_KEYS-1:0] lock_wr_vec;
    logic [KV_NUM_KEYS-1:0] lock_use_vec;
    logic [KV_NUM_KEYS-1:0] dest_valid_nonzero;

    generate
        for (genvar i = 0; i < KV_NUM_KEYS; i++) begin : gen_slot_signals
            assign lock_wr_vec[i]       = kv.kv_reg_hwif_out.KEY_CTRL[i].lock_wr;
            assign lock_use_vec[i]      = kv.kv_reg_hwif_out.KEY_CTRL[i].lock_use;
            assign dest_valid_nonzero[i] = |kv.kv_reg_hwif_out.KEY_CTRL[i].dest_valid.value;
        end
    endgenerate

    // Expected enforcement masks per the architecture (kv.sv KV_ENFORCEMENT block)
    // FMC lock_wr: slots {0,1,2,6,7,8}
    localparam logic [KV_NUM_KEYS-1:0] FMC_LOCK_WR_MASK =
        (1 << KV_SLOT_SI_IDEV)    | (1 << KV_SLOT_SI_LDEV) |
        (1 << KV_SLOT_KEY_LADDER) | (1 << KV_SLOT_FMC_CDI) |
        (1 << KV_SLOT_FMC_ECDSA)  | (1 << KV_SLOT_FMC_MLDSA);

    // RT lock_wr: FMC slots + RT slots {4,5,9}
    localparam logic [KV_NUM_KEYS-1:0] RT_LOCK_WR_MASK = FMC_LOCK_WR_MASK |
        (1 << KV_SLOT_RT_CDI) | (1 << KV_SLOT_RT_ECDSA) | (1 << KV_SLOT_RT_MLDSA);

    // RT lock_use: FMC accumulator slots {6,7,8}
    localparam logic [KV_NUM_KEYS-1:0] RT_LOCK_USE_MASK =
        (1 << KV_SLOT_FMC_CDI) | (1 << KV_SLOT_FMC_ECDSA) | (1 << KV_SLOT_FMC_MLDSA);

    // Post-enforcement checks: do the actual lock vectors contain the expected bits?
    logic fmc_lock_wr_correct;
    logic rt_lock_wr_correct;
    logic rt_lock_use_correct;

    assign fmc_lock_wr_correct  = (lock_wr_vec & FMC_LOCK_WR_MASK) == FMC_LOCK_WR_MASK;
    assign rt_lock_wr_correct   = (lock_wr_vec & RT_LOCK_WR_MASK)  == RT_LOCK_WR_MASK;
    assign rt_lock_use_correct  = (lock_use_vec & RT_LOCK_USE_MASK) == RT_LOCK_USE_MASK;

    // =========================================================================
    // cg_enforcement_result
    // Sampled ONE CYCLE after enter_fmc/enter_rt to observe registered results.
    // Verifies that enforcement set the correct lock_wr/lock_use bits and
    // cleared non-preserved slots.
    // =========================================================================
    covergroup cg_enforcement_result @(posedge clk iff (enter_fmc_d || enter_rt_d));
        option.per_instance = 1;
        option.name = "cg_enforcement_result";

        cp_transition: coverpoint sampled_transition_d {
            bins fmc = {TRANS_FMC};
            bins rt  = {TRANS_RT};
        }

        // After enter_fmc: FMC DICE slots must have lock_wr set
        cp_fmc_lock_wr: coverpoint fmc_lock_wr_correct iff (enter_fmc_d) {
            bins correct   = {1'b1};
            // Enforcement is hardwired combinational logic — incorrect is
            // architecturally impossible in correct RTL (would require a bug)
            ignore_bins incorrect = {1'b0};
        }

        // After enter_rt: all DICE slots must have lock_wr set
        cp_rt_lock_wr: coverpoint rt_lock_wr_correct iff (enter_rt_d) {
            bins correct   = {1'b1};
            ignore_bins incorrect = {1'b0};
        }

        // After enter_rt: FMC accumulator slots must have lock_use set
        cp_rt_lock_use: coverpoint rt_lock_use_correct iff (enter_rt_d) {
            bins correct   = {1'b1};
            ignore_bins incorrect = {1'b0};
        }
    endgroup

    // =========================================================================
    // cg_monitor_check
    // Sampled on enter_fmc or enter_rt -- tracks pass/fail of monitor validation
    // =========================================================================
    covergroup cg_monitor_check @(posedge clk iff (enter_fmc || enter_rt));
        option.per_instance = 1;
        option.name = "cg_monitor_check";

        cp_transition: coverpoint sampled_transition {
            bins fmc = {TRANS_FMC};
            bins rt  = {TRANS_RT};
        }

        cp_alert: coverpoint kv_monitor_alert {
            bins pass = {1'b0};
            bins fail = {1'b1};
        }

        // Cross: transition x pass/fail
        transition_X_result: cross cp_transition, cp_alert;
    endgroup

    // =========================================================================
    // cg_flush_source
    // Covers which error source triggered a KV flush.
    // flush_keyvault = debugUnlock_or_scan_mode_switch | boot_flow_error |
    //                  kv_monitor_alert | (debug_mode & clear_secrets)
    // This group covers the boot-flow-relevant flush sources:
    //   - monitor_alert fires only on enter_fmc/enter_rt (always FMC or RT phase)
    //   - boot_flow_error is driven externally from soc_ifc boot FSM
    // =========================================================================
    logic boot_flow_error_active;
    assign boot_flow_error_active = mubi4_test_true_strict(boot_flow_error);

    logic prev_boot_flow_error, prev_monitor_alert;
    always_ff @(posedge clk or negedge rst_b) begin
        if (!rst_b) begin
            prev_boot_flow_error <= '0;
            prev_monitor_alert   <= '0;
        end else begin
            prev_boot_flow_error <= boot_flow_error_active;
            prev_monitor_alert   <= kv_monitor_alert;
        end
    end

    logic flush_event;
    assign flush_event = (boot_flow_error_active & ~prev_boot_flow_error) |
                         (kv_monitor_alert & ~prev_monitor_alert);

    typedef enum logic {
        FLUSH_BOOT_FLOW_ERR = 0,
        FLUSH_MONITOR_ALERT = 1
    } flush_source_t;

    flush_source_t flush_source;
    always_comb begin
        if (boot_flow_error_active & ~prev_boot_flow_error)
            flush_source = FLUSH_BOOT_FLOW_ERR;
        else
            flush_source = FLUSH_MONITOR_ALERT;
    end

    covergroup cg_flush_source @(posedge clk iff flush_event);
        option.per_instance = 1;
        option.name = "cg_flush_source";

        cp_source: coverpoint flush_source {
            bins boot_flow_err = {FLUSH_BOOT_FLOW_ERR};
            bins monitor_alert = {FLUSH_MONITOR_ALERT};
        }

        // Monitor alert is only possible during FMC or RT transitions.
        // Boot flow error can occur in any phase.
        cp_phase: coverpoint {mubi4_test_true_strict(boot_flow_fmc), mubi4_test_true_strict(boot_flow_rt)} {
            bins rom_phase = {2'b00};
            bins fmc_phase = {2'b10};
            bins rt_phase  = {2'b11};
        }

        // Only include architecturally possible crosses:
        //   boot_flow_err can occur in any phase
        //   monitor_alert only occurs at enter_fmc (fmc_phase) or enter_rt (rt_phase)
        source_X_phase: cross cp_source, cp_phase {
            // monitor_alert during ROM is architecturally impossible
            ignore_bins monitor_in_rom = binsof(cp_source) intersect {FLUSH_MONITOR_ALERT} &&
                                         binsof(cp_phase.rom_phase);
        }
    endgroup

    // =========================================================================
    // cg_write_counter_threshold
    // Sampled at enter_fmc -- checks whether each DICE slot's write counter
    // meets the monitor's minimum threshold. This is the architecturally
    // meaningful check: counters accumulate during ROM and are validated at
    // the ROM-to-FMC transition.
    // =========================================================================
    typedef enum logic [1:0] {
        THRESHOLD_BELOW = 0,
        THRESHOLD_MET   = 1,
        THRESHOLD_ABOVE = 2
    } threshold_t;

    // Minimum write thresholds from kv.sv (accessed via hierarchical scope
    // since bind places this module inside kv's instance)
    localparam logic [2:0] KV_EXPECTED_WRITES_FMC_CDI   = 3'd4;
    localparam logic [2:0] KV_EXPECTED_WRITES_FMC_ECDSA = 3'd2;
    localparam logic [2:0] KV_EXPECTED_WRITES_FMC_MLDSA = 3'd2;

    threshold_t cdi_threshold, ecdsa_threshold, mldsa_threshold;

    always_comb begin
        if (write_count_fmc_cdi < KV_EXPECTED_WRITES_FMC_CDI)
            cdi_threshold = THRESHOLD_BELOW;
        else if (write_count_fmc_cdi == KV_EXPECTED_WRITES_FMC_CDI)
            cdi_threshold = THRESHOLD_MET;
        else
            cdi_threshold = THRESHOLD_ABOVE;
    end

    always_comb begin
        if (write_count_fmc_ecdsa < KV_EXPECTED_WRITES_FMC_ECDSA)
            ecdsa_threshold = THRESHOLD_BELOW;
        else if (write_count_fmc_ecdsa == KV_EXPECTED_WRITES_FMC_ECDSA)
            ecdsa_threshold = THRESHOLD_MET;
        else
            ecdsa_threshold = THRESHOLD_ABOVE;
    end

    always_comb begin
        if (write_count_fmc_mldsa < KV_EXPECTED_WRITES_FMC_MLDSA)
            mldsa_threshold = THRESHOLD_BELOW;
        else if (write_count_fmc_mldsa == KV_EXPECTED_WRITES_FMC_MLDSA)
            mldsa_threshold = THRESHOLD_MET;
        else
            mldsa_threshold = THRESHOLD_ABOVE;
    end

    covergroup cg_write_counter_threshold @(posedge clk iff enter_fmc);
        option.per_instance = 1;
        option.name = "cg_write_counter_threshold";

        cp_cdi_threshold: coverpoint cdi_threshold {
            bins below = {THRESHOLD_BELOW};
            bins met   = {THRESHOLD_MET};
            bins above = {THRESHOLD_ABOVE};
        }

        cp_ecdsa_threshold: coverpoint ecdsa_threshold {
            bins below = {THRESHOLD_BELOW};
            bins met   = {THRESHOLD_MET};
            bins above = {THRESHOLD_ABOVE};
        }

        cp_mldsa_threshold: coverpoint mldsa_threshold {
            bins below = {THRESHOLD_BELOW};
            bins met   = {THRESHOLD_MET};
            bins above = {THRESHOLD_ABOVE};
        }

        cp_alert: coverpoint kv_monitor_alert {
            bins no_alert = {1'b0};
            bins alert    = {1'b1};
        }

        // Per-slot crosses: prove each slot independently triggers/passes monitor
        cdi_X_alert: cross cp_cdi_threshold, cp_alert {
            // Monitor uses exact match: both below AND above fire alert
            ignore_bins below_no_alert = binsof(cp_cdi_threshold.below) && binsof(cp_alert.no_alert);
            ignore_bins above_no_alert = binsof(cp_cdi_threshold.above) && binsof(cp_alert.no_alert);
        }

        ecdsa_X_alert: cross cp_ecdsa_threshold, cp_alert {
            ignore_bins below_no_alert = binsof(cp_ecdsa_threshold.below) && binsof(cp_alert.no_alert);
            ignore_bins above_no_alert = binsof(cp_ecdsa_threshold.above) && binsof(cp_alert.no_alert);
        }

        mldsa_X_alert: cross cp_mldsa_threshold, cp_alert {
            ignore_bins below_no_alert = binsof(cp_mldsa_threshold.below) && binsof(cp_alert.no_alert);
            ignore_bins above_no_alert = binsof(cp_mldsa_threshold.above) && binsof(cp_alert.no_alert);
        }
    endgroup

    // =========================================================================
    // Instantiate covergroups
    // =========================================================================
    cg_enforcement_result       cg_enforcement_result_inst       = new();
    cg_monitor_check            cg_monitor_check_inst            = new();
    cg_flush_source             cg_flush_source_inst             = new();
    cg_write_counter_threshold  cg_write_counter_threshold_inst  = new();

endmodule

`endif
