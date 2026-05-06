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
// Covers: enforcement actions, monitor checks, error escalation, write counters

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

    // Multi-write error
    input logic kv_multi_write_err,

    // Crypto write strobes (for counter sampling)
    input logic crypto_wr_fmc_cdi,
    input logic crypto_wr_fmc_ecdsa,
    input logic crypto_wr_fmc_mldsa
);

    // =========================================================================
    // Intermediate signals — sample slot state at transition edges
    // =========================================================================
    logic [KV_NUM_KEYS-1:0] lock_wr_at_sample;
    logic [KV_NUM_KEYS-1:0] lock_use_at_sample;
    logic [KV_NUM_KEYS-1:0] dest_valid_nonzero;

    generate
        for (genvar i = 0; i < KV_NUM_KEYS; i++) begin : gen_slot_signals
            assign lock_wr_at_sample[i]  = kv.kv_reg_hwif_out.KEY_CTRL[i].lock_wr;
            assign lock_use_at_sample[i] = kv.kv_reg_hwif_out.KEY_CTRL[i].lock_use;
            assign dest_valid_nonzero[i] = |kv.kv_reg_hwif_out.KEY_CTRL[i].dest_valid.value;
        end
    endgenerate

    // =========================================================================
    // cg_enforcement_action
    // Sampled on enter_fmc or enter_rt — tracks which slots get which actions
    // =========================================================================
    typedef enum logic [1:0] {TRANS_FMC = 0, TRANS_RT = 1} transition_t;

    transition_t sampled_transition;
    assign sampled_transition = enter_fmc ? TRANS_FMC : TRANS_RT;

    // Count of locked/cleared slots at transition time
    logic [4:0] lock_wr_count, lock_use_count, cleared_count;
    always_comb begin
        lock_wr_count  = $countones(lock_wr_at_sample);
        lock_use_count = $countones(lock_use_at_sample);
        cleared_count  = $countones(~dest_valid_nonzero);
    end

    covergroup cg_enforcement_action @(posedge clk iff (enter_fmc || enter_rt));
        option.per_instance = 1;
        option.name = "cg_enforcement_action";

        cp_transition: coverpoint sampled_transition {
            bins fmc = {TRANS_FMC};
            bins rt  = {TRANS_RT};
        }

        cp_lock_wr_count: coverpoint lock_wr_count {
            bins none   = {0};
            bins low    = {[1:5]};
            bins mid    = {[6:10]};
            bins high   = {[11:KV_NUM_KEYS]};
        }

        cp_lock_use_count: coverpoint lock_use_count {
            bins none = {0};
            bins some = {[1:5]};
            bins many = {[6:KV_NUM_KEYS]};
        }

        cp_cleared_count: coverpoint cleared_count {
            bins none  = {0};
            bins some  = {[1:8]};
            bins most  = {[9:KV_NUM_KEYS]};
        }

        cp_alert: coverpoint kv_monitor_alert;

        // Key crosses
        transition_X_lock_wr: cross cp_transition, cp_lock_wr_count;
        transition_X_lock_use: cross cp_transition, cp_lock_use_count;
        transition_X_cleared: cross cp_transition, cp_cleared_count;
        transition_X_alert: cross cp_transition, cp_alert;
    endgroup

    // =========================================================================
    // cg_monitor_check
    // Sampled on enter_fmc or enter_rt — tracks pass/fail of monitor validation
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

        // Cross: transition × pass/fail
        transition_X_result: cross cp_transition, cp_alert;
    endgroup

    // =========================================================================
    // cg_error_escalation
    // Sampled on rising edge of any error source
    // =========================================================================
    logic boot_flow_error_active;
    assign boot_flow_error_active = mubi4_test_true_strict(boot_flow_error);

    logic prev_boot_flow_error, prev_monitor_alert, prev_multi_write_err;
    always_ff @(posedge clk or negedge rst_b) begin
        if (!rst_b) begin
            prev_boot_flow_error <= '0;
            prev_monitor_alert   <= '0;
            prev_multi_write_err <= '0;
        end else begin
            prev_boot_flow_error <= boot_flow_error_active;
            prev_monitor_alert   <= kv_monitor_alert;
            prev_multi_write_err <= kv_multi_write_err;
        end
    end

    logic error_event;
    assign error_event = (boot_flow_error_active & ~prev_boot_flow_error) |
                         (kv_monitor_alert & ~prev_monitor_alert) |
                         (kv_multi_write_err & ~prev_multi_write_err);

    typedef enum logic [1:0] {
        ERR_BOOT_FLOW  = 0,
        ERR_MONITOR    = 1,
        ERR_MULTI_WRITE = 2
    } error_source_t;

    error_source_t error_source;
    always_comb begin
        if (boot_flow_error_active & ~prev_boot_flow_error)
            error_source = ERR_BOOT_FLOW;
        else if (kv_monitor_alert & ~prev_monitor_alert)
            error_source = ERR_MONITOR;
        else
            error_source = ERR_MULTI_WRITE;
    end

    covergroup cg_error_escalation @(posedge clk iff error_event);
        option.per_instance = 1;
        option.name = "cg_error_escalation";

        cp_source: coverpoint error_source {
            bins boot_flow_err = {ERR_BOOT_FLOW};
            bins monitor_alert = {ERR_MONITOR};
            bins multi_write   = {ERR_MULTI_WRITE};
        }

        cp_boot_phase: coverpoint {mubi4_test_true_strict(boot_flow_fmc), mubi4_test_true_strict(boot_flow_rt)} {
            bins rom_phase = {2'b00};
            bins fmc_phase = {2'b10};
            bins rt_phase  = {2'b11};
        }

        source_X_phase: cross cp_source, cp_boot_phase;
    endgroup

    // =========================================================================
    // cg_write_counter
    // Sampled on crypto write to monitored slots (6, 7, 8)
    // =========================================================================
    logic crypto_wr_any_monitored;
    assign crypto_wr_any_monitored = crypto_wr_fmc_cdi | crypto_wr_fmc_ecdsa | crypto_wr_fmc_mldsa;

    typedef enum logic [1:0] {SLOT_FMC_CDI = 0, SLOT_FMC_ECDSA = 1, SLOT_FMC_MLDSA = 2} monitored_slot_t;

    monitored_slot_t wr_slot;
    always_comb begin
        if (crypto_wr_fmc_cdi)        wr_slot = SLOT_FMC_CDI;
        else if (crypto_wr_fmc_ecdsa) wr_slot = SLOT_FMC_ECDSA;
        else                          wr_slot = SLOT_FMC_MLDSA;
    end

    logic [2:0] wr_count_at_sample;
    always_comb begin
        case (wr_slot)
            SLOT_FMC_CDI:   wr_count_at_sample = write_count_fmc_cdi;
            SLOT_FMC_ECDSA: wr_count_at_sample = write_count_fmc_ecdsa;
            default:        wr_count_at_sample = write_count_fmc_mldsa;
        endcase
    end

    covergroup cg_write_counter @(posedge clk iff crypto_wr_any_monitored);
        option.per_instance = 1;
        option.name = "cg_write_counter";

        cp_slot: coverpoint wr_slot {
            bins fmc_cdi   = {SLOT_FMC_CDI};
            bins fmc_ecdsa = {SLOT_FMC_ECDSA};
            bins fmc_mldsa = {SLOT_FMC_MLDSA};
        }

        cp_count: coverpoint wr_count_at_sample {
            bins count[] = {[0:7]};
        }

        cp_boot_phase: coverpoint {mubi4_test_true_strict(boot_flow_fmc), mubi4_test_true_strict(boot_flow_rt)} {
            bins rom_phase = {2'b00};
            bins fmc_phase = {2'b10};
            bins rt_phase  = {2'b11};
        }

        slot_X_count: cross cp_slot, cp_count;
        slot_X_phase: cross cp_slot, cp_boot_phase;
    endgroup

    // =========================================================================
    // Instantiate covergroups
    // =========================================================================
    cg_enforcement_action cg_enforcement_action_inst = new();
    cg_monitor_check      cg_monitor_check_inst      = new();
    cg_error_escalation   cg_error_escalation_inst   = new();
    cg_write_counter      cg_write_counter_inst      = new();

endmodule

`endif
