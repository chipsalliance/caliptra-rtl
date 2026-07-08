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
    logic csr_mode;
    logic last;
    logic ready;
    logic valid;
    logic restore;
    logic is_last_op;

    logic core_tag_we;

    logic kv_key_data_present;
    logic kv_block_data_present;
    logic dest_keyvault;
    logic tag_was_masked;
    logic awaiting_zeroize;

    logic key_mode_error_edge;
    logic key_zero_error_edge;
    logic invalid_cmd_error_edge;
    logic intermediate_tag_hidden_edge;

    logic [4:0] hmac_cmd;
    logic [1:0] hmac_mode_bits;

    kv_write_filter_metrics_t kv_write_metrics;
    kv_write_ctrl_reg_t kv_write_ctrl_reg;

    assign init       = hmac_ctrl.hmac_inst.init_reg;
    assign next       = hmac_ctrl.hmac_inst.next_reg;
    assign zeroize    = hmac_ctrl.hmac_inst.zeroize_reg;
    assign mode       = hmac_ctrl.hmac_inst.mode_reg;
    assign csr_mode   = hmac_ctrl.hmac_inst.csr_mode_reg;
    assign last       = hmac_ctrl.hmac_inst.last_reg;
    assign ready      = hmac_ctrl.hmac_inst.ready_reg;
    assign valid      = hmac_ctrl.hmac_inst.tag_valid_reg;
    assign restore    = hmac_ctrl.hmac_inst.restore_reg;
    assign is_last_op = hmac_ctrl.hmac_inst.is_last_op_reg;

    assign core_tag_we = hmac_ctrl.hmac_inst.core_tag_we;

    assign kv_key_data_present   = hmac_ctrl.hmac_inst.kv_key_data_present;
    assign kv_block_data_present = hmac_ctrl.hmac_inst.kv_block_data_present;
    assign dest_keyvault         = hmac_ctrl.hmac_inst.dest_keyvault;
    assign tag_was_masked        = hmac_ctrl.hmac_inst.tag_was_masked_reg;
    assign awaiting_zeroize      = hmac_ctrl.hmac_inst.awaiting_zeroize;

    assign key_mode_error_edge          = hmac_ctrl.hmac_inst.key_mode_error_edge;
    assign key_zero_error_edge          = hmac_ctrl.hmac_inst.key_zero_error_edge;
    assign invalid_cmd_error_edge       = hmac_ctrl.hmac_inst.invalid_cmd_error_edge;
    assign intermediate_tag_hidden_edge = hmac_ctrl.hmac_inst.intermediate_tag_hidden_edge;

    // hmac_cmd bit layout: {restore, last, next, init, zeroize}.
    // Sampled off the RAW CTRL field values so illegal combos that get
    // masked by invalid_cmd_error still show up in the covergroup.
    assign hmac_cmd = {hmac_ctrl.hmac_inst.hwif_out.HMAC512_CTRL.RESTORE.value,
                       hmac_ctrl.hmac_inst.hwif_out.HMAC512_CTRL.LAST.value,
                       hmac_ctrl.hmac_inst.hwif_out.HMAC512_CTRL.NEXT.value,
                       hmac_ctrl.hmac_inst.hwif_out.HMAC512_CTRL.INIT.value,
                       hmac_ctrl.hmac_inst.hwif_out.HMAC512_CTRL.ZEROIZE.value};

    // {csr_mode, mode} — 4 combinations (HMAC-384 vs HMAC-512, CSR vs SW).
    assign hmac_mode_bits = {csr_mode, mode};

    assign kv_write_metrics  = hmac_ctrl.hmac_inst.kv_write_metrics;
    assign kv_write_ctrl_reg = hmac_ctrl.hmac_inst.kv_write_ctrl_reg;

    covergroup hmac_ctrl_cov_grp @(posedge clk);
        reset_cp: coverpoint reset_n;
        //cptra_pwrgood_cp: coverpoint cptra_pwrgood;

        init_cp: coverpoint init;
        next_cp: coverpoint next;
        zeroize_cp: coverpoint zeroize;
        mode_cp: coverpoint mode;
        csr_mode_cp: coverpoint csr_mode;
        last_cp: coverpoint last;
        restore_cp: coverpoint restore;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;
        is_last_op_cp: coverpoint is_last_op;

        core_tag_we_cp: coverpoint core_tag_we;

        // Every combination of {restore, last, next, init, zeroize}.
        // Bin names describe which SW-visible fields are asserted.
        hmac_cmd_cp: coverpoint hmac_cmd {
            bins idle                     = {5'h00};
            bins zeroize_only             = {5'h01};
            bins init                     = {5'h02};
            bins init_zeroize             = {5'h03};
            bins next                     = {5'h04};
            bins next_zeroize             = {5'h05};
            bins init_next                = {5'h06};
            bins init_next_zeroize        = {5'h07};
            bins last_alone               = {5'h08};
            bins last_zeroize             = {5'h09};
            bins init_last                = {5'h0A};
            bins init_last_zeroize        = {5'h0B};
            bins next_last                = {5'h0C};
            bins next_last_zeroize        = {5'h0D};
            bins init_next_last           = {5'h0E};
            bins init_next_last_zeroize   = {5'h0F};
            bins restore_alone            = {5'h10};
            bins restore_zeroize          = {5'h11};
            bins init_restore             = {5'h12};
            bins init_restore_zeroize     = {5'h13};
            bins next_restore             = {5'h14};
            bins next_restore_zeroize     = {5'h15};
            bins init_next_restore        = {5'h16};
            bins init_next_restore_zero   = {5'h17};
            bins last_restore             = {5'h18};
            bins last_restore_zeroize     = {5'h19};
            bins init_last_restore        = {5'h1A};
            bins init_last_restore_zero   = {5'h1B};
            bins next_last_restore        = {5'h1C};
            bins next_last_restore_zero   = {5'h1D};
            bins all_four                 = {5'h1E};
            bins all_four_zeroize         = {5'h1F};
        }

        // {csr_mode, mode} → 4 bins: HMAC-384/-512 × SW-key/CSR-key.
        hmac_mode_bits_cp: coverpoint hmac_mode_bits {
            bins hmac384_sw  = {2'b00};
            bins hmac512_sw  = {2'b01};
            bins hmac384_csr = {2'b10};
            bins hmac512_csr = {2'b11};
        }

        // Every CTRL encoding crossed with every mode/key combination
        // = 32 * 4 = 128 physical stimuli that SW can present.
        hmac_cmd_x_mode: cross hmac_cmd_cp, hmac_mode_bits_cp;

        //init_ready_cp: cross ready, init;
        //next_ready_cp: cross ready, next;
        mode_ready_cp: cross ready, mode;
        zeroize_ready_cp: cross ready, zeroize;
        zeroize_init_cp: cross zeroize, init;
        zeroize_next_cp: cross zeroize, next;
        init_mode_cp: cross init, mode;
        next_mode_cp: cross next, mode;
        last_mode_cp: cross last, mode;
        restore_mode_cp: cross restore, mode;

    endgroup

    // ---------------------------------------------------------------
    // KV / CSR / dest-KV coverage
    //   Each cause of intermediate_tag_hidden gets its own coverpoint
    //   plus a cross so we know every combination SW can present.
    // ---------------------------------------------------------------
    covergroup hmac_kv_csr_cov_grp @(posedge clk);
        kv_key_present_cp   : coverpoint kv_key_data_present;
        kv_block_present_cp : coverpoint kv_block_data_present;
        csr_mode_cause_cp   : coverpoint csr_mode;
        dest_keyvault_cp    : coverpoint dest_keyvault;

        // Sticky latch — was any intermediate tag ever masked?
        tag_was_masked_cp   : coverpoint tag_was_masked;

        // All 16 combinations of the four tag-hiding causes.
        // Only sampled during an active op so we filter out reset.
        tag_hidden_causes_cp: coverpoint {kv_key_data_present,
                                          kv_block_data_present,
                                          csr_mode,
                                          dest_keyvault}
            iff (init | next | restore) {
                bins none              = {4'b0000};
                bins kv_key            = {4'b1000};
                bins kv_block          = {4'b0100};
                bins csr               = {4'b0010};
                bins dest_kv           = {4'b0001};
                bins kv_key_and_block  = {4'b1100};
                bins csr_and_dest_kv   = {4'b0011};
                bins others            = default;
            }
    endgroup

    // ---------------------------------------------------------------
    // Error-status coverage
    //   Sample each error edge so it shows up in the report even if
    //   the assertion in the smoke test is what actually catches the
    //   miss.
    // ---------------------------------------------------------------
    covergroup hmac_error_cov_grp @(posedge clk);
        key_mode_error_cp          : coverpoint key_mode_error_edge
                                       iff (key_mode_error_edge);
        key_zero_error_cp          : coverpoint key_zero_error_edge
                                       iff (key_zero_error_edge);
        invalid_cmd_error_cp       : coverpoint invalid_cmd_error_edge
                                       iff (invalid_cmd_error_edge);
        intermediate_tag_hidden_cp : coverpoint intermediate_tag_hidden_edge
                                       iff (intermediate_tag_hidden_edge);

        // Both error paths crossed with mode so we know HMAC-384 and
        // HMAC-512 each exercised each error class.
        invalid_cmd_x_mode : cross invalid_cmd_error_cp, mode;
        tag_hidden_x_mode  : cross intermediate_tag_hidden_cp, mode;

        // awaiting_zeroize gate — did we ever park the engine?
        awaiting_zeroize_cp : coverpoint awaiting_zeroize;
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

    hmac_ctrl_cov_grp     hmac_ctrl_cov_grp1     = new();
    hmac_kv_csr_cov_grp   hmac_kv_csr_cov_grp1   = new();
    hmac_error_cov_grp    hmac_error_cov_grp1    = new();
    hmac_ocp_lock_cov_grp hmac_ocp_lock_cov_grp1 = new();

endinterface

`endif