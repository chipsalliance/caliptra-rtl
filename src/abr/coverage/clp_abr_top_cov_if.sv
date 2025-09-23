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

interface clp_abr_top_cov_if
    import abr_params_pkg::*;
    import kv_defines_pkg::*; 
    (


    input logic           clk,
    input logic           rst_b,

    input logic           ocp_lock_in_progress,

    input logic           debugUnlock_or_scan_mode_switch

);

    logic [2 : 0] mldsa_cmd;
    logic [2 : 0] mlkem_cmd;
    logic [2 : 0] mldsa_sw_cmd;
    logic zeroize;
    logic ready;
    logic mldsa_valid;
    logic mlkem_valid;
    logic pcr_process;

    logic error_flag;
    logic skdecode_error;
    logic mldsa_keygen_process;
    logic mldsa_signing_process;
    logic mldsa_verifying_process;
    logic mldsa_keygen_signing_process;
    logic mlkem_keygen_process;
    logic mlkem_encaps_process;
    logic mlkem_decaps_process;
    logic mlkem_keygen_decaps_process;

    logic verify_failure;
    logic normcheck_failure;
    logic [2 : 0] normcheck_mode;
    logic makehint_failure;
    logic invalid_hint;

    logic pcr_sign_mode;
    logic pcr_sign_input_invalid;
    logic kv_mldsa_seed_data_present;
    logic kv_mlkem_seed_data_present;
    logic kv_mlkem_msg_data_present;

    assign pcr_sign_input_invalid = abr_top.abr_ctrl_inst.pcr_sign_input_invalid;
    assign pcr_sign_mode = abr_top.abr_ctrl_inst.pcr_sign_mode;
    
    assign kv_mldsa_seed_data_present = abr_top.abr_ctrl_inst.kv_mldsa_seed_data_present;
    assign kv_mlkem_seed_data_present = abr_top.abr_ctrl_inst.kv_mlkem_seed_data_present;
    assign kv_mlkem_msg_data_present  = abr_top.abr_ctrl_inst.kv_mlkem_msg_data_present;

    always_ff @(posedge clk) begin
        if (!rst_b) begin
            pcr_process <= '0;
        end
        else if (pcr_sign_mode) begin
            pcr_process <= '1;
        end
        else if (!mldsa_signing_process & !mldsa_keygen_signing_process) begin
            pcr_process <= '0;
        end
    end

    kv_write_filter_metrics_t kv_write_metrics;
    kv_write_ctrl_reg_t kv_write_ctrl_reg;
    kv_read_ctrl_reg_t kv_read_ctrl_reg;

    assign kv_write_metrics = abr_top.abr_ctrl_inst.kv_mlkem_sharedkey_write_metrics;
    assign kv_write_ctrl_reg = abr_top.abr_ctrl_inst.kv_mlkem_sharedkey_write_ctrl_reg;
    assign kv_read_ctrl_reg = abr_top.abr_ctrl_inst.kv_mldsa_seed_read_ctrl_reg;

    assign mldsa_cmd = abr_top.abr_ctrl_inst.mldsa_cmd_reg;
    assign mlkem_cmd = abr_top.abr_ctrl_inst.mlkem_cmd_reg;
    assign zeroize = abr_top.abr_ctrl_inst.zeroize;
    assign ready = abr_top.abr_ctrl_inst.abr_ready;
    assign mldsa_valid = abr_top.abr_ctrl_inst.mldsa_valid_reg;
    assign mlkem_valid = abr_top.abr_ctrl_inst.mlkem_valid_reg;

    always_ff @(posedge clk) begin
        if (!rst_b) begin
            mldsa_sw_cmd <= '0;
        end
        else if (abr_top.abr_reg_inst.decoded_reg_strb.MLDSA_CTRL && abr_top.abr_reg_inst.decoded_req_is_wr) begin // SW write
            mldsa_sw_cmd <= (abr_top.abr_reg_inst.field_storage.MLDSA_CTRL.CTRL.value & ~abr_top.abr_reg_inst.decoded_wr_biten[2:0]) | (abr_top.abr_reg_inst.decoded_wr_data[2:0] & abr_top.abr_reg_inst.decoded_wr_biten[2:0]);
        end
    end


    assign error_flag = abr_top.abr_ctrl_inst.error_flag | abr_top.abr_ctrl_inst.error_flag_reg;
    assign skdecode_error = abr_top.abr_ctrl_inst.skdecode_error_i;

    assign mldsa_keygen_process = abr_top.abr_ctrl_inst.mldsa_keygen_process;
    assign mldsa_signing_process = abr_top.abr_ctrl_inst.mldsa_signing_process;
    assign mldsa_verifying_process = abr_top.abr_ctrl_inst.mldsa_verifying_process;
    assign mldsa_keygen_signing_process = abr_top.abr_ctrl_inst.mldsa_keygen_signing_process;
    assign mlkem_keygen_process = abr_top.abr_ctrl_inst.mldsa_keygen_process;
    assign mlkem_encaps_process = abr_top.abr_ctrl_inst.mlkem_encaps_process;
    assign mlkem_decaps_process = abr_top.abr_ctrl_inst.mlkem_decaps_process;
    assign mlkem_keygen_decaps_process = abr_top.abr_ctrl_inst.mlkem_keygen_decaps_process;

    assign verify_failure = abr_top.abr_ctrl_inst.clear_verify_valid;
    assign normcheck_failure = abr_top.abr_ctrl_inst.normcheck_done_i & abr_top.abr_ctrl_inst.normcheck_invalid_i;
    assign normcheck_mode[0] = (abr_top.abr_ctrl_inst.normcheck_mode_o == 2'b00);
    assign normcheck_mode[1] = (abr_top.abr_ctrl_inst.normcheck_mode_o == 2'b01);
    assign normcheck_mode[2] = (abr_top.abr_ctrl_inst.normcheck_mode_o == 2'b10);
    assign makehint_failure = abr_top.abr_ctrl_inst.makehint_done_i & abr_top.abr_ctrl_inst.makehint_invalid_i;
    assign invalid_hint = abr_top.abr_ctrl_inst.sigdecode_h_invalid_i;

    covergroup clp_abr_top_cov_grp @(posedge clk);
        reset_cp: coverpoint rst_b;
        debugUnlock_or_scan_mode_switch_cp: coverpoint debugUnlock_or_scan_mode_switch;

        mldsa_cmd_cp: coverpoint mldsa_cmd{
            illegal_bins illegal_values = {5, 6, 7};
        }
        mlkem_cmd_cp: coverpoint mlkem_cmd{
            illegal_bins illegal_values = {5, 6, 7};
        }
        zeroize_cp: coverpoint zeroize;
        ready_cp: coverpoint ready;
        mldsa_valid_cp: coverpoint mldsa_valid;
        mlkem_valid_cp: coverpoint mlkem_valid;
        mldsa_keygen_process_cp: coverpoint mldsa_keygen_process;
        mldsa_signing_process_cp: coverpoint mldsa_signing_process;
        mldsa_verifying_process_cp: coverpoint mldsa_verifying_process;
        mldsa_keygen_signing_process_cp: coverpoint mldsa_keygen_signing_process;

        mlkem_keygen_process_cp: coverpoint mlkem_keygen_process;
        mlkem_encaps_process_cp: coverpoint mlkem_encaps_process;
        mlkem_decaps_process_cp: coverpoint mlkem_decaps_process;
        mlkem_keygen_decaps_process_cp: coverpoint mlkem_keygen_decaps_process;

        error_flag_cp: coverpoint error_flag;
        skdecode_error_cp: coverpoint skdecode_error;
        verify_failure_cp: coverpoint verify_failure;
        normcheck_mode_sign_cp: coverpoint normcheck_mode {
            bins mode_0 = {1};
            bins mode_1 = {2};
            bins mode_2 = {4};
        }
        normcheck_mode_verify_cp: coverpoint normcheck_mode {
            bins mode_0 = {1};
        }
        normcheck_failure_cp: coverpoint normcheck_failure;
        makehint_failure_cp: coverpoint makehint_failure;
        invalid_hint_cp: coverpoint invalid_hint;
        clear_decaps_valid_cp: coverpoint abr_top.abr_ctrl_inst.clear_decaps_valid;
        encaps_input_check_failure_cp: coverpoint abr_top.abr_ctrl_inst.encaps_input_check_failure;
        decaps_input_check_failure_cp: coverpoint abr_top.abr_ctrl_inst.decaps_input_check_failure;

        stream_msg_strobe_cp: coverpoint abr_top.abr_ctrl_inst.stream_msg_strobe {
            bins one_byte = {4'b0001};
            bins two_bytes = {4'b0011};
            bins three_bytes = {4'b0111};
            bins four_bytes = {4'b1111};
        }

        mldsa_sw_cmd_cp: coverpoint mldsa_sw_cmd {
            illegal_bins illegal_values = {5, 6, 7};
        }

        mldsa_cmdXready: cross mldsa_sw_cmd_cp, ready_cp;

        zeroizeXerror: cross zeroize_cp, error_flag_cp;
        readyXzeroize: cross ready_cp, zeroize_cp;
        mldsa_validXzeroize: cross mldsa_valid_cp, zeroize_cp;
        mlkem_validXzeroize: cross mlkem_valid_cp, zeroize_cp;
        errorXmldsa_signing: cross error_flag_cp, mldsa_signing_process_cp;

        normcheckXsigning_failure: cross normcheck_mode_sign_cp, normcheck_failure_cp iff (mldsa_signing_process | mldsa_keygen_signing_process);
        normcheckXverifying_failure: cross normcheck_mode_verify_cp, normcheck_failure_cp iff (mldsa_verifying_process);

        kv_mldsa_seed_data_present_cp: coverpoint kv_mldsa_seed_data_present;
        mldsa_keygenXkv: cross mldsa_keygen_process_cp, kv_mldsa_seed_data_present_cp;

        kv_mlkem_seed_data_present_cp: coverpoint kv_mlkem_seed_data_present;
        mlkem_keygenXkv: cross mlkem_keygen_process_cp, kv_mlkem_seed_data_present_cp;
        mlkem_keygen_decapsXkv: cross mlkem_keygen_decaps_process_cp, kv_mlkem_seed_data_present_cp;

        kv_mlkem_msg_data_present_cp: coverpoint kv_mlkem_msg_data_present;
        mlkem_encapsXkv: cross mlkem_encaps_process_cp, kv_mlkem_msg_data_present_cp;

        pcr_sign_cp: coverpoint pcr_sign_mode;
        pcr_sign_input_invalid_cp: coverpoint pcr_sign_input_invalid;

        readyXpcr_sign: cross ready_cp, pcr_sign_cp;
        pcr_signXmldsa_cmd: cross pcr_sign_cp, mldsa_cmd_cp {
            ignore_bins illegal_crosses = binsof(mldsa_cmd_cp.illegal_values);
        }
        zeroizeXpcr_sign: cross zeroize_cp, pcr_sign_cp;

        errorXmldsa_keygen: cross error_flag_cp, mldsa_keygen_process_cp; // due to pcr_sign_input_invalid
        errorXmldsa_verifying: cross error_flag_cp, mldsa_verifying_process_cp; // due to pcr_sign_input_invalid
        errorXmldsa_keygen_signing: cross error_flag_cp, mldsa_keygen_signing_process_cp; // due to pcr_sign_input_invalid
        
        normcheck_fail_signXpcr_sign: cross normcheck_mode_sign_cp, normcheck_failure_cp iff (pcr_process);
        makehint_failXpcr_sign: cross makehint_failure_cp, pcr_sign_cp;

    endgroup

    // SIGN Z encoding
    localparam int NUM_ENC  = 4;
    localparam int GAMMA1   = 19;
    localparam int REG_SIZE = 23;
    localparam int MLDSA_GAMMA1_RANGE = 2**GAMMA1;
    localparam int MLDSA_Q  = 8380417;

    logic [(NUM_ENC*2)-1:0] eq_flags;
    logic [(NUM_ENC*2)-1:0] less_flags;
    logic [(NUM_ENC*2)-1:0] greater_flags;
    logic enc_unit_equal;
    logic enc_unit_less;
    logic enc_unit_greater;

    genvar sig_enc_i;
    generate
        for(sig_enc_i = 0; sig_enc_i < NUM_ENC; sig_enc_i++) begin : enc_loop
        // For the upper instance
        assign eq_flags[sig_enc_i*2]   = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].upper_encode.data_i == MLDSA_GAMMA1_RANGE);
        assign less_flags[sig_enc_i*2] = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].upper_encode.data_i <  MLDSA_GAMMA1_RANGE);
        assign greater_flags[sig_enc_i*2] = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].upper_encode.data_i > MLDSA_GAMMA1_RANGE);
        
        // For the lower instance
        assign eq_flags[sig_enc_i*2+1]   = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].lower_encode.data_i == MLDSA_GAMMA1_RANGE);
        assign less_flags[sig_enc_i*2+1] = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].lower_encode.data_i <  MLDSA_GAMMA1_RANGE);
        assign greater_flags[sig_enc_i*2+1] = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].lower_encode.data_i > MLDSA_GAMMA1_RANGE);
        end
    endgenerate

    // OR-reduce the flags: if any instance meets the condition, the corresponding signal is 1.
    assign enc_unit_equal   = (|eq_flags) & (abr_top.sigencode_z_inst.state != abr_top.sigencode_z_inst.IDLE);
    assign enc_unit_less    = (|less_flags) & (abr_top.sigencode_z_inst.state != abr_top.sigencode_z_inst.IDLE);
    assign enc_unit_greater = (|greater_flags) & (abr_top.sigencode_z_inst.state != abr_top.sigencode_z_inst.IDLE);
    // Sign_z to cover the aggregated conditions
    covergroup clp_mldsa_sign_z_enc_agg_cg @(posedge clk);
        coverpoint enc_unit_equal {
            bins hit = {1'b1};
        }
        coverpoint enc_unit_less {
            bins hit = {1'b1};
        }
        coverpoint enc_unit_greater {
            bins hit = {1'b1};
        }
    endgroup

    // The FSM cases are: 'h0, 'h1, 'h2, MLDSA_Q-1, MLDSA_Q-2, and default.
    logic [(NUM_ENC*2)-1:0] skenc_state0_flags;
    logic [(NUM_ENC*2)-1:0] skenc_state1_flags;
    logic [(NUM_ENC*2)-1:0] skenc_state2_flags;
    logic [(NUM_ENC*2)-1:0] skenc_state_mq1_flags;
    logic [(NUM_ENC*2)-1:0] skenc_state_mq2_flags;
    logic skenc_state0_agg, skenc_state1_agg, skenc_state2_agg, skenc_state_mq1_agg, skenc_state_mq2_agg;

    genvar sk_enc_i;
    generate
    for (sk_enc_i = 0; sk_enc_i < NUM_ENC; sk_enc_i++) begin : sk_enc_loop
        // For mem_a_rd_data element
        assign skenc_state0_flags[sk_enc_i*2]    = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == 'h0);
        assign skenc_state1_flags[sk_enc_i*2]    = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == 'h1);
        assign skenc_state2_flags[sk_enc_i*2]    = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == 'h2);
        assign skenc_state_mq1_flags[sk_enc_i*2] = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == MLDSA_Q - 1);
        assign skenc_state_mq2_flags[sk_enc_i*2] = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == MLDSA_Q - 2);
        // For mem_b_rd_data element
        assign skenc_state0_flags[sk_enc_i*2+1]    = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == 'h0);
        assign skenc_state1_flags[sk_enc_i*2+1]    = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == 'h1);
        assign skenc_state2_flags[sk_enc_i*2+1]    = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == 'h2);
        assign skenc_state_mq1_flags[sk_enc_i*2+1] = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == MLDSA_Q - 1);
        assign skenc_state_mq2_flags[sk_enc_i*2+1] = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == MLDSA_Q - 2);
    end
    endgenerate

    // OR-reduce each set of flags and ensure the FSM is not in IDLE.
    // (Assuming abr_top.skencode_inst.state and its IDLE constant are accessible.)
    assign skenc_state0_agg    = (|skenc_state0_flags)    & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.IDLE);
    assign skenc_state1_agg    = (|skenc_state1_flags)    & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.IDLE);
    assign skenc_state2_agg    = (|skenc_state2_flags)    & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.IDLE);
    assign skenc_state_mq1_agg = (|skenc_state_mq1_flags) & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.IDLE);
    assign skenc_state_mq2_agg = (|skenc_state_mq2_flags) & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.IDLE);

    // Now create a covergroup that samples these aggregated flags.
    covergroup clp_mldsa_skencode_agg_cg @(posedge clk);
        coverpoint skenc_state0_agg    { bins hit = {1'b1}; }
        coverpoint skenc_state1_agg    { bins hit = {1'b1}; }
        coverpoint skenc_state2_agg    { bins hit = {1'b1}; }
        coverpoint skenc_state_mq1_agg { bins hit = {1'b1}; }
        coverpoint skenc_state_mq2_agg { bins hit = {1'b1}; }
    endgroup
    
    covergroup clp_abr_ocp_lock_cov_grp @(posedge clk);

        ocp_lock_in_progress_cp: coverpoint ocp_lock_in_progress;

        kv_read_entry_mldsa_cp: coverpoint {kv_mldsa_seed_data_present, kv_read_ctrl_reg.read_entry } 
        iff (mldsa_cmd inside {MLDSA_KEYGEN, MLDSA_KEYGEN_SIGN}) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        kv_read_entry_0_cp: coverpoint {kv_write_metrics.kv_data0_present, kv_write_metrics.kv_data0_entry} 
        iff (mlkem_cmd inside {MLKEM_KEYGEN_DEC}) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        kv_read_entry_1_cp: coverpoint {kv_write_metrics.kv_data1_present, kv_write_metrics.kv_data1_entry} 
        iff (mlkem_cmd inside {MLKEM_ENCAPS}) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        kv_write_entry_decaps_cp: coverpoint {kv_write_ctrl_reg.write_en, kv_write_metrics.kv_write_entry} 
        iff (mlkem_cmd inside {MLKEM_KEYGEN_DEC}) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        kv_write_entry_encaps_cp: coverpoint {kv_write_ctrl_reg.write_en, kv_write_metrics.kv_write_entry} 
        iff (mlkem_cmd inside {MLKEM_ENCAPS}) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        ocp_lock_X_kv_read_entry0: cross ocp_lock_in_progress_cp, kv_write_entry_decaps_cp, kv_read_entry_0_cp;
        ocp_lock_X_kv_read_entry1: cross ocp_lock_in_progress_cp, kv_write_entry_encaps_cp, kv_read_entry_1_cp;
        ocp_lock_X_kv_read_entry_mldsa: cross ocp_lock_in_progress_cp, kv_read_entry_mldsa_cp;
    endgroup  

    // Instantiate the covergroup
    clp_mldsa_skencode_agg_cg clp_mldsa_skencode_agg_cov = new();
    clp_mldsa_sign_z_enc_agg_cg clp_mldsa_sign_z_enc_agg_cov_grp1 = new();

    clp_abr_ocp_lock_cov_grp clp_abr_ocp_lock_cov_grp1 = new();

    clp_abr_top_cov_grp clp_abr_top_cov_grp1 = new();

endinterface

`endif
