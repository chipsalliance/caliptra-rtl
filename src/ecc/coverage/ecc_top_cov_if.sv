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

interface ecc_top_cov_if
    import kv_defines_pkg::*;  
    (
    input logic           clk,
    input logic           reset_n,
    input logic           cptra_pwrgood,
    input logic           ocp_lock_in_progress

);

    logic [2 : 0] ecc_cmd;
    logic [2 : 0] ecc_sw_cmd;
    logic zeroize;
    logic pcr_sign_mode;
    logic ready;
    logic valid;

    logic dest_keyvault;

    logic error_flag;
    logic privkey_input_outofrange;
    logic r_output_outofrange;
    logic s_output_outofrange;
    logic r_input_outofrange;
    logic s_input_outofrange;
    logic pubkeyx_input_outofrange;
    logic pubkeyy_input_outofrange;
    logic pubkey_input_invalid;
    logic pcr_sign_input_invalid;
    logic keygen_process;
    logic signing_process;
    logic verifying_process;
    logic sharedkey_process;
    logic privkey_output_outofrange, pubkeyx_output_outofrange, pubkeyy_output_outofrange;
    logic sharedkey_outofrange;


    logic mod_p_q;
    logic add_en;
    logic add_sub_i;
    logic [383 : 0] add_res0;
    logic add_cout0;
    logic add_cout1;
    logic add_res_less_than_prime;
    logic add_res_greater_than_384_bit;

    logic mult_ready;
    logic mult_last_reduction;
    logic mult_final_subtraction;

    kv_write_filter_metrics_t kv_write_metrics;
    kv_write_ctrl_reg_t kv_write_ctrl_reg;

    assign mod_p_q = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.mod_p_q;
    assign add_en = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.add_en_i;
    assign add_sub_i = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.sub_i;
    assign add_res0 = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_ADDER_SUBTRACTOR.r0_reg;
    assign add_cout0 = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_ADDER_SUBTRACTOR.carry0_reg;
    assign add_cout1 = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_ADDER_SUBTRACTOR.carry1;
    assign add_res_less_than_prime = ((add_cout0 == 1'b0) & (add_res0 < ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.prime_i));
    assign add_res_greater_than_384_bit = (add_cout0 == 1'b1);
    
    assign mult_ready = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_MULTIPLIER.ready_o;
    assign mult_last_reduction = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_MULTIPLIER.last_reduction;
    assign mult_final_subtraction = mult_ready & mult_last_reduction;
    
    assign ecc_cmd = ecc_top.ecc_dsa_ctrl_i.cmd_reg;
    assign pcr_sign_mode = ecc_top.ecc_dsa_ctrl_i.pcr_sign_mode;
    assign zeroize = ecc_top.ecc_dsa_ctrl_i.zeroize_reg;
    assign ready = ecc_top.ecc_dsa_ctrl_i.ecc_ready_reg;
    assign valid = ecc_top.ecc_dsa_ctrl_i.ecc_valid_reg;

    assign kv_write_metrics = ecc_top.ecc_dsa_ctrl_i.kv_write_metrics;
    assign kv_write_ctrl_reg = ecc_top.ecc_dsa_ctrl_i.kv_write_ctrl_reg;

    always_ff @(posedge clk) begin
        if (!reset_n) begin
            ecc_sw_cmd <= '0;
        end
        else if (ecc_top.ecc_reg1.decoded_reg_strb.ECC_CTRL && ecc_top.ecc_reg1.decoded_req_is_wr) begin // SW write
            ecc_sw_cmd[1:0] <= (ecc_top.ecc_reg1.field_storage.ECC_CTRL.CTRL.value & ~ecc_top.ecc_reg1.decoded_wr_biten[1:0]) | (ecc_top.ecc_reg1.decoded_wr_data[1:0] & ecc_top.ecc_reg1.decoded_wr_biten[1:0]);
            ecc_sw_cmd[2] <= (ecc_top.ecc_reg1.field_storage.ECC_CTRL.DH_SHAREDKEY.value & ~ecc_top.ecc_reg1.decoded_wr_biten[4]) | (ecc_top.ecc_reg1.decoded_wr_data[4] & ecc_top.ecc_reg1.decoded_wr_biten[4]);
        end
    end

    assign dest_keyvault = ecc_top.ecc_dsa_ctrl_i.dest_keyvault;

    assign error_flag = ecc_top.ecc_dsa_ctrl_i.error_flag | ecc_top.ecc_dsa_ctrl_i.error_flag_reg;
    assign privkey_input_outofrange = ecc_top.ecc_dsa_ctrl_i.privkey_input_outofrange;
    assign r_output_outofrange = ecc_top.ecc_dsa_ctrl_i.r_output_outofrange;
    assign s_output_outofrange = ecc_top.ecc_dsa_ctrl_i.s_output_outofrange;
    assign r_input_outofrange = ecc_top.ecc_dsa_ctrl_i.r_input_outofrange;
    assign s_input_outofrange = ecc_top.ecc_dsa_ctrl_i.s_input_outofrange;
    assign pubkeyx_input_outofrange = ecc_top.ecc_dsa_ctrl_i.pubkeyx_input_outofrange;
    assign pubkeyy_input_outofrange = ecc_top.ecc_dsa_ctrl_i.pubkeyy_input_outofrange;
    assign pubkey_input_invalid = ecc_top.ecc_dsa_ctrl_i.pubkey_input_invalid;
    assign pcr_sign_input_invalid = ecc_top.ecc_dsa_ctrl_i.pcr_sign_input_invalid;
    assign keygen_process = ecc_top.ecc_dsa_ctrl_i.keygen_process;
    assign signing_process = ecc_top.ecc_dsa_ctrl_i.signing_process;
    assign verifying_process = ecc_top.ecc_dsa_ctrl_i.verifying_process;
    assign sharedkey_process = ecc_top.ecc_dsa_ctrl_i.sharedkey_process;
    assign privkey_output_outofrange = ecc_top.ecc_dsa_ctrl_i.privkey_output_outofrange;
    assign pubkeyx_output_outofrange = ecc_top.ecc_dsa_ctrl_i.pubkeyx_output_outofrange;
    assign pubkeyy_output_outofrange = ecc_top.ecc_dsa_ctrl_i.pubkeyy_output_outofrange;
    assign sharedkey_outofrange = ecc_top.ecc_dsa_ctrl_i.sharedkey_outofrange;

    covergroup ecc_top_cov_grp @(posedge clk);
        reset_cp: coverpoint reset_n;
        //cptra_pwrgood_cp: coverpoint cptra_pwrgood;

        ecc_cmd_cp: coverpoint ecc_cmd {
            illegal_bins illegal_values = {5, 6, 7};
        }
        pcr_sign_cp: coverpoint pcr_sign_mode;
        zeroize_cp: coverpoint zeroize;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;

        dest_keyvault_cp: coverpoint dest_keyvault;

        error_flag_cp: coverpoint error_flag;
        privkey_input_outofrange_cp: coverpoint privkey_input_outofrange;
        r_output_outofrange_cp: coverpoint r_output_outofrange;
        s_output_outofrange_cp: coverpoint s_output_outofrange;
        r_input_outofrange_cp: coverpoint r_input_outofrange;
        s_input_outofrange_cp: coverpoint s_input_outofrange;
        pubkeyx_input_outofrange_cp: coverpoint pubkeyx_input_outofrange;
        pubkeyx_input_outofrange_cross: cross pubkeyx_input_outofrange_cp, verifying_process, sharedkey_process {
            // Exclude illegal state
            ignore_bins both_active = binsof(verifying_process) intersect {1} && binsof(sharedkey_process) intersect {1};
            ignore_bins neither_active = binsof(verifying_process) intersect {0} && binsof(sharedkey_process) intersect {0};
        }
        pubkeyy_input_outofrange_cp: coverpoint pubkeyy_input_outofrange;
        pubkeyy_input_outofrange_cross: cross pubkeyy_input_outofrange_cp, verifying_process, sharedkey_process {
            // Exclude illegal state
            ignore_bins both_active = binsof(verifying_process) intersect {1} && binsof(sharedkey_process) intersect {1};
            ignore_bins neither_active = binsof(verifying_process) intersect {0} && binsof(sharedkey_process) intersect {0};
        }
        pubkey_input_invalid_cp: coverpoint pubkey_input_invalid;
        pubkey_input_invalid_cross: cross pubkey_input_invalid_cp, verifying_process, sharedkey_process {
            // Exclude illegal state
            ignore_bins both_active = binsof(verifying_process) intersect {1} && binsof(sharedkey_process) intersect {1};
            ignore_bins neither_active = binsof(verifying_process) intersect {0} && binsof(sharedkey_process) intersect {0};
        }
        pcr_sign_input_invalid_cp: coverpoint pcr_sign_input_invalid;

        privkey_output_outofrange_cp: coverpoint privkey_output_outofrange;
        pubkeyx_output_outofrange_cp: coverpoint pubkeyx_output_outofrange;
        pubkeyy_output_outofrange_cp: coverpoint pubkeyy_output_outofrange;
        sharedkey_outofrange_cp: coverpoint sharedkey_outofrange;

        cmd_ready_cp: cross ecc_sw_cmd, ready{
            ignore_bins illegal_sw_cmd = binsof(ecc_sw_cmd) intersect {5, 6, 7};
        }
        keygen_kv_cp: cross keygen_process, dest_keyvault;
        pcr_ready_cp: cross ready, pcr_sign_mode;
        pcr_cmd_cp: cross pcr_sign_mode, ecc_cmd_cp{
            ignore_bins illegal_crosses = binsof(ecc_cmd_cp.illegal_values);
        }
        zeroize_pcr_cp: cross zeroize, pcr_sign_mode;
        zeroize_cmd_cp: cross zeroize, ecc_cmd_cp{
            ignore_bins illegal_crosses = binsof(ecc_cmd_cp.illegal_values);
        }
        zeroize_error_cp: cross zeroize, error_flag;
        zeroize_ready_cp: cross ready, zeroize;
        pcr_sign_input_invalid_cmd_cp: cross error_flag, ecc_cmd_cp{
            ignore_bins illegal_crosses = binsof(ecc_cmd_cp.illegal_values) || binsof(ecc_cmd_cp) intersect {2};
        }
        error_keygen_cp: cross error_flag, keygen_process;
        error_signing_cp: cross error_flag, signing_process;
        error_verifying_cp: cross error_flag, verifying_process;
        error_sharedkey_cp: cross error_flag, sharedkey_process;

        // modular operation
        add_carry_cp: cross mod_p_q, add_sub_i, add_cout0, add_cout1;
        add_result_less_than_prime_cp: cross mod_p_q, add_sub_i, add_res_less_than_prime;
        add_result_greater_than_384_bit_cp: cross mod_p_q, add_sub_i, add_res_greater_than_384_bit;
        

    endgroup

    covergroup ecc_ocp_lock_cov_grp @(posedge clk);

        ocp_lock_in_progress_cp: coverpoint ocp_lock_in_progress;

        kv_read_entry_0_cp: coverpoint {kv_write_metrics.kv_data0_present, kv_write_metrics.kv_data0_entry} 
        iff (ecc_cmd inside {3'b001}) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        kv_read_entry_1_cp: coverpoint {kv_write_metrics.kv_data1_present, kv_write_metrics.kv_data1_entry} 
        iff (ecc_cmd inside {3'b100}) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        kv_write_entry_kg_cp: coverpoint {kv_write_ctrl_reg.write_en, kv_write_metrics.kv_write_entry} 
        iff (ecc_cmd inside {3'b001}) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        kv_write_entry_ecdh_cp: coverpoint {kv_write_ctrl_reg.write_en, kv_write_metrics.kv_write_entry} 
        iff (ecc_cmd inside {3'b100}) {
            bins fw = {[0:23]}; //{1'b0, [0:$]};
            bins lower_slots = {[32:47]}; //{1'b1, [0:15]};
            bins upper_slots = {[48:54]}; //{1'b1, [16:22]};
            bins slot_23 = {55}; //{1'b1, 23};
        }

        ocp_lock_X_kv_read_entry0: cross ocp_lock_in_progress_cp, kv_write_entry_kg_cp, kv_read_entry_0_cp;
        ocp_lock_X_kv_read_entry1: cross ocp_lock_in_progress_cp, kv_write_entry_ecdh_cp, kv_read_entry_1_cp;
    endgroup  

    ecc_top_cov_grp ecc_top_cov_grp1 = new();
    ecc_ocp_lock_cov_grp ecc_ocp_lock_cov_grp1 = new();

endinterface

`endif
