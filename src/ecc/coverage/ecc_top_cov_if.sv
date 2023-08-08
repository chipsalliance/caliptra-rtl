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
    (
    input logic           clk,
    input logic           reset_n,
    input logic           cptra_pwrgood

);

    logic [1 : 0] ecc_cmd;
    logic [1 : 0] ecc_sw_cmd;
    logic zeroize;
    logic pcr_sign_mode;
    logic ready;
    logic valid;

    logic dest_keyvault;

    logic error_flag;
    logic privkey_input_outofrange;
    logic r_output_outofrange;
    logic r_input_outofrange;
    logic s_input_outofrange;
    logic pubkeyx_input_outofrange;
    logic pubkeyy_input_outofrange;
    logic pubkey_input_invalid;
    logic signing_process;
    logic verifying_process;


    logic mod_p_q;
    logic add_en;
    logic add_sub_i;
    logic [383 : 0] add_res0;
    logic add_cout0;
    logic add_cout1;
    logic add_res_less_than_prime;
    logic add_res_greater_than_prime;
    logic add_res_greater_than_384_bit;

    logic mult_ready;
    logic mult_last_reduction;
    logic mult_final_subtraction;

    assign mod_p_q = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.mod_p_q;
    assign add_en = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.add_en_i;
    assign add_sub_i = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.sub_i;
    assign add_res0 = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_ADDER_SUBTRACTOR.r0_reg;
    assign add_cout0 = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_ADDER_SUBTRACTOR.carry0_reg;
    assign add_cout1 = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_ADDER_SUBTRACTOR.carry1;
    assign add_res_less_than_prime = ((add_cout0 == 1'b0) & (add_res0 < ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.prime_i));
    assign add_res_greater_than_prime = ((add_cout0 == 1'b0) & (add_res0 >= ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.prime_i));
    assign add_res_greater_than_384_bit = (add_cout0 == 1'b1);
    
    assign mult_ready = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_MULTIPLIER.ready_o;
    assign mult_last_reduction = ecc_top.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_MULTIPLIER.last_reduction;
    assign mult_final_subtraction = mult_ready & mult_last_reduction;
    
    assign ecc_cmd = ecc_top.ecc_dsa_ctrl_i.cmd_reg;
    assign pcr_sign_mode = ecc_top.ecc_dsa_ctrl_i.pcr_sign_mode;
    assign zeroize = ecc_top.ecc_dsa_ctrl_i.zeroize_reg;
    assign ready = ecc_top.ecc_dsa_ctrl_i.dsa_ready_reg;
    assign valid = ecc_top.ecc_dsa_ctrl_i.dsa_valid_reg;

    always_ff @(posedge clk) begin
        if (!reset_n) begin
            ecc_sw_cmd <= '0;
        end
        else if (ecc_top.ecc_reg1.decoded_reg_strb.ECC_CTRL && ecc_top.ecc_reg1.decoded_req_is_wr) begin // SW write
            ecc_sw_cmd <= (ecc_top.ecc_reg1.field_storage.ECC_CTRL.CTRL.value & ~ecc_top.ecc_reg1.decoded_wr_biten[1:0]) | (ecc_top.ecc_reg1.decoded_wr_data[1:0] & ecc_top.ecc_reg1.decoded_wr_biten[1:0]);
        end
    end

    assign dest_keyvault = ecc_top.ecc_dsa_ctrl_i.dest_keyvault;

    assign error_flag = ecc_top.ecc_dsa_ctrl_i.error_flag;
    assign privkey_input_outofrange = ecc_top.ecc_dsa_ctrl_i.privkey_input_outofrange;
    assign r_output_outofrange = ecc_top.ecc_dsa_ctrl_i.r_output_outofrange;
    assign r_input_outofrange = ecc_top.ecc_dsa_ctrl_i.r_input_outofrange;
    assign s_input_outofrange = ecc_top.ecc_dsa_ctrl_i.s_input_outofrange;
    assign pubkeyx_input_outofrange = ecc_top.ecc_dsa_ctrl_i.pubkeyx_input_outofrange;
    assign pubkeyy_input_outofrange = ecc_top.ecc_dsa_ctrl_i.pubkeyy_input_outofrange;
    assign pubkey_input_invalid = ecc_top.ecc_dsa_ctrl_i.pubkey_input_invalid;
    assign signing_process = ecc_top.ecc_dsa_ctrl_i.signing_process;
    assign verifying_process = ecc_top.ecc_dsa_ctrl_i.verifying_process;

    covergroup ecc_top_cov_grp @(posedge clk);
        reset_cp: coverpoint reset_n;
        cptra_pwrgood_cp: coverpoint cptra_pwrgood;

        ecc_cmd_cp: coverpoint ecc_cmd;
        pcr_sign_cp: coverpoint pcr_sign_mode;
        zeroize_cp: coverpoint zeroize;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;

        dest_keyvault_cp: coverpoint dest_keyvault;

        error_flag_cp: coverpoint error_flag;
        privkey_input_outofrange_cp: coverpoint privkey_input_outofrange;
        r_output_outofrange_cp: coverpoint r_output_outofrange;
        r_input_outofrange_cp: coverpoint r_input_outofrange;
        s_input_outofrange_cp: coverpoint s_input_outofrange;
        pubkeyx_input_outofrange_cp: coverpoint pubkeyx_input_outofrange;
        pubkeyy_input_outofrange_cp: coverpoint pubkeyy_input_outofrange;
        pubkey_input_invalid_cp: coverpoint pubkey_input_invalid;

        cmd_ready_cp: cross ecc_sw_cmd, ready;
        cmd_kv_cp: cross ecc_cmd, dest_keyvault;
        pcr_ready_cp: cross ready, pcr_sign_mode;
        pcr_cmd_cp: cross pcr_sign_mode, ecc_cmd;
        zeroize_pcr_cp: cross zeroize, pcr_sign_mode;
        zeroize_cmd_cp: cross zeroize, ecc_cmd;
        zeroize_error_cp: cross zeroize, error_flag;
        zeroize_ready_cp: cross ready, zeroize;
        error_signing_cp: cross error_flag, signing_process;
        error_verifying_cp: cross error_flag, verifying_process;

        // modular operation
        mult_final_subtraction_cp: coverpoint mult_final_subtraction;
        add_carry_cp: cross mod_p_q, add_sub_i, add_cout0, add_cout1;
        add_result_less_than_prime_cp: cross mod_p_q, add_sub_i, add_res_less_than_prime;
        add_result_greater_than_prime_cp: cross mod_p_q, add_sub_i, add_res_greater_than_prime;
        add_result_greater_than_384_bit_cp: cross mod_p_q, add_sub_i, add_res_greater_than_384_bit;
        

    endgroup

    ecc_top_cov_grp ecc_top_cov_grp1 = new();

endinterface

`endif