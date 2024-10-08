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

`ifndef SHA512_ACC_CSR_COVERGROUPS
    `define SHA512_ACC_CSR_COVERGROUPS
    
    /*----------------------- SHA512_ACC_CSR__LOCK COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__LOCK_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__LOCK_fld_cg with function sample(
    input bit [1-1:0] LOCK
    );
        option.per_instance = 1;
        LOCK_cp : coverpoint LOCK;

    endgroup

    /*----------------------- SHA512_ACC_CSR__ID COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__ID_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__ID_fld_cg with function sample(
    input bit [32-1:0] ID
    );
        option.per_instance = 1;
        ID_cp : coverpoint ID;

    endgroup

    /*----------------------- SHA512_ACC_CSR__MODE COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__MODE_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__MODE_fld_cg with function sample(
    input bit [2-1:0] MODE,
    input bit [1-1:0] ENDIAN_TOGGLE
    );
        option.per_instance = 1;
        MODE_cp : coverpoint MODE;
        ENDIAN_TOGGLE_cp : coverpoint ENDIAN_TOGGLE;

    endgroup

    /*----------------------- SHA512_ACC_CSR__START_ADDRESS COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__START_ADDRESS_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__START_ADDRESS_fld_cg with function sample(
    input bit [32-1:0] ADDR
    );
        option.per_instance = 1;
        ADDR_cp : coverpoint ADDR {
            bins zero_val = {32'h0};
            bins legal_val = {[1:32'h7FFF]};
            bins illegal_val = {[32'h8000:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SHA512_ACC_CSR__DLEN COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__DLEN_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__DLEN_fld_cg with function sample(
    input bit [32-1:0] LENGTH
    );
        option.per_instance = 1;
        LENGTH_cp : coverpoint LENGTH {
            bins zero_val = {32'h0};
            bins legal_byte_aligned_val  = {[1:32'h8000]};
            bins legal_word_aligned_val  = {[1:32'h8000]} with (~|item[0]);
            bins legal_dword_aligned_val = {[1:32'h8000]} with (~|item[1:0]);
            bins legal_qword_aligned_val = {[1:32'h8000]} with (~|item[2:0]);
            bins legal_oword_aligned_val = {[1:32'h8000]} with (~|item[3:0]);
            bins illegal_val = {[32'h8001:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SHA512_ACC_CSR__DATAIN COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__DATAIN_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__DATAIN_fld_cg with function sample(
    input bit [32-1:0] DATAIN
    );
        option.per_instance = 1;
        DATAIN_cp : coverpoint DATAIN;

    endgroup

    /*----------------------- SHA512_ACC_CSR__EXECUTE COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__EXECUTE_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__EXECUTE_fld_cg with function sample(
    input bit [1-1:0] EXECUTE
    );
        option.per_instance = 1;
        EXECUTE_cp : coverpoint EXECUTE;

    endgroup

    /*----------------------- SHA512_ACC_CSR__STATUS COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__STATUS_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__STATUS_fld_cg with function sample(
    input bit [1-1:0] VALID,
    input bit [1-1:0] SOC_HAS_LOCK
    );
        option.per_instance = 1;
        VALID_cp : coverpoint VALID;
        SOC_HAS_LOCK_cp : coverpoint SOC_HAS_LOCK;

    endgroup

    /*----------------------- SHA512_ACC_CSR__DIGEST COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__DIGEST_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__DIGEST_fld_cg with function sample(
    input bit [32-1:0] DIGEST
    );
        option.per_instance = 1;
        DIGEST_cp : coverpoint DIGEST;

    endgroup

    /*----------------------- SHA512_ACC_CSR__CONTROL COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__CONTROL_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__CONTROL_fld_cg with function sample(
    input bit [1-1:0] ZEROIZE
    );
        option.per_instance = 1;
        ZEROIZE_cp : coverpoint ZEROIZE;

    endgroup

    /*----------------------- SHA512_ACC_CSR__GLOBAL_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__global_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__global_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] error_en,
    input bit [1-1:0] notif_en
    );
        option.per_instance = 1;
        error_en_cp : coverpoint error_en;
        notif_en_cp : coverpoint notif_en;

    endgroup

    /*----------------------- SHA512_ACC_CSR__ERROR_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__error_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__error_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] error0_en,
    input bit [1-1:0] error1_en,
    input bit [1-1:0] error2_en,
    input bit [1-1:0] error3_en
    );
        option.per_instance = 1;
        error0_en_cp : coverpoint error0_en;
        error1_en_cp : coverpoint error1_en;
        error2_en_cp : coverpoint error2_en;
        error3_en_cp : coverpoint error3_en;

    endgroup

    /*----------------------- SHA512_ACC_CSR__NOTIF_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__notif_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__notif_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_en
    );
        option.per_instance = 1;
        notif_cmd_done_en_cp : coverpoint notif_cmd_done_en;

    endgroup

    /*----------------------- SHA512_ACC_CSR__GLOBAL_INTR_T_AGG_STS_DD3DCF0A COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__global_intr_t_agg_sts_dd3dcf0a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__global_intr_t_agg_sts_dd3dcf0a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- SHA512_ACC_CSR__GLOBAL_INTR_T_AGG_STS_E6399B4A COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__global_intr_t_agg_sts_e6399b4a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__global_intr_t_agg_sts_e6399b4a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- SHA512_ACC_CSR__ERROR_INTR_T_ERROR0_STS_5EE134BF_ERROR1_STS_AAD9583F_ERROR2_STS_6CAD4575_ERROR3_STS_735BBEBA COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__error_intr_t_error0_sts_5ee134bf_error1_sts_aad9583f_error2_sts_6cad4575_error3_sts_735bbeba_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__error_intr_t_error0_sts_5ee134bf_error1_sts_aad9583f_error2_sts_6cad4575_error3_sts_735bbeba_fld_cg with function sample(
    input bit [1-1:0] error0_sts,
    input bit [1-1:0] error1_sts,
    input bit [1-1:0] error2_sts,
    input bit [1-1:0] error3_sts
    );
        option.per_instance = 1;
        error0_sts_cp : coverpoint error0_sts;
        error1_sts_cp : coverpoint error1_sts;
        error2_sts_cp : coverpoint error2_sts;
        error3_sts_cp : coverpoint error3_sts;

    endgroup

    /*----------------------- SHA512_ACC_CSR__NOTIF_INTR_T_NOTIF_CMD_DONE_STS_1C68637E COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__notif_intr_t_notif_cmd_done_sts_1c68637e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__notif_intr_t_notif_cmd_done_sts_1c68637e_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_sts
    );
        option.per_instance = 1;
        notif_cmd_done_sts_cp : coverpoint notif_cmd_done_sts;

    endgroup

    /*----------------------- SHA512_ACC_CSR__ERROR_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__error_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__error_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] error0_trig,
    input bit [1-1:0] error1_trig,
    input bit [1-1:0] error2_trig,
    input bit [1-1:0] error3_trig
    );
        option.per_instance = 1;
        error0_trig_cp : coverpoint error0_trig;
        error1_trig_cp : coverpoint error1_trig;
        error2_trig_cp : coverpoint error2_trig;
        error3_trig_cp : coverpoint error3_trig;

    endgroup

    /*----------------------- SHA512_ACC_CSR__NOTIF_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__notif_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__notif_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_trig
    );
        option.per_instance = 1;
        notif_cmd_done_trig_cp : coverpoint notif_cmd_done_trig;

    endgroup

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_T_CNT_130AB269 COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__intr_count_t_cnt_130ab269_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__intr_count_t_cnt_130ab269_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_T_CNT_324DFC53 COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__intr_count_t_cnt_324dfc53_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__intr_count_t_cnt_324dfc53_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_T_CNT_791A4799 COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__intr_count_t_cnt_791a4799_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__intr_count_t_cnt_791a4799_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_T_CNT_E9DE7334 COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__intr_count_t_cnt_e9de7334_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__intr_count_t_cnt_e9de7334_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_T_CNT_BE67D6D5 COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__intr_count_t_cnt_be67d6d5_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__intr_count_t_cnt_be67d6d5_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_INCR_T_PULSE_37026C97 COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__intr_count_incr_t_pulse_37026c97_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__intr_count_incr_t_pulse_37026c97_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_INCR_T_PULSE_D860D977 COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__intr_count_incr_t_pulse_d860d977_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__intr_count_incr_t_pulse_d860d977_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_INCR_T_PULSE_87B45FE7 COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__intr_count_incr_t_pulse_87b45fe7_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__intr_count_incr_t_pulse_87b45fe7_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_INCR_T_PULSE_C1689EE6 COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__intr_count_incr_t_pulse_c1689ee6_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__intr_count_incr_t_pulse_c1689ee6_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_INCR_T_PULSE_6173128E COVERGROUPS -----------------------*/
    covergroup sha512_acc_csr__intr_count_incr_t_pulse_6173128e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup sha512_acc_csr__intr_count_incr_t_pulse_6173128e_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

`endif
