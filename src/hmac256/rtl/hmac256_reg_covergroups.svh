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

`ifndef HMAC256_REG_COVERGROUPS
    `define HMAC256_REG_COVERGROUPS
    
    /*----------------------- HMAC256_REG__HMAC256_NAME COVERGROUPS -----------------------*/
    covergroup hmac256_reg__HMAC256_NAME_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__HMAC256_NAME_fld_cg with function sample(
    input bit [32-1:0] NAME
    );
        option.per_instance = 1;
        NAME_cp : coverpoint NAME;

    endgroup

    /*----------------------- HMAC256_REG__HMAC256_VERSION COVERGROUPS -----------------------*/
    covergroup hmac256_reg__HMAC256_VERSION_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__HMAC256_VERSION_fld_cg with function sample(
    input bit [32-1:0] VERSION
    );
        option.per_instance = 1;
        VERSION_cp : coverpoint VERSION;

    endgroup

    /*----------------------- HMAC256_REG__HMAC256_CTRL COVERGROUPS -----------------------*/
    covergroup hmac256_reg__HMAC256_CTRL_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__HMAC256_CTRL_fld_cg with function sample(
    input bit [1-1:0] INIT,
    input bit [1-1:0] NEXT,
    input bit [1-1:0] ZEROIZE,
    input bit [1-1:0] MODE,
    input bit [1-1:0] LAST,
    input bit [1-1:0] RESTORE
    );
        option.per_instance = 1;
        INIT_cp : coverpoint INIT;
        NEXT_cp : coverpoint NEXT;
        ZEROIZE_cp : coverpoint ZEROIZE;
        MODE_cp : coverpoint MODE;
        LAST_cp : coverpoint LAST;
        RESTORE_cp : coverpoint RESTORE;

    endgroup

    /*----------------------- HMAC256_REG__HMAC256_STATUS COVERGROUPS -----------------------*/
    covergroup hmac256_reg__HMAC256_STATUS_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__HMAC256_STATUS_fld_cg with function sample(
    input bit [1-1:0] READY,
    input bit [1-1:0] VALID
    );
        option.per_instance = 1;
        READY_cp : coverpoint READY;
        VALID_cp : coverpoint VALID;

    endgroup

    /*----------------------- HMAC256_REG__HMAC256_KEY COVERGROUPS -----------------------*/
    covergroup hmac256_reg__HMAC256_KEY_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__HMAC256_KEY_fld_cg with function sample(
    input bit [32-1:0] KEY
    );
        option.per_instance = 1;
        KEY_cp : coverpoint KEY;

    endgroup

    /*----------------------- HMAC256_REG__HMAC256_BLOCK COVERGROUPS -----------------------*/
    covergroup hmac256_reg__HMAC256_BLOCK_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__HMAC256_BLOCK_fld_cg with function sample(
    input bit [32-1:0] BLOCK
    );
        option.per_instance = 1;
        BLOCK_cp : coverpoint BLOCK;

    endgroup

    /*----------------------- HMAC256_REG__HMAC256_TAG COVERGROUPS -----------------------*/
    covergroup hmac256_reg__HMAC256_TAG_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__HMAC256_TAG_fld_cg with function sample(
    input bit [32-1:0] TAG
    );
        option.per_instance = 1;
        TAG_cp : coverpoint TAG;

    endgroup

    /*----------------------- HMAC256_REG__HMAC256_LFSR_SEED COVERGROUPS -----------------------*/
    covergroup hmac256_reg__HMAC256_LFSR_SEED_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__HMAC256_LFSR_SEED_fld_cg with function sample(
    input bit [32-1:0] LFSR_SEED
    );
        option.per_instance = 1;
        LFSR_SEED_cp : coverpoint LFSR_SEED;

    endgroup

    /*----------------------- HMAC256_REG__GLOBAL_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup hmac256_reg__global_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__global_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] error_en,
    input bit [1-1:0] notif_en
    );
        option.per_instance = 1;
        error_en_cp : coverpoint error_en;
        notif_en_cp : coverpoint notif_en;

    endgroup

    /*----------------------- HMAC256_REG__ERROR_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup hmac256_reg__error_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__error_intr_en_t_fld_cg with function sample(
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

    /*----------------------- HMAC256_REG__NOTIF_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup hmac256_reg__notif_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__notif_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_en
    );
        option.per_instance = 1;
        notif_cmd_done_en_cp : coverpoint notif_cmd_done_en;

    endgroup

    /*----------------------- HMAC256_REG__GLOBAL_INTR_T_AGG_STS_DD3DCF0A COVERGROUPS -----------------------*/
    covergroup hmac256_reg__global_intr_t_agg_sts_dd3dcf0a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__global_intr_t_agg_sts_dd3dcf0a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- HMAC256_REG__GLOBAL_INTR_T_AGG_STS_E6399B4A COVERGROUPS -----------------------*/
    covergroup hmac256_reg__global_intr_t_agg_sts_e6399b4a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__global_intr_t_agg_sts_e6399b4a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- HMAC256_REG__ERROR_INTR_T_ERROR0_STS_28545624_ERROR1_STS_40E0D3E1_ERROR2_STS_B1CF2205_ERROR3_STS_74A35378 COVERGROUPS -----------------------*/
    covergroup hmac256_reg__error_intr_t_error0_sts_28545624_error1_sts_40e0d3e1_error2_sts_b1cf2205_error3_sts_74a35378_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__error_intr_t_error0_sts_28545624_error1_sts_40e0d3e1_error2_sts_b1cf2205_error3_sts_74a35378_fld_cg with function sample(
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

    /*----------------------- HMAC256_REG__NOTIF_INTR_T_NOTIF_CMD_DONE_STS_1C68637E COVERGROUPS -----------------------*/
    covergroup hmac256_reg__notif_intr_t_notif_cmd_done_sts_1c68637e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__notif_intr_t_notif_cmd_done_sts_1c68637e_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_sts
    );
        option.per_instance = 1;
        notif_cmd_done_sts_cp : coverpoint notif_cmd_done_sts;

    endgroup

    /*----------------------- HMAC256_REG__ERROR_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup hmac256_reg__error_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__error_intr_trig_t_fld_cg with function sample(
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

    /*----------------------- HMAC256_REG__NOTIF_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup hmac256_reg__notif_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__notif_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_trig
    );
        option.per_instance = 1;
        notif_cmd_done_trig_cp : coverpoint notif_cmd_done_trig;

    endgroup

    /*----------------------- HMAC256_REG__INTR_COUNT_T_CNT_35ACE267 COVERGROUPS -----------------------*/
    covergroup hmac256_reg__intr_count_t_cnt_35ace267_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__intr_count_t_cnt_35ace267_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- HMAC256_REG__INTR_COUNT_T_CNT_73C42C28 COVERGROUPS -----------------------*/
    covergroup hmac256_reg__intr_count_t_cnt_73c42c28_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__intr_count_t_cnt_73c42c28_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- HMAC256_REG__INTR_COUNT_T_CNT_D8AF96FF COVERGROUPS -----------------------*/
    covergroup hmac256_reg__intr_count_t_cnt_d8af96ff_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__intr_count_t_cnt_d8af96ff_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- HMAC256_REG__INTR_COUNT_T_CNT_9BD7F809 COVERGROUPS -----------------------*/
    covergroup hmac256_reg__intr_count_t_cnt_9bd7f809_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__intr_count_t_cnt_9bd7f809_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- HMAC256_REG__INTR_COUNT_T_CNT_BE67D6D5 COVERGROUPS -----------------------*/
    covergroup hmac256_reg__intr_count_t_cnt_be67d6d5_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__intr_count_t_cnt_be67d6d5_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- HMAC256_REG__INTR_COUNT_INCR_T_PULSE_37026C97 COVERGROUPS -----------------------*/
    covergroup hmac256_reg__intr_count_incr_t_pulse_37026c97_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__intr_count_incr_t_pulse_37026c97_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- HMAC256_REG__INTR_COUNT_INCR_T_PULSE_D860D977 COVERGROUPS -----------------------*/
    covergroup hmac256_reg__intr_count_incr_t_pulse_d860d977_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__intr_count_incr_t_pulse_d860d977_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- HMAC256_REG__INTR_COUNT_INCR_T_PULSE_87B45FE7 COVERGROUPS -----------------------*/
    covergroup hmac256_reg__intr_count_incr_t_pulse_87b45fe7_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__intr_count_incr_t_pulse_87b45fe7_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- HMAC256_REG__INTR_COUNT_INCR_T_PULSE_C1689EE6 COVERGROUPS -----------------------*/
    covergroup hmac256_reg__intr_count_incr_t_pulse_c1689ee6_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__intr_count_incr_t_pulse_c1689ee6_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- HMAC256_REG__INTR_COUNT_INCR_T_PULSE_6173128E COVERGROUPS -----------------------*/
    covergroup hmac256_reg__intr_count_incr_t_pulse_6173128e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac256_reg__intr_count_incr_t_pulse_6173128e_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

`endif