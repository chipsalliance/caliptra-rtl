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

`ifndef HMAC_REG_COVERGROUPS
    `define HMAC_REG_COVERGROUPS
    
    /*----------------------- HMAC_REG__HMAC512_NAME COVERGROUPS -----------------------*/
    covergroup hmac_reg__HMAC512_NAME_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__HMAC512_NAME_fld_cg with function sample(
    input bit [32-1:0] NAME
    );
        option.per_instance = 1;
        NAME_cp : coverpoint NAME;

    endgroup

    /*----------------------- HMAC_REG__HMAC512_VERSION COVERGROUPS -----------------------*/
    covergroup hmac_reg__HMAC512_VERSION_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__HMAC512_VERSION_fld_cg with function sample(
    input bit [32-1:0] VERSION
    );
        option.per_instance = 1;
        VERSION_cp : coverpoint VERSION;

    endgroup

    /*----------------------- HMAC_REG__HMAC512_CTRL COVERGROUPS -----------------------*/
    covergroup hmac_reg__HMAC512_CTRL_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__HMAC512_CTRL_fld_cg with function sample(
    input bit [1-1:0] INIT,
    input bit [1-1:0] NEXT,
    input bit [1-1:0] ZEROIZE,
    input bit [1-1:0] MODE,
    input bit [1-1:0] CSR_MODE,
    input bit [1-1:0] LAST,
    input bit [1-1:0] Reserved,
    input bit [1-1:0] RESTORE
    );
        option.per_instance = 1;
        INIT_cp : coverpoint INIT;
        NEXT_cp : coverpoint NEXT;
        ZEROIZE_cp : coverpoint ZEROIZE;
        MODE_cp : coverpoint MODE;
        CSR_MODE_cp : coverpoint CSR_MODE;
        LAST_cp : coverpoint LAST;
        Reserved_cp : coverpoint Reserved;
        RESTORE_cp : coverpoint RESTORE;

    endgroup

    /*----------------------- HMAC_REG__HMAC512_STATUS COVERGROUPS -----------------------*/
    covergroup hmac_reg__HMAC512_STATUS_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__HMAC512_STATUS_fld_cg with function sample(
    input bit [1-1:0] READY,
    input bit [1-1:0] VALID
    );
        option.per_instance = 1;
        READY_cp : coverpoint READY;
        VALID_cp : coverpoint VALID;

    endgroup

    /*----------------------- HMAC_REG__HMAC512_KEY COVERGROUPS -----------------------*/
    covergroup hmac_reg__HMAC512_KEY_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__HMAC512_KEY_fld_cg with function sample(
    input bit [32-1:0] KEY
    );
        option.per_instance = 1;
        KEY_cp : coverpoint KEY;

    endgroup

    /*----------------------- HMAC_REG__HMAC512_BLOCK COVERGROUPS -----------------------*/
    covergroup hmac_reg__HMAC512_BLOCK_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__HMAC512_BLOCK_fld_cg with function sample(
    input bit [32-1:0] BLOCK
    );
        option.per_instance = 1;
        BLOCK_cp : coverpoint BLOCK;

    endgroup

    /*----------------------- HMAC_REG__HMAC512_TAG COVERGROUPS -----------------------*/
    covergroup hmac_reg__HMAC512_TAG_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__HMAC512_TAG_fld_cg with function sample(
    input bit [32-1:0] TAG
    );
        option.per_instance = 1;
        TAG_cp : coverpoint TAG;

    endgroup

    /*----------------------- HMAC_REG__HMAC512_LFSR_SEED COVERGROUPS -----------------------*/
    covergroup hmac_reg__HMAC512_LFSR_SEED_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__HMAC512_LFSR_SEED_fld_cg with function sample(
    input bit [32-1:0] LFSR_SEED
    );
        option.per_instance = 1;
        LFSR_SEED_cp : coverpoint LFSR_SEED;

    endgroup

    /*----------------------- KV_READ_CTRL_REG COVERGROUPS -----------------------*/
    covergroup kv_read_ctrl_reg_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup kv_read_ctrl_reg_fld_cg with function sample(
    input bit [1-1:0] read_en,
    input bit [5-1:0] read_entry,
    input bit [1-1:0] pcr_hash_extend,
    input bit [25-1:0] rsvd
    );
        option.per_instance = 1;
        read_en_cp : coverpoint read_en;
        read_entry_cp : coverpoint read_entry;
        pcr_hash_extend_cp : coverpoint pcr_hash_extend;
        rsvd_cp : coverpoint rsvd;

    endgroup

    /*----------------------- KV_STATUS_REG COVERGROUPS -----------------------*/
    covergroup kv_status_reg_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup kv_status_reg_fld_cg with function sample(
    input bit [1-1:0] READY,
    input bit [1-1:0] VALID,
    input bit [8-1:0] ERROR
    );
        option.per_instance = 1;
        READY_cp : coverpoint READY;
        VALID_cp : coverpoint VALID;
        ERROR_cp : coverpoint ERROR;

    endgroup



    /*----------------------- KV_WRITE_CTRL_REG COVERGROUPS -----------------------*/
    covergroup kv_write_ctrl_reg_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup kv_write_ctrl_reg_fld_cg with function sample(
    input bit [1-1:0] write_en,
    input bit [5-1:0] write_entry,
    input bit [1-1:0] hmac_key_dest_valid,
    input bit [1-1:0] hmac_block_dest_valid,
    input bit [1-1:0] mldsa_seed_dest_valid,
    input bit [1-1:0] ecc_pkey_dest_valid,
    input bit [1-1:0] ecc_seed_dest_valid,
    input bit [1-1:0] aes_key_dest_valid,
    input bit [1-1:0] mlkem_seed_dest_valid,
    input bit [1-1:0] mlkem_msg_dest_valid,
    input bit [1-1:0] dma_data_dest_valid,
    input bit [17-1:0] rsvd
    );
        option.per_instance = 1;
        write_en_cp : coverpoint write_en;
        write_entry_cp : coverpoint write_entry;
        hmac_key_dest_valid_cp : coverpoint hmac_key_dest_valid;
        hmac_block_dest_valid_cp : coverpoint hmac_block_dest_valid;
        mldsa_seed_dest_valid_cp : coverpoint mldsa_seed_dest_valid;
        ecc_pkey_dest_valid_cp : coverpoint ecc_pkey_dest_valid;
        ecc_seed_dest_valid_cp : coverpoint ecc_seed_dest_valid;
        aes_key_dest_valid_cp : coverpoint aes_key_dest_valid;
        mlkem_seed_dest_valid_cp : coverpoint mlkem_seed_dest_valid;
        mlkem_msg_dest_valid_cp : coverpoint mlkem_msg_dest_valid;
        dma_data_dest_valid_cp : coverpoint dma_data_dest_valid;
        rsvd_cp : coverpoint rsvd;

    endgroup


    /*----------------------- HMAC_REG__GLOBAL_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup hmac_reg__global_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__global_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] error_en,
    input bit [1-1:0] notif_en
    );
        option.per_instance = 1;
        error_en_cp : coverpoint error_en;
        notif_en_cp : coverpoint notif_en;

    endgroup

    /*----------------------- HMAC_REG__ERROR_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup hmac_reg__error_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__error_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] key_mode_error_en,
    input bit [1-1:0] key_zero_error_en,
    input bit [1-1:0] error2_en,
    input bit [1-1:0] error3_en
    );
        option.per_instance = 1;
        key_mode_error_en_cp : coverpoint key_mode_error_en;
        key_zero_error_en_cp : coverpoint key_zero_error_en;
        error2_en_cp : coverpoint error2_en;
        error3_en_cp : coverpoint error3_en;

    endgroup

    /*----------------------- HMAC_REG__NOTIF_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup hmac_reg__notif_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__notif_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_en
    );
        option.per_instance = 1;
        notif_cmd_done_en_cp : coverpoint notif_cmd_done_en;

    endgroup

    /*----------------------- HMAC_REG__GLOBAL_INTR_T_AGG_STS_DD3DCF0A COVERGROUPS -----------------------*/
    covergroup hmac_reg__global_intr_t_agg_sts_dd3dcf0a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__global_intr_t_agg_sts_dd3dcf0a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- HMAC_REG__GLOBAL_INTR_T_AGG_STS_E6399B4A COVERGROUPS -----------------------*/
    covergroup hmac_reg__global_intr_t_agg_sts_e6399b4a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__global_intr_t_agg_sts_e6399b4a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- HMAC_REG__ERROR_INTR_T_ERROR2_STS_B1CF2205_ERROR3_STS_74A35378_KEY_MODE_ERROR_STS_F2304C86_KEY_ZERO_ERROR_STS_64A18183 COVERGROUPS -----------------------*/
    covergroup hmac_reg__error_intr_t_error2_sts_b1cf2205_error3_sts_74a35378_key_mode_error_sts_f2304c86_key_zero_error_sts_64a18183_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__error_intr_t_error2_sts_b1cf2205_error3_sts_74a35378_key_mode_error_sts_f2304c86_key_zero_error_sts_64a18183_fld_cg with function sample(
    input bit [1-1:0] key_mode_error_sts,
    input bit [1-1:0] key_zero_error_sts,
    input bit [1-1:0] error2_sts,
    input bit [1-1:0] error3_sts
    );
        option.per_instance = 1;
        key_mode_error_sts_cp : coverpoint key_mode_error_sts;
        key_zero_error_sts_cp : coverpoint key_zero_error_sts;
        error2_sts_cp : coverpoint error2_sts;
        error3_sts_cp : coverpoint error3_sts;

    endgroup

    /*----------------------- HMAC_REG__NOTIF_INTR_T_NOTIF_CMD_DONE_STS_1C68637E COVERGROUPS -----------------------*/
    covergroup hmac_reg__notif_intr_t_notif_cmd_done_sts_1c68637e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__notif_intr_t_notif_cmd_done_sts_1c68637e_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_sts
    );
        option.per_instance = 1;
        notif_cmd_done_sts_cp : coverpoint notif_cmd_done_sts;

    endgroup

    /*----------------------- HMAC_REG__ERROR_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup hmac_reg__error_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__error_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] key_mode_error_trig,
    input bit [1-1:0] key_zero_error_trig,
    input bit [1-1:0] error2_trig,
    input bit [1-1:0] error3_trig
    );
        option.per_instance = 1;
        key_mode_error_trig_cp : coverpoint key_mode_error_trig;
        key_zero_error_trig_cp : coverpoint key_zero_error_trig;
        error2_trig_cp : coverpoint error2_trig;
        error3_trig_cp : coverpoint error3_trig;

    endgroup

    /*----------------------- HMAC_REG__NOTIF_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup hmac_reg__notif_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__notif_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_trig
    );
        option.per_instance = 1;
        notif_cmd_done_trig_cp : coverpoint notif_cmd_done_trig;

    endgroup

    /*----------------------- HMAC_REG__INTR_COUNT_T_CNT_B8D41777 COVERGROUPS -----------------------*/
    covergroup hmac_reg__intr_count_t_cnt_b8d41777_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__intr_count_t_cnt_b8d41777_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- HMAC_REG__INTR_COUNT_T_CNT_55FC66D7 COVERGROUPS -----------------------*/
    covergroup hmac_reg__intr_count_t_cnt_55fc66d7_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__intr_count_t_cnt_55fc66d7_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- HMAC_REG__INTR_COUNT_T_CNT_D8AF96FF COVERGROUPS -----------------------*/
    covergroup hmac_reg__intr_count_t_cnt_d8af96ff_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__intr_count_t_cnt_d8af96ff_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- HMAC_REG__INTR_COUNT_T_CNT_9BD7F809 COVERGROUPS -----------------------*/
    covergroup hmac_reg__intr_count_t_cnt_9bd7f809_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__intr_count_t_cnt_9bd7f809_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- HMAC_REG__INTR_COUNT_T_CNT_BE67D6D5 COVERGROUPS -----------------------*/
    covergroup hmac_reg__intr_count_t_cnt_be67d6d5_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__intr_count_t_cnt_be67d6d5_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- HMAC_REG__INTR_COUNT_INCR_T_PULSE_14F62453 COVERGROUPS -----------------------*/
    covergroup hmac_reg__intr_count_incr_t_pulse_14f62453_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__intr_count_incr_t_pulse_14f62453_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- HMAC_REG__INTR_COUNT_INCR_T_PULSE_080329B7 COVERGROUPS -----------------------*/
    covergroup hmac_reg__intr_count_incr_t_pulse_080329b7_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__intr_count_incr_t_pulse_080329b7_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- HMAC_REG__INTR_COUNT_INCR_T_PULSE_87B45FE7 COVERGROUPS -----------------------*/
    covergroup hmac_reg__intr_count_incr_t_pulse_87b45fe7_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__intr_count_incr_t_pulse_87b45fe7_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- HMAC_REG__INTR_COUNT_INCR_T_PULSE_C1689EE6 COVERGROUPS -----------------------*/
    covergroup hmac_reg__intr_count_incr_t_pulse_c1689ee6_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__intr_count_incr_t_pulse_c1689ee6_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- HMAC_REG__INTR_COUNT_INCR_T_PULSE_6173128E COVERGROUPS -----------------------*/
    covergroup hmac_reg__intr_count_incr_t_pulse_6173128e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup hmac_reg__intr_count_incr_t_pulse_6173128e_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

`endif