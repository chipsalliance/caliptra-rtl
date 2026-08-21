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

`ifndef HMAC256_REG_SAMPLE
    `define HMAC256_REG_SAMPLE
    
    /*----------------------- HMAC256_REG__HMAC256_NAME SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__HMAC256_NAME::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(NAME_bit_cg[bt]) this.NAME_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*NAME*/   );
        end
    endfunction

    function void hmac256_reg__HMAC256_NAME::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(NAME_bit_cg[bt]) this.NAME_bit_cg[bt].sample(NAME.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( NAME.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__HMAC256_VERSION SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__HMAC256_VERSION::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VERSION_bit_cg[bt]) this.VERSION_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*VERSION*/   );
        end
    endfunction

    function void hmac256_reg__HMAC256_VERSION::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VERSION_bit_cg[bt]) this.VERSION_bit_cg[bt].sample(VERSION.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( VERSION.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__HMAC256_CTRL SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__HMAC256_CTRL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(INIT_bit_cg[bt]) this.INIT_bit_cg[bt].sample(data[0 + bt]);
            foreach(NEXT_bit_cg[bt]) this.NEXT_bit_cg[bt].sample(data[1 + bt]);
            foreach(ZEROIZE_bit_cg[bt]) this.ZEROIZE_bit_cg[bt].sample(data[2 + bt]);
            foreach(MODE_bit_cg[bt]) this.MODE_bit_cg[bt].sample(data[3 + bt]);
            foreach(LAST_bit_cg[bt]) this.LAST_bit_cg[bt].sample(data[4 + bt]);
            foreach(RESTORE_bit_cg[bt]) this.RESTORE_bit_cg[bt].sample(data[5 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*INIT*/  ,  data[1:1]/*NEXT*/  ,  data[2:2]/*ZEROIZE*/  ,  data[3:3]/*MODE*/  ,  data[4:4]/*LAST*/  ,  data[5:5]/*RESTORE*/   );
        end
    endfunction

    function void hmac256_reg__HMAC256_CTRL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(INIT_bit_cg[bt]) this.INIT_bit_cg[bt].sample(INIT.get_mirrored_value() >> bt);
            foreach(NEXT_bit_cg[bt]) this.NEXT_bit_cg[bt].sample(NEXT.get_mirrored_value() >> bt);
            foreach(ZEROIZE_bit_cg[bt]) this.ZEROIZE_bit_cg[bt].sample(ZEROIZE.get_mirrored_value() >> bt);
            foreach(MODE_bit_cg[bt]) this.MODE_bit_cg[bt].sample(MODE.get_mirrored_value() >> bt);
            foreach(LAST_bit_cg[bt]) this.LAST_bit_cg[bt].sample(LAST.get_mirrored_value() >> bt);
            foreach(RESTORE_bit_cg[bt]) this.RESTORE_bit_cg[bt].sample(RESTORE.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( INIT.get_mirrored_value()  ,  NEXT.get_mirrored_value()  ,  ZEROIZE.get_mirrored_value()  ,  MODE.get_mirrored_value()  ,  LAST.get_mirrored_value()  ,  RESTORE.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__HMAC256_STATUS SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__HMAC256_STATUS::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(data[0 + bt]);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(data[1 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*READY*/  ,  data[1:1]/*VALID*/   );
        end
    endfunction

    function void hmac256_reg__HMAC256_STATUS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(READY.get_mirrored_value() >> bt);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(VALID.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( READY.get_mirrored_value()  ,  VALID.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__HMAC256_KEY SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__HMAC256_KEY::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(KEY_bit_cg[bt]) this.KEY_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*KEY*/   );
        end
    endfunction

    function void hmac256_reg__HMAC256_KEY::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(KEY_bit_cg[bt]) this.KEY_bit_cg[bt].sample(KEY.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( KEY.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__HMAC256_BLOCK SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__HMAC256_BLOCK::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(BLOCK_bit_cg[bt]) this.BLOCK_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*BLOCK*/   );
        end
    endfunction

    function void hmac256_reg__HMAC256_BLOCK::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(BLOCK_bit_cg[bt]) this.BLOCK_bit_cg[bt].sample(BLOCK.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( BLOCK.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__HMAC256_TAG SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__HMAC256_TAG::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(TAG_bit_cg[bt]) this.TAG_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*TAG*/   );
        end
    endfunction

    function void hmac256_reg__HMAC256_TAG::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(TAG_bit_cg[bt]) this.TAG_bit_cg[bt].sample(TAG.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( TAG.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__HMAC256_LFSR_SEED SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__HMAC256_LFSR_SEED::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LFSR_SEED_bit_cg[bt]) this.LFSR_SEED_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*LFSR_SEED*/   );
        end
    endfunction

    function void hmac256_reg__HMAC256_LFSR_SEED::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LFSR_SEED_bit_cg[bt]) this.LFSR_SEED_bit_cg[bt].sample(LFSR_SEED.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( LFSR_SEED.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__GLOBAL_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__global_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_en_bit_cg[bt]) this.error_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(notif_en_bit_cg[bt]) this.notif_en_bit_cg[bt].sample(data[1 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_en*/  ,  data[1:1]/*notif_en*/   );
        end
    endfunction

    function void hmac256_reg__global_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_en_bit_cg[bt]) this.error_en_bit_cg[bt].sample(error_en.get_mirrored_value() >> bt);
            foreach(notif_en_bit_cg[bt]) this.notif_en_bit_cg[bt].sample(notif_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_en.get_mirrored_value()  ,  notif_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__ERROR_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__error_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error0_en_bit_cg[bt]) this.error0_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(error1_en_bit_cg[bt]) this.error1_en_bit_cg[bt].sample(data[1 + bt]);
            foreach(error2_en_bit_cg[bt]) this.error2_en_bit_cg[bt].sample(data[2 + bt]);
            foreach(error3_en_bit_cg[bt]) this.error3_en_bit_cg[bt].sample(data[3 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error0_en*/  ,  data[1:1]/*error1_en*/  ,  data[2:2]/*error2_en*/  ,  data[3:3]/*error3_en*/   );
        end
    endfunction

    function void hmac256_reg__error_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error0_en_bit_cg[bt]) this.error0_en_bit_cg[bt].sample(error0_en.get_mirrored_value() >> bt);
            foreach(error1_en_bit_cg[bt]) this.error1_en_bit_cg[bt].sample(error1_en.get_mirrored_value() >> bt);
            foreach(error2_en_bit_cg[bt]) this.error2_en_bit_cg[bt].sample(error2_en.get_mirrored_value() >> bt);
            foreach(error3_en_bit_cg[bt]) this.error3_en_bit_cg[bt].sample(error3_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error0_en.get_mirrored_value()  ,  error1_en.get_mirrored_value()  ,  error2_en.get_mirrored_value()  ,  error3_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__NOTIF_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__notif_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_en_bit_cg[bt]) this.notif_cmd_done_en_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_done_en*/   );
        end
    endfunction

    function void hmac256_reg__notif_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_en_bit_cg[bt]) this.notif_cmd_done_en_bit_cg[bt].sample(notif_cmd_done_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__GLOBAL_INTR_T_AGG_STS_DD3DCF0A SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__global_intr_t_agg_sts_dd3dcf0a::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*agg_sts*/   );
        end
    endfunction

    function void hmac256_reg__global_intr_t_agg_sts_dd3dcf0a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__GLOBAL_INTR_T_AGG_STS_E6399B4A SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__global_intr_t_agg_sts_e6399b4a::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*agg_sts*/   );
        end
    endfunction

    function void hmac256_reg__global_intr_t_agg_sts_e6399b4a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__ERROR_INTR_T_ERROR0_STS_28545624_ERROR1_STS_40E0D3E1_ERROR2_STS_B1CF2205_ERROR3_STS_74A35378 SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__error_intr_t_error0_sts_28545624_error1_sts_40e0d3e1_error2_sts_b1cf2205_error3_sts_74a35378::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error0_sts_bit_cg[bt]) this.error0_sts_bit_cg[bt].sample(data[0 + bt]);
            foreach(error1_sts_bit_cg[bt]) this.error1_sts_bit_cg[bt].sample(data[1 + bt]);
            foreach(error2_sts_bit_cg[bt]) this.error2_sts_bit_cg[bt].sample(data[2 + bt]);
            foreach(error3_sts_bit_cg[bt]) this.error3_sts_bit_cg[bt].sample(data[3 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error0_sts*/  ,  data[1:1]/*error1_sts*/  ,  data[2:2]/*error2_sts*/  ,  data[3:3]/*error3_sts*/   );
        end
    endfunction

    function void hmac256_reg__error_intr_t_error0_sts_28545624_error1_sts_40e0d3e1_error2_sts_b1cf2205_error3_sts_74a35378::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error0_sts_bit_cg[bt]) this.error0_sts_bit_cg[bt].sample(error0_sts.get_mirrored_value() >> bt);
            foreach(error1_sts_bit_cg[bt]) this.error1_sts_bit_cg[bt].sample(error1_sts.get_mirrored_value() >> bt);
            foreach(error2_sts_bit_cg[bt]) this.error2_sts_bit_cg[bt].sample(error2_sts.get_mirrored_value() >> bt);
            foreach(error3_sts_bit_cg[bt]) this.error3_sts_bit_cg[bt].sample(error3_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error0_sts.get_mirrored_value()  ,  error1_sts.get_mirrored_value()  ,  error2_sts.get_mirrored_value()  ,  error3_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__NOTIF_INTR_T_NOTIF_CMD_DONE_STS_1C68637E SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__notif_intr_t_notif_cmd_done_sts_1c68637e::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_sts_bit_cg[bt]) this.notif_cmd_done_sts_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_done_sts*/   );
        end
    endfunction

    function void hmac256_reg__notif_intr_t_notif_cmd_done_sts_1c68637e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_sts_bit_cg[bt]) this.notif_cmd_done_sts_bit_cg[bt].sample(notif_cmd_done_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__ERROR_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__error_intr_trig_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error0_trig_bit_cg[bt]) this.error0_trig_bit_cg[bt].sample(data[0 + bt]);
            foreach(error1_trig_bit_cg[bt]) this.error1_trig_bit_cg[bt].sample(data[1 + bt]);
            foreach(error2_trig_bit_cg[bt]) this.error2_trig_bit_cg[bt].sample(data[2 + bt]);
            foreach(error3_trig_bit_cg[bt]) this.error3_trig_bit_cg[bt].sample(data[3 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error0_trig*/  ,  data[1:1]/*error1_trig*/  ,  data[2:2]/*error2_trig*/  ,  data[3:3]/*error3_trig*/   );
        end
    endfunction

    function void hmac256_reg__error_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error0_trig_bit_cg[bt]) this.error0_trig_bit_cg[bt].sample(error0_trig.get_mirrored_value() >> bt);
            foreach(error1_trig_bit_cg[bt]) this.error1_trig_bit_cg[bt].sample(error1_trig.get_mirrored_value() >> bt);
            foreach(error2_trig_bit_cg[bt]) this.error2_trig_bit_cg[bt].sample(error2_trig.get_mirrored_value() >> bt);
            foreach(error3_trig_bit_cg[bt]) this.error3_trig_bit_cg[bt].sample(error3_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error0_trig.get_mirrored_value()  ,  error1_trig.get_mirrored_value()  ,  error2_trig.get_mirrored_value()  ,  error3_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__NOTIF_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__notif_intr_trig_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_trig_bit_cg[bt]) this.notif_cmd_done_trig_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_done_trig*/   );
        end
    endfunction

    function void hmac256_reg__notif_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_trig_bit_cg[bt]) this.notif_cmd_done_trig_bit_cg[bt].sample(notif_cmd_done_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__INTR_COUNT_T_CNT_35ACE267 SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__intr_count_t_cnt_35ace267::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void hmac256_reg__intr_count_t_cnt_35ace267::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__INTR_COUNT_T_CNT_73C42C28 SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__intr_count_t_cnt_73c42c28::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void hmac256_reg__intr_count_t_cnt_73c42c28::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__INTR_COUNT_T_CNT_D8AF96FF SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__intr_count_t_cnt_d8af96ff::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void hmac256_reg__intr_count_t_cnt_d8af96ff::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__INTR_COUNT_T_CNT_9BD7F809 SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__intr_count_t_cnt_9bd7f809::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void hmac256_reg__intr_count_t_cnt_9bd7f809::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__INTR_COUNT_T_CNT_BE67D6D5 SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__intr_count_t_cnt_be67d6d5::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void hmac256_reg__intr_count_t_cnt_be67d6d5::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__INTR_COUNT_INCR_T_PULSE_37026C97 SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__intr_count_incr_t_pulse_37026c97::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void hmac256_reg__intr_count_incr_t_pulse_37026c97::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__INTR_COUNT_INCR_T_PULSE_D860D977 SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__intr_count_incr_t_pulse_d860d977::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void hmac256_reg__intr_count_incr_t_pulse_d860d977::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__INTR_COUNT_INCR_T_PULSE_87B45FE7 SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__intr_count_incr_t_pulse_87b45fe7::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void hmac256_reg__intr_count_incr_t_pulse_87b45fe7::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__INTR_COUNT_INCR_T_PULSE_C1689EE6 SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__intr_count_incr_t_pulse_c1689ee6::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void hmac256_reg__intr_count_incr_t_pulse_c1689ee6::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- HMAC256_REG__INTR_COUNT_INCR_T_PULSE_6173128E SAMPLE FUNCTIONS -----------------------*/
    function void hmac256_reg__intr_count_incr_t_pulse_6173128e::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void hmac256_reg__intr_count_incr_t_pulse_6173128e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

`endif