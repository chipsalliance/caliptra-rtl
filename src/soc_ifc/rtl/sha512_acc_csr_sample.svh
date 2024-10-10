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

`ifndef SHA512_ACC_CSR_SAMPLE
    `define SHA512_ACC_CSR_SAMPLE
    
    /*----------------------- SHA512_ACC_CSR__LOCK SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__LOCK::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LOCK_bit_cg[bt]) this.LOCK_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*LOCK*/   );
        end
    endfunction

    function void sha512_acc_csr__LOCK::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LOCK_bit_cg[bt]) this.LOCK_bit_cg[bt].sample(LOCK.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( LOCK.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__ID SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__ID::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(ID_bit_cg[bt]) this.ID_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*ID*/   );
        end
    endfunction

    function void sha512_acc_csr__ID::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(ID_bit_cg[bt]) this.ID_bit_cg[bt].sample(ID.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( ID.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__MODE SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__MODE::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(MODE_bit_cg[bt]) this.MODE_bit_cg[bt].sample(data[0 + bt]);
            foreach(ENDIAN_TOGGLE_bit_cg[bt]) this.ENDIAN_TOGGLE_bit_cg[bt].sample(data[2 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[1:0]/*MODE*/  ,  data[2:2]/*ENDIAN_TOGGLE*/   );
        end
    endfunction

    function void sha512_acc_csr__MODE::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(MODE_bit_cg[bt]) this.MODE_bit_cg[bt].sample(MODE.get_mirrored_value() >> bt);
            foreach(ENDIAN_TOGGLE_bit_cg[bt]) this.ENDIAN_TOGGLE_bit_cg[bt].sample(ENDIAN_TOGGLE.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( MODE.get_mirrored_value()  ,  ENDIAN_TOGGLE.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__START_ADDRESS SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__START_ADDRESS::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(ADDR_bit_cg[bt]) this.ADDR_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*ADDR*/   );
        end
    endfunction

    function void sha512_acc_csr__START_ADDRESS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(ADDR_bit_cg[bt]) this.ADDR_bit_cg[bt].sample(ADDR.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( ADDR.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__DLEN SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__DLEN::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LENGTH_bit_cg[bt]) this.LENGTH_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*LENGTH*/   );
        end
    endfunction

    function void sha512_acc_csr__DLEN::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LENGTH_bit_cg[bt]) this.LENGTH_bit_cg[bt].sample(LENGTH.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( LENGTH.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__DATAIN SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__DATAIN::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(DATAIN_bit_cg[bt]) this.DATAIN_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*DATAIN*/   );
        end
    endfunction

    function void sha512_acc_csr__DATAIN::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(DATAIN_bit_cg[bt]) this.DATAIN_bit_cg[bt].sample(DATAIN.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( DATAIN.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__EXECUTE SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__EXECUTE::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(EXECUTE_bit_cg[bt]) this.EXECUTE_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*EXECUTE*/   );
        end
    endfunction

    function void sha512_acc_csr__EXECUTE::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(EXECUTE_bit_cg[bt]) this.EXECUTE_bit_cg[bt].sample(EXECUTE.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( EXECUTE.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__STATUS SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__STATUS::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(data[0 + bt]);
            foreach(SOC_HAS_LOCK_bit_cg[bt]) this.SOC_HAS_LOCK_bit_cg[bt].sample(data[1 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*VALID*/  ,  data[1:1]/*SOC_HAS_LOCK*/   );
        end
    endfunction

    function void sha512_acc_csr__STATUS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(VALID.get_mirrored_value() >> bt);
            foreach(SOC_HAS_LOCK_bit_cg[bt]) this.SOC_HAS_LOCK_bit_cg[bt].sample(SOC_HAS_LOCK.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( VALID.get_mirrored_value()  ,  SOC_HAS_LOCK.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__DIGEST SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__DIGEST::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(DIGEST_bit_cg[bt]) this.DIGEST_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*DIGEST*/   );
        end
    endfunction

    function void sha512_acc_csr__DIGEST::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(DIGEST_bit_cg[bt]) this.DIGEST_bit_cg[bt].sample(DIGEST.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( DIGEST.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__CONTROL SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__CONTROL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(ZEROIZE_bit_cg[bt]) this.ZEROIZE_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*ZEROIZE*/   );
        end
    endfunction

    function void sha512_acc_csr__CONTROL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(ZEROIZE_bit_cg[bt]) this.ZEROIZE_bit_cg[bt].sample(ZEROIZE.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( ZEROIZE.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__GLOBAL_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__global_intr_en_t::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__global_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_en_bit_cg[bt]) this.error_en_bit_cg[bt].sample(error_en.get_mirrored_value() >> bt);
            foreach(notif_en_bit_cg[bt]) this.notif_en_bit_cg[bt].sample(notif_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_en.get_mirrored_value()  ,  notif_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__ERROR_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__error_intr_en_t::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__error_intr_en_t::sample_values();
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

    /*----------------------- SHA512_ACC_CSR__NOTIF_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__notif_intr_en_t::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__notif_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_en_bit_cg[bt]) this.notif_cmd_done_en_bit_cg[bt].sample(notif_cmd_done_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__GLOBAL_INTR_T_AGG_STS_DD3DCF0A SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__global_intr_t_agg_sts_dd3dcf0a::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__global_intr_t_agg_sts_dd3dcf0a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__GLOBAL_INTR_T_AGG_STS_E6399B4A SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__global_intr_t_agg_sts_e6399b4a::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__global_intr_t_agg_sts_e6399b4a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__ERROR_INTR_T_ERROR0_STS_5EE134BF_ERROR1_STS_AAD9583F_ERROR2_STS_6CAD4575_ERROR3_STS_735BBEBA SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__error_intr_t_error0_sts_5ee134bf_error1_sts_aad9583f_error2_sts_6cad4575_error3_sts_735bbeba::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__error_intr_t_error0_sts_5ee134bf_error1_sts_aad9583f_error2_sts_6cad4575_error3_sts_735bbeba::sample_values();
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

    /*----------------------- SHA512_ACC_CSR__NOTIF_INTR_T_NOTIF_CMD_DONE_STS_1C68637E SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__notif_intr_t_notif_cmd_done_sts_1c68637e::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__notif_intr_t_notif_cmd_done_sts_1c68637e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_sts_bit_cg[bt]) this.notif_cmd_done_sts_bit_cg[bt].sample(notif_cmd_done_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__ERROR_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__error_intr_trig_t::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__error_intr_trig_t::sample_values();
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

    /*----------------------- SHA512_ACC_CSR__NOTIF_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__notif_intr_trig_t::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__notif_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_trig_bit_cg[bt]) this.notif_cmd_done_trig_bit_cg[bt].sample(notif_cmd_done_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_T_CNT_130AB269 SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__intr_count_t_cnt_130ab269::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__intr_count_t_cnt_130ab269::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_T_CNT_324DFC53 SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__intr_count_t_cnt_324dfc53::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__intr_count_t_cnt_324dfc53::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_T_CNT_791A4799 SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__intr_count_t_cnt_791a4799::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__intr_count_t_cnt_791a4799::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_T_CNT_E9DE7334 SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__intr_count_t_cnt_e9de7334::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__intr_count_t_cnt_e9de7334::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_T_CNT_BE67D6D5 SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__intr_count_t_cnt_be67d6d5::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__intr_count_t_cnt_be67d6d5::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_INCR_T_PULSE_37026C97 SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__intr_count_incr_t_pulse_37026c97::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__intr_count_incr_t_pulse_37026c97::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_INCR_T_PULSE_D860D977 SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__intr_count_incr_t_pulse_d860d977::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__intr_count_incr_t_pulse_d860d977::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_INCR_T_PULSE_87B45FE7 SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__intr_count_incr_t_pulse_87b45fe7::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__intr_count_incr_t_pulse_87b45fe7::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_INCR_T_PULSE_C1689EE6 SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__intr_count_incr_t_pulse_c1689ee6::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__intr_count_incr_t_pulse_c1689ee6::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SHA512_ACC_CSR__INTR_COUNT_INCR_T_PULSE_6173128E SAMPLE FUNCTIONS -----------------------*/
    function void sha512_acc_csr__intr_count_incr_t_pulse_6173128e::sample(uvm_reg_data_t  data,
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

    function void sha512_acc_csr__intr_count_incr_t_pulse_6173128e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

`endif