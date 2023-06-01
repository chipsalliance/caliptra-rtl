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

`ifndef MBOX_CSR_SAMPLE
    `define MBOX_CSR_SAMPLE
    
    /*----------------------- MBOX_CSR__MBOX_LOCK SAMPLE FUNCTIONS -----------------------*/
    function void mbox_csr__mbox_lock::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lock_bit_cg[bt]) this.lock_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*lock*/   );
        end
    endfunction

    function void mbox_csr__mbox_lock::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lock_bit_cg[bt]) this.lock_bit_cg[bt].sample(lock.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( lock.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MBOX_CSR__MBOX_USER SAMPLE FUNCTIONS -----------------------*/
    function void mbox_csr__mbox_user::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(user_bit_cg[bt]) this.user_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*user*/   );
        end
    endfunction

    function void mbox_csr__mbox_user::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(user_bit_cg[bt]) this.user_bit_cg[bt].sample(user.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( user.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MBOX_CSR__MBOX_CMD SAMPLE FUNCTIONS -----------------------*/
    function void mbox_csr__mbox_cmd::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(command_bit_cg[bt]) this.command_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*command*/   );
        end
    endfunction

    function void mbox_csr__mbox_cmd::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(command_bit_cg[bt]) this.command_bit_cg[bt].sample(command.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( command.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MBOX_CSR__MBOX_DLEN SAMPLE FUNCTIONS -----------------------*/
    function void mbox_csr__mbox_dlen::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(length_bit_cg[bt]) this.length_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*length*/   );
        end
    endfunction

    function void mbox_csr__mbox_dlen::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(length_bit_cg[bt]) this.length_bit_cg[bt].sample(length.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( length.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MBOX_CSR__MBOX_DATAIN SAMPLE FUNCTIONS -----------------------*/
    function void mbox_csr__mbox_datain::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(datain_bit_cg[bt]) this.datain_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*datain*/   );
        end
    endfunction

    function void mbox_csr__mbox_datain::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(datain_bit_cg[bt]) this.datain_bit_cg[bt].sample(datain.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( datain.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MBOX_CSR__MBOX_DATAOUT SAMPLE FUNCTIONS -----------------------*/
    function void mbox_csr__mbox_dataout::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(dataout_bit_cg[bt]) this.dataout_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*dataout*/   );
        end
    endfunction

    function void mbox_csr__mbox_dataout::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(dataout_bit_cg[bt]) this.dataout_bit_cg[bt].sample(dataout.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( dataout.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MBOX_CSR__MBOX_EXECUTE SAMPLE FUNCTIONS -----------------------*/
    function void mbox_csr__mbox_execute::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(execute_bit_cg[bt]) this.execute_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*execute*/   );
        end
    endfunction

    function void mbox_csr__mbox_execute::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(execute_bit_cg[bt]) this.execute_bit_cg[bt].sample(execute.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( execute.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MBOX_CSR__MBOX_STATUS_ECC_DOUBLE_ERROR_38CEC4B0_ECC_SINGLE_ERROR_9C62B760 SAMPLE FUNCTIONS -----------------------*/
    function void mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(status_bit_cg[bt]) this.status_bit_cg[bt].sample(data[0 + bt]);
            foreach(ecc_single_error_bit_cg[bt]) this.ecc_single_error_bit_cg[bt].sample(data[4 + bt]);
            foreach(ecc_double_error_bit_cg[bt]) this.ecc_double_error_bit_cg[bt].sample(data[5 + bt]);
            foreach(mbox_fsm_ps_bit_cg[bt]) this.mbox_fsm_ps_bit_cg[bt].sample(data[6 + bt]);
            foreach(soc_has_lock_bit_cg[bt]) this.soc_has_lock_bit_cg[bt].sample(data[9 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[3:0]/*status*/  ,  data[4:4]/*ecc_single_error*/  ,  data[5:5]/*ecc_double_error*/  ,  data[8:6]/*mbox_fsm_ps*/  ,  data[9:9]/*soc_has_lock*/   );
        end
    endfunction

    function void mbox_csr__mbox_status_ecc_double_error_38cec4b0_ecc_single_error_9c62b760::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(status_bit_cg[bt]) this.status_bit_cg[bt].sample(status.get_mirrored_value() >> bt);
            foreach(ecc_single_error_bit_cg[bt]) this.ecc_single_error_bit_cg[bt].sample(ecc_single_error.get_mirrored_value() >> bt);
            foreach(ecc_double_error_bit_cg[bt]) this.ecc_double_error_bit_cg[bt].sample(ecc_double_error.get_mirrored_value() >> bt);
            foreach(mbox_fsm_ps_bit_cg[bt]) this.mbox_fsm_ps_bit_cg[bt].sample(mbox_fsm_ps.get_mirrored_value() >> bt);
            foreach(soc_has_lock_bit_cg[bt]) this.soc_has_lock_bit_cg[bt].sample(soc_has_lock.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( status.get_mirrored_value()  ,  ecc_single_error.get_mirrored_value()  ,  ecc_double_error.get_mirrored_value()  ,  mbox_fsm_ps.get_mirrored_value()  ,  soc_has_lock.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MBOX_CSR__MBOX_UNLOCK SAMPLE FUNCTIONS -----------------------*/
    function void mbox_csr__mbox_unlock::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(unlock_bit_cg[bt]) this.unlock_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*unlock*/   );
        end
    endfunction

    function void mbox_csr__mbox_unlock::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(unlock_bit_cg[bt]) this.unlock_bit_cg[bt].sample(unlock.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( unlock.get_mirrored_value()   );
        end
    endfunction

`endif