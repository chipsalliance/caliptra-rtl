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

`ifndef SOC_IFC_REG_SAMPLE
    `define SOC_IFC_REG_SAMPLE
    
    /*----------------------- SOC_IFC_REG__CPTRA_HW_ERROR_FATAL SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_HW_ERROR_FATAL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(iccm_ecc_unc_bit_cg[bt]) this.iccm_ecc_unc_bit_cg[bt].sample(data[0 + bt]);
            foreach(dccm_ecc_unc_bit_cg[bt]) this.dccm_ecc_unc_bit_cg[bt].sample(data[1 + bt]);
            foreach(nmi_pin_bit_cg[bt]) this.nmi_pin_bit_cg[bt].sample(data[2 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*iccm_ecc_unc*/  ,  data[1:1]/*dccm_ecc_unc*/  ,  data[2:2]/*nmi_pin*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_HW_ERROR_FATAL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(iccm_ecc_unc_bit_cg[bt]) this.iccm_ecc_unc_bit_cg[bt].sample(iccm_ecc_unc.get_mirrored_value() >> bt);
            foreach(dccm_ecc_unc_bit_cg[bt]) this.dccm_ecc_unc_bit_cg[bt].sample(dccm_ecc_unc.get_mirrored_value() >> bt);
            foreach(nmi_pin_bit_cg[bt]) this.nmi_pin_bit_cg[bt].sample(nmi_pin.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( iccm_ecc_unc.get_mirrored_value()  ,  dccm_ecc_unc.get_mirrored_value()  ,  nmi_pin.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_HW_ERROR_NON_FATAL SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_HW_ERROR_NON_FATAL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mbox_prot_no_lock_bit_cg[bt]) this.mbox_prot_no_lock_bit_cg[bt].sample(data[0 + bt]);
            foreach(mbox_prot_ooo_bit_cg[bt]) this.mbox_prot_ooo_bit_cg[bt].sample(data[1 + bt]);
            foreach(mbox_ecc_unc_bit_cg[bt]) this.mbox_ecc_unc_bit_cg[bt].sample(data[2 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*mbox_prot_no_lock*/  ,  data[1:1]/*mbox_prot_ooo*/  ,  data[2:2]/*mbox_ecc_unc*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_HW_ERROR_NON_FATAL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mbox_prot_no_lock_bit_cg[bt]) this.mbox_prot_no_lock_bit_cg[bt].sample(mbox_prot_no_lock.get_mirrored_value() >> bt);
            foreach(mbox_prot_ooo_bit_cg[bt]) this.mbox_prot_ooo_bit_cg[bt].sample(mbox_prot_ooo.get_mirrored_value() >> bt);
            foreach(mbox_ecc_unc_bit_cg[bt]) this.mbox_ecc_unc_bit_cg[bt].sample(mbox_ecc_unc.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( mbox_prot_no_lock.get_mirrored_value()  ,  mbox_prot_ooo.get_mirrored_value()  ,  mbox_ecc_unc.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_FW_ERROR_FATAL SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_FW_ERROR_FATAL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_code_bit_cg[bt]) this.error_code_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*error_code*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_FW_ERROR_FATAL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_code_bit_cg[bt]) this.error_code_bit_cg[bt].sample(error_code.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_code.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_FW_ERROR_NON_FATAL SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_FW_ERROR_NON_FATAL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_code_bit_cg[bt]) this.error_code_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*error_code*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_FW_ERROR_NON_FATAL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_code_bit_cg[bt]) this.error_code_bit_cg[bt].sample(error_code.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_code.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_HW_ERROR_ENC SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_HW_ERROR_ENC::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_code_bit_cg[bt]) this.error_code_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*error_code*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_HW_ERROR_ENC::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_code_bit_cg[bt]) this.error_code_bit_cg[bt].sample(error_code.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_code.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_FW_ERROR_ENC SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_FW_ERROR_ENC::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_code_bit_cg[bt]) this.error_code_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*error_code*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_FW_ERROR_ENC::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_code_bit_cg[bt]) this.error_code_bit_cg[bt].sample(error_code.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_code.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_FW_EXTENDED_ERROR_INFO SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_FW_EXTENDED_ERROR_INFO::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_info_bit_cg[bt]) this.error_info_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*error_info*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_FW_EXTENDED_ERROR_INFO::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_info_bit_cg[bt]) this.error_info_bit_cg[bt].sample(error_info.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_info.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_BOOT_STATUS SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_BOOT_STATUS::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(status_bit_cg[bt]) this.status_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*status*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_BOOT_STATUS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(status_bit_cg[bt]) this.status_bit_cg[bt].sample(status.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( status.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_FLOW_STATUS SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_FLOW_STATUS::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(status_bit_cg[bt]) this.status_bit_cg[bt].sample(data[0 + bt]);
            foreach(ready_for_fw_bit_cg[bt]) this.ready_for_fw_bit_cg[bt].sample(data[28 + bt]);
            foreach(ready_for_runtime_bit_cg[bt]) this.ready_for_runtime_bit_cg[bt].sample(data[29 + bt]);
            foreach(ready_for_fuses_bit_cg[bt]) this.ready_for_fuses_bit_cg[bt].sample(data[30 + bt]);
            foreach(mailbox_flow_done_bit_cg[bt]) this.mailbox_flow_done_bit_cg[bt].sample(data[31 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[27:0]/*status*/  ,  data[28:28]/*ready_for_fw*/  ,  data[29:29]/*ready_for_runtime*/  ,  data[30:30]/*ready_for_fuses*/  ,  data[31:31]/*mailbox_flow_done*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_FLOW_STATUS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(status_bit_cg[bt]) this.status_bit_cg[bt].sample(status.get_mirrored_value() >> bt);
            foreach(ready_for_fw_bit_cg[bt]) this.ready_for_fw_bit_cg[bt].sample(ready_for_fw.get_mirrored_value() >> bt);
            foreach(ready_for_runtime_bit_cg[bt]) this.ready_for_runtime_bit_cg[bt].sample(ready_for_runtime.get_mirrored_value() >> bt);
            foreach(ready_for_fuses_bit_cg[bt]) this.ready_for_fuses_bit_cg[bt].sample(ready_for_fuses.get_mirrored_value() >> bt);
            foreach(mailbox_flow_done_bit_cg[bt]) this.mailbox_flow_done_bit_cg[bt].sample(mailbox_flow_done.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( status.get_mirrored_value()  ,  ready_for_fw.get_mirrored_value()  ,  ready_for_runtime.get_mirrored_value()  ,  ready_for_fuses.get_mirrored_value()  ,  mailbox_flow_done.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_RESET_REASON SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_RESET_REASON::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(FW_UPD_RESET_bit_cg[bt]) this.FW_UPD_RESET_bit_cg[bt].sample(data[0 + bt]);
            foreach(WARM_RESET_bit_cg[bt]) this.WARM_RESET_bit_cg[bt].sample(data[1 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*FW_UPD_RESET*/  ,  data[1:1]/*WARM_RESET*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_RESET_REASON::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(FW_UPD_RESET_bit_cg[bt]) this.FW_UPD_RESET_bit_cg[bt].sample(FW_UPD_RESET.get_mirrored_value() >> bt);
            foreach(WARM_RESET_bit_cg[bt]) this.WARM_RESET_bit_cg[bt].sample(WARM_RESET.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( FW_UPD_RESET.get_mirrored_value()  ,  WARM_RESET.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_SECURITY_STATE SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_SECURITY_STATE::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(device_lifecycle_bit_cg[bt]) this.device_lifecycle_bit_cg[bt].sample(data[0 + bt]);
            foreach(debug_locked_bit_cg[bt]) this.debug_locked_bit_cg[bt].sample(data[2 + bt]);
            foreach(scan_mode_bit_cg[bt]) this.scan_mode_bit_cg[bt].sample(data[3 + bt]);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(data[4 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[1:0]/*device_lifecycle*/  ,  data[2:2]/*debug_locked*/  ,  data[3:3]/*scan_mode*/  ,  data[31:4]/*rsvd*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_SECURITY_STATE::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(device_lifecycle_bit_cg[bt]) this.device_lifecycle_bit_cg[bt].sample(device_lifecycle.get_mirrored_value() >> bt);
            foreach(debug_locked_bit_cg[bt]) this.debug_locked_bit_cg[bt].sample(debug_locked.get_mirrored_value() >> bt);
            foreach(scan_mode_bit_cg[bt]) this.scan_mode_bit_cg[bt].sample(scan_mode.get_mirrored_value() >> bt);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(rsvd.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( device_lifecycle.get_mirrored_value()  ,  debug_locked.get_mirrored_value()  ,  scan_mode.get_mirrored_value()  ,  rsvd.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_MBOX_VALID_PAUSER SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_MBOX_VALID_PAUSER::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(PAUSER_bit_cg[bt]) this.PAUSER_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*PAUSER*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_MBOX_VALID_PAUSER::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(PAUSER_bit_cg[bt]) this.PAUSER_bit_cg[bt].sample(PAUSER.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( PAUSER.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_MBOX_PAUSER_LOCK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_MBOX_PAUSER_LOCK::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__CPTRA_MBOX_PAUSER_LOCK::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LOCK_bit_cg[bt]) this.LOCK_bit_cg[bt].sample(LOCK.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( LOCK.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_TRNG_VALID_PAUSER SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_TRNG_VALID_PAUSER::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(PAUSER_bit_cg[bt]) this.PAUSER_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*PAUSER*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_TRNG_VALID_PAUSER::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(PAUSER_bit_cg[bt]) this.PAUSER_bit_cg[bt].sample(PAUSER.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( PAUSER.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_TRNG_PAUSER_LOCK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_TRNG_PAUSER_LOCK::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__CPTRA_TRNG_PAUSER_LOCK::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LOCK_bit_cg[bt]) this.LOCK_bit_cg[bt].sample(LOCK.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( LOCK.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_TRNG_DATA SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_TRNG_DATA::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(DATA_bit_cg[bt]) this.DATA_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*DATA*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_TRNG_DATA::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(DATA_bit_cg[bt]) this.DATA_bit_cg[bt].sample(DATA.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( DATA.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_TRNG_STATUS SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_TRNG_STATUS::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(DATA_REQ_bit_cg[bt]) this.DATA_REQ_bit_cg[bt].sample(data[0 + bt]);
            foreach(DATA_WR_DONE_bit_cg[bt]) this.DATA_WR_DONE_bit_cg[bt].sample(data[1 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*DATA_REQ*/  ,  data[1:1]/*DATA_WR_DONE*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_TRNG_STATUS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(DATA_REQ_bit_cg[bt]) this.DATA_REQ_bit_cg[bt].sample(DATA_REQ.get_mirrored_value() >> bt);
            foreach(DATA_WR_DONE_bit_cg[bt]) this.DATA_WR_DONE_bit_cg[bt].sample(DATA_WR_DONE.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( DATA_REQ.get_mirrored_value()  ,  DATA_WR_DONE.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_FUSE_WR_DONE SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_FUSE_WR_DONE::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(done_bit_cg[bt]) this.done_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*done*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_FUSE_WR_DONE::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(done_bit_cg[bt]) this.done_bit_cg[bt].sample(done.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( done.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_TIMER_CONFIG SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_TIMER_CONFIG::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(clk_period_bit_cg[bt]) this.clk_period_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*clk_period*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_TIMER_CONFIG::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(clk_period_bit_cg[bt]) this.clk_period_bit_cg[bt].sample(clk_period.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( clk_period.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_BOOTFSM_GO SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_BOOTFSM_GO::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(GO_bit_cg[bt]) this.GO_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*GO*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_BOOTFSM_GO::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(GO_bit_cg[bt]) this.GO_bit_cg[bt].sample(GO.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( GO.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_DBG_MANUF_SERVICE_REG SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_DBG_MANUF_SERVICE_REG::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(DATA_bit_cg[bt]) this.DATA_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*DATA*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_DBG_MANUF_SERVICE_REG::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(DATA_bit_cg[bt]) this.DATA_bit_cg[bt].sample(DATA.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( DATA.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_CLK_GATING_EN SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_CLK_GATING_EN::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(clk_gating_en_bit_cg[bt]) this.clk_gating_en_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*clk_gating_en*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_CLK_GATING_EN::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(clk_gating_en_bit_cg[bt]) this.clk_gating_en_bit_cg[bt].sample(clk_gating_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( clk_gating_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_GENERIC_INPUT_WIRES SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_GENERIC_INPUT_WIRES::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(generic_wires_bit_cg[bt]) this.generic_wires_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*generic_wires*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_GENERIC_INPUT_WIRES::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(generic_wires_bit_cg[bt]) this.generic_wires_bit_cg[bt].sample(generic_wires.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( generic_wires.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_GENERIC_OUTPUT_WIRES SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_GENERIC_OUTPUT_WIRES::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(generic_wires_bit_cg[bt]) this.generic_wires_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*generic_wires*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_GENERIC_OUTPUT_WIRES::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(generic_wires_bit_cg[bt]) this.generic_wires_bit_cg[bt].sample(generic_wires.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( generic_wires.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_HW_REV_ID SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_HW_REV_ID::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(REV_ID_bit_cg[bt]) this.REV_ID_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*REV_ID*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_HW_REV_ID::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(REV_ID_bit_cg[bt]) this.REV_ID_bit_cg[bt].sample(REV_ID.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( REV_ID.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_FW_REV_ID SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_FW_REV_ID::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(REV_ID_bit_cg[bt]) this.REV_ID_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*REV_ID*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_FW_REV_ID::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(REV_ID_bit_cg[bt]) this.REV_ID_bit_cg[bt].sample(REV_ID.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( REV_ID.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_HW_CONFIG SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_HW_CONFIG::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(iTRNG_en_bit_cg[bt]) this.iTRNG_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(QSPI_en_bit_cg[bt]) this.QSPI_en_bit_cg[bt].sample(data[1 + bt]);
            foreach(I3C_en_bit_cg[bt]) this.I3C_en_bit_cg[bt].sample(data[2 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*iTRNG_en*/  ,  data[1:1]/*QSPI_en*/  ,  data[2:2]/*I3C_en*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_HW_CONFIG::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(iTRNG_en_bit_cg[bt]) this.iTRNG_en_bit_cg[bt].sample(iTRNG_en.get_mirrored_value() >> bt);
            foreach(QSPI_en_bit_cg[bt]) this.QSPI_en_bit_cg[bt].sample(QSPI_en.get_mirrored_value() >> bt);
            foreach(I3C_en_bit_cg[bt]) this.I3C_en_bit_cg[bt].sample(I3C_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( iTRNG_en.get_mirrored_value()  ,  QSPI_en.get_mirrored_value()  ,  I3C_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_TIMER1_EN SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_WDT_TIMER1_EN::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(timer1_en_bit_cg[bt]) this.timer1_en_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*timer1_en*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_WDT_TIMER1_EN::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(timer1_en_bit_cg[bt]) this.timer1_en_bit_cg[bt].sample(timer1_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( timer1_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_TIMER1_CTRL SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_WDT_TIMER1_CTRL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(timer1_restart_bit_cg[bt]) this.timer1_restart_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*timer1_restart*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_WDT_TIMER1_CTRL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(timer1_restart_bit_cg[bt]) this.timer1_restart_bit_cg[bt].sample(timer1_restart.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( timer1_restart.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_TIMER1_TIMEOUT_PERIOD SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_WDT_TIMER1_TIMEOUT_PERIOD::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(timer1_timeout_period_bit_cg[bt]) this.timer1_timeout_period_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*timer1_timeout_period*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_WDT_TIMER1_TIMEOUT_PERIOD::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(timer1_timeout_period_bit_cg[bt]) this.timer1_timeout_period_bit_cg[bt].sample(timer1_timeout_period.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( timer1_timeout_period.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_TIMER2_EN SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_WDT_TIMER2_EN::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(timer2_en_bit_cg[bt]) this.timer2_en_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*timer2_en*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_WDT_TIMER2_EN::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(timer2_en_bit_cg[bt]) this.timer2_en_bit_cg[bt].sample(timer2_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( timer2_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_TIMER2_CTRL SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_WDT_TIMER2_CTRL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(timer2_restart_bit_cg[bt]) this.timer2_restart_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*timer2_restart*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_WDT_TIMER2_CTRL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(timer2_restart_bit_cg[bt]) this.timer2_restart_bit_cg[bt].sample(timer2_restart.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( timer2_restart.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_TIMER2_TIMEOUT_PERIOD SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_WDT_TIMER2_TIMEOUT_PERIOD::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(timer2_timeout_period_bit_cg[bt]) this.timer2_timeout_period_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*timer2_timeout_period*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_WDT_TIMER2_TIMEOUT_PERIOD::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(timer2_timeout_period_bit_cg[bt]) this.timer2_timeout_period_bit_cg[bt].sample(timer2_timeout_period.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( timer2_timeout_period.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_STATUS SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_WDT_STATUS::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(t1_timeout_bit_cg[bt]) this.t1_timeout_bit_cg[bt].sample(data[0 + bt]);
            foreach(t2_timeout_bit_cg[bt]) this.t2_timeout_bit_cg[bt].sample(data[1 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*t1_timeout*/  ,  data[1:1]/*t2_timeout*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_WDT_STATUS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(t1_timeout_bit_cg[bt]) this.t1_timeout_bit_cg[bt].sample(t1_timeout.get_mirrored_value() >> bt);
            foreach(t2_timeout_bit_cg[bt]) this.t2_timeout_bit_cg[bt].sample(t2_timeout.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( t1_timeout.get_mirrored_value()  ,  t2_timeout.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_FUSE_VALID_PAUSER SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_FUSE_VALID_PAUSER::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(PAUSER_bit_cg[bt]) this.PAUSER_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*PAUSER*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_FUSE_VALID_PAUSER::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(PAUSER_bit_cg[bt]) this.PAUSER_bit_cg[bt].sample(PAUSER.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( PAUSER.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_FUSE_PAUSER_LOCK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_FUSE_PAUSER_LOCK::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__CPTRA_FUSE_PAUSER_LOCK::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LOCK_bit_cg[bt]) this.LOCK_bit_cg[bt].sample(LOCK.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( LOCK.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_UDS_SEED SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_uds_seed::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(seed_bit_cg[bt]) this.seed_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*seed*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_uds_seed::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(seed_bit_cg[bt]) this.seed_bit_cg[bt].sample(seed.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( seed.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_FIELD_ENTROPY SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_field_entropy::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(seed_bit_cg[bt]) this.seed_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*seed*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_field_entropy::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(seed_bit_cg[bt]) this.seed_bit_cg[bt].sample(seed.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( seed.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_KEY_MANIFEST_PK_HASH SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_key_manifest_pk_hash::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(hash_bit_cg[bt]) this.hash_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*hash*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_key_manifest_pk_hash::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(hash_bit_cg[bt]) this.hash_bit_cg[bt].sample(hash.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( hash.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_KEY_MANIFEST_PK_HASH_MASK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_key_manifest_pk_hash_mask::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mask_bit_cg[bt]) this.mask_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[3:0]/*mask*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_key_manifest_pk_hash_mask::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mask_bit_cg[bt]) this.mask_bit_cg[bt].sample(mask.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( mask.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_OWNER_PK_HASH SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_owner_pk_hash::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(hash_bit_cg[bt]) this.hash_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*hash*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_owner_pk_hash::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(hash_bit_cg[bt]) this.hash_bit_cg[bt].sample(hash.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( hash.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_FMC_KEY_MANIFEST_SVN SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_fmc_key_manifest_svn::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(svn_bit_cg[bt]) this.svn_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*svn*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_fmc_key_manifest_svn::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(svn_bit_cg[bt]) this.svn_bit_cg[bt].sample(svn.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( svn.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_RUNTIME_SVN SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_runtime_svn::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(svn_bit_cg[bt]) this.svn_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*svn*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_runtime_svn::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(svn_bit_cg[bt]) this.svn_bit_cg[bt].sample(svn.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( svn.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_ANTI_ROLLBACK_DISABLE SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_anti_rollback_disable::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(dis_bit_cg[bt]) this.dis_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*dis*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_anti_rollback_disable::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(dis_bit_cg[bt]) this.dis_bit_cg[bt].sample(dis.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( dis.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_IDEVID_CERT_ATTR SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_idevid_cert_attr::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cert_bit_cg[bt]) this.cert_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cert*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_idevid_cert_attr::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cert_bit_cg[bt]) this.cert_bit_cg[bt].sample(cert.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cert.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_IDEVID_MANUF_HSM_ID SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_idevid_manuf_hsm_id::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(hsm_id_bit_cg[bt]) this.hsm_id_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*hsm_id*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_idevid_manuf_hsm_id::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(hsm_id_bit_cg[bt]) this.hsm_id_bit_cg[bt].sample(hsm_id.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( hsm_id.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_LIFE_CYCLE SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_life_cycle::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(life_cycle_bit_cg[bt]) this.life_cycle_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[1:0]/*life_cycle*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_life_cycle::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(life_cycle_bit_cg[bt]) this.life_cycle_bit_cg[bt].sample(life_cycle.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( life_cycle.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_LMS_VERIFY SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_lms_verify::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lms_verify_bit_cg[bt]) this.lms_verify_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*lms_verify*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_lms_verify::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lms_verify_bit_cg[bt]) this.lms_verify_bit_cg[bt].sample(lms_verify.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( lms_verify.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_LMS_REVOCATION SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_lms_revocation::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lms_revocation_bit_cg[bt]) this.lms_revocation_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*lms_revocation*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_lms_revocation::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lms_revocation_bit_cg[bt]) this.lms_revocation_bit_cg[bt].sample(lms_revocation.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( lms_revocation.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_OBF_KEY SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_obf_key::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(key_bit_cg[bt]) this.key_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*key*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_obf_key::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(key_bit_cg[bt]) this.key_bit_cg[bt].sample(key.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( key.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_ICCM_LOCK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_iccm_lock::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__internal_iccm_lock::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lock_bit_cg[bt]) this.lock_bit_cg[bt].sample(lock.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( lock.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_FW_UPDATE_RESET SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_fw_update_reset::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(core_rst_bit_cg[bt]) this.core_rst_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*core_rst*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_fw_update_reset::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(core_rst_bit_cg[bt]) this.core_rst_bit_cg[bt].sample(core_rst.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( core_rst.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_fw_update_reset_wait_cycles::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(wait_cycles_bit_cg[bt]) this.wait_cycles_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[7:0]/*wait_cycles*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_fw_update_reset_wait_cycles::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(wait_cycles_bit_cg[bt]) this.wait_cycles_bit_cg[bt].sample(wait_cycles.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( wait_cycles.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_NMI_VECTOR SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_nmi_vector::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(vec_bit_cg[bt]) this.vec_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*vec*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_nmi_vector::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(vec_bit_cg[bt]) this.vec_bit_cg[bt].sample(vec.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( vec.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_HW_ERROR_FATAL_MASK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_hw_error_fatal_mask::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mask_iccm_ecc_unc_bit_cg[bt]) this.mask_iccm_ecc_unc_bit_cg[bt].sample(data[0 + bt]);
            foreach(mask_dccm_ecc_unc_bit_cg[bt]) this.mask_dccm_ecc_unc_bit_cg[bt].sample(data[1 + bt]);
            foreach(mask_nmi_pin_bit_cg[bt]) this.mask_nmi_pin_bit_cg[bt].sample(data[2 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*mask_iccm_ecc_unc*/  ,  data[1:1]/*mask_dccm_ecc_unc*/  ,  data[2:2]/*mask_nmi_pin*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_hw_error_fatal_mask::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mask_iccm_ecc_unc_bit_cg[bt]) this.mask_iccm_ecc_unc_bit_cg[bt].sample(mask_iccm_ecc_unc.get_mirrored_value() >> bt);
            foreach(mask_dccm_ecc_unc_bit_cg[bt]) this.mask_dccm_ecc_unc_bit_cg[bt].sample(mask_dccm_ecc_unc.get_mirrored_value() >> bt);
            foreach(mask_nmi_pin_bit_cg[bt]) this.mask_nmi_pin_bit_cg[bt].sample(mask_nmi_pin.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( mask_iccm_ecc_unc.get_mirrored_value()  ,  mask_dccm_ecc_unc.get_mirrored_value()  ,  mask_nmi_pin.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_HW_ERROR_NON_FATAL_MASK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_hw_error_non_fatal_mask::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mask_mbox_prot_no_lock_bit_cg[bt]) this.mask_mbox_prot_no_lock_bit_cg[bt].sample(data[0 + bt]);
            foreach(mask_mbox_prot_ooo_bit_cg[bt]) this.mask_mbox_prot_ooo_bit_cg[bt].sample(data[1 + bt]);
            foreach(mask_mbox_ecc_unc_bit_cg[bt]) this.mask_mbox_ecc_unc_bit_cg[bt].sample(data[2 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*mask_mbox_prot_no_lock*/  ,  data[1:1]/*mask_mbox_prot_ooo*/  ,  data[2:2]/*mask_mbox_ecc_unc*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_hw_error_non_fatal_mask::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mask_mbox_prot_no_lock_bit_cg[bt]) this.mask_mbox_prot_no_lock_bit_cg[bt].sample(mask_mbox_prot_no_lock.get_mirrored_value() >> bt);
            foreach(mask_mbox_prot_ooo_bit_cg[bt]) this.mask_mbox_prot_ooo_bit_cg[bt].sample(mask_mbox_prot_ooo.get_mirrored_value() >> bt);
            foreach(mask_mbox_ecc_unc_bit_cg[bt]) this.mask_mbox_ecc_unc_bit_cg[bt].sample(mask_mbox_ecc_unc.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( mask_mbox_prot_no_lock.get_mirrored_value()  ,  mask_mbox_prot_ooo.get_mirrored_value()  ,  mask_mbox_ecc_unc.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_FW_ERROR_FATAL_MASK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_fw_error_fatal_mask::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mask_bit_cg[bt]) this.mask_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*mask*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_fw_error_fatal_mask::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mask_bit_cg[bt]) this.mask_bit_cg[bt].sample(mask.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( mask.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_FW_ERROR_NON_FATAL_MASK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_fw_error_non_fatal_mask::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mask_bit_cg[bt]) this.mask_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*mask*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_fw_error_non_fatal_mask::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mask_bit_cg[bt]) this.mask_bit_cg[bt].sample(mask.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( mask.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_RV_MTIME_L SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_rv_mtime_l::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(count_l_bit_cg[bt]) this.count_l_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*count_l*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_rv_mtime_l::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(count_l_bit_cg[bt]) this.count_l_bit_cg[bt].sample(count_l.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( count_l.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_RV_MTIME_H SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_rv_mtime_h::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(count_h_bit_cg[bt]) this.count_h_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*count_h*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_rv_mtime_h::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(count_h_bit_cg[bt]) this.count_h_bit_cg[bt].sample(count_h.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( count_h.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_RV_MTIMECMP_L SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_rv_mtimecmp_l::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(compare_l_bit_cg[bt]) this.compare_l_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*compare_l*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_rv_mtimecmp_l::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(compare_l_bit_cg[bt]) this.compare_l_bit_cg[bt].sample(compare_l.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( compare_l.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTERNAL_RV_MTIMECMP_H SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__internal_rv_mtimecmp_h::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(compare_h_bit_cg[bt]) this.compare_h_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*compare_h*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_rv_mtimecmp_h::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(compare_h_bit_cg[bt]) this.compare_h_bit_cg[bt].sample(compare_h.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( compare_h.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__GLOBAL_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__global_intr_en_t::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__global_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_en_bit_cg[bt]) this.error_en_bit_cg[bt].sample(error_en.get_mirrored_value() >> bt);
            foreach(notif_en_bit_cg[bt]) this.notif_en_bit_cg[bt].sample(notif_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_en.get_mirrored_value()  ,  notif_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__ERROR_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__error_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_en_bit_cg[bt]) this.error_internal_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(error_inv_dev_en_bit_cg[bt]) this.error_inv_dev_en_bit_cg[bt].sample(data[1 + bt]);
            foreach(error_cmd_fail_en_bit_cg[bt]) this.error_cmd_fail_en_bit_cg[bt].sample(data[2 + bt]);
            foreach(error_bad_fuse_en_bit_cg[bt]) this.error_bad_fuse_en_bit_cg[bt].sample(data[3 + bt]);
            foreach(error_iccm_blocked_en_bit_cg[bt]) this.error_iccm_blocked_en_bit_cg[bt].sample(data[4 + bt]);
            foreach(error_mbox_ecc_unc_en_bit_cg[bt]) this.error_mbox_ecc_unc_en_bit_cg[bt].sample(data[5 + bt]);
            foreach(error_wdt_timer1_timeout_en_bit_cg[bt]) this.error_wdt_timer1_timeout_en_bit_cg[bt].sample(data[6 + bt]);
            foreach(error_wdt_timer2_timeout_en_bit_cg[bt]) this.error_wdt_timer2_timeout_en_bit_cg[bt].sample(data[7 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_internal_en*/  ,  data[1:1]/*error_inv_dev_en*/  ,  data[2:2]/*error_cmd_fail_en*/  ,  data[3:3]/*error_bad_fuse_en*/  ,  data[4:4]/*error_iccm_blocked_en*/  ,  data[5:5]/*error_mbox_ecc_unc_en*/  ,  data[6:6]/*error_wdt_timer1_timeout_en*/  ,  data[7:7]/*error_wdt_timer2_timeout_en*/   );
        end
    endfunction

    function void soc_ifc_reg__intr_block_t__error_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_en_bit_cg[bt]) this.error_internal_en_bit_cg[bt].sample(error_internal_en.get_mirrored_value() >> bt);
            foreach(error_inv_dev_en_bit_cg[bt]) this.error_inv_dev_en_bit_cg[bt].sample(error_inv_dev_en.get_mirrored_value() >> bt);
            foreach(error_cmd_fail_en_bit_cg[bt]) this.error_cmd_fail_en_bit_cg[bt].sample(error_cmd_fail_en.get_mirrored_value() >> bt);
            foreach(error_bad_fuse_en_bit_cg[bt]) this.error_bad_fuse_en_bit_cg[bt].sample(error_bad_fuse_en.get_mirrored_value() >> bt);
            foreach(error_iccm_blocked_en_bit_cg[bt]) this.error_iccm_blocked_en_bit_cg[bt].sample(error_iccm_blocked_en.get_mirrored_value() >> bt);
            foreach(error_mbox_ecc_unc_en_bit_cg[bt]) this.error_mbox_ecc_unc_en_bit_cg[bt].sample(error_mbox_ecc_unc_en.get_mirrored_value() >> bt);
            foreach(error_wdt_timer1_timeout_en_bit_cg[bt]) this.error_wdt_timer1_timeout_en_bit_cg[bt].sample(error_wdt_timer1_timeout_en.get_mirrored_value() >> bt);
            foreach(error_wdt_timer2_timeout_en_bit_cg[bt]) this.error_wdt_timer2_timeout_en_bit_cg[bt].sample(error_wdt_timer2_timeout_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_internal_en.get_mirrored_value()  ,  error_inv_dev_en.get_mirrored_value()  ,  error_cmd_fail_en.get_mirrored_value()  ,  error_bad_fuse_en.get_mirrored_value()  ,  error_iccm_blocked_en.get_mirrored_value()  ,  error_mbox_ecc_unc_en.get_mirrored_value()  ,  error_wdt_timer1_timeout_en.get_mirrored_value()  ,  error_wdt_timer2_timeout_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__NOTIF_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__notif_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_avail_en_bit_cg[bt]) this.notif_cmd_avail_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(notif_mbox_ecc_cor_en_bit_cg[bt]) this.notif_mbox_ecc_cor_en_bit_cg[bt].sample(data[1 + bt]);
            foreach(notif_debug_locked_en_bit_cg[bt]) this.notif_debug_locked_en_bit_cg[bt].sample(data[2 + bt]);
            foreach(notif_soc_req_lock_en_bit_cg[bt]) this.notif_soc_req_lock_en_bit_cg[bt].sample(data[3 + bt]);
            foreach(notif_gen_in_toggle_en_bit_cg[bt]) this.notif_gen_in_toggle_en_bit_cg[bt].sample(data[4 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_avail_en*/  ,  data[1:1]/*notif_mbox_ecc_cor_en*/  ,  data[2:2]/*notif_debug_locked_en*/  ,  data[3:3]/*notif_soc_req_lock_en*/  ,  data[4:4]/*notif_gen_in_toggle_en*/   );
        end
    endfunction

    function void soc_ifc_reg__intr_block_t__notif_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_avail_en_bit_cg[bt]) this.notif_cmd_avail_en_bit_cg[bt].sample(notif_cmd_avail_en.get_mirrored_value() >> bt);
            foreach(notif_mbox_ecc_cor_en_bit_cg[bt]) this.notif_mbox_ecc_cor_en_bit_cg[bt].sample(notif_mbox_ecc_cor_en.get_mirrored_value() >> bt);
            foreach(notif_debug_locked_en_bit_cg[bt]) this.notif_debug_locked_en_bit_cg[bt].sample(notif_debug_locked_en.get_mirrored_value() >> bt);
            foreach(notif_soc_req_lock_en_bit_cg[bt]) this.notif_soc_req_lock_en_bit_cg[bt].sample(notif_soc_req_lock_en.get_mirrored_value() >> bt);
            foreach(notif_gen_in_toggle_en_bit_cg[bt]) this.notif_gen_in_toggle_en_bit_cg[bt].sample(notif_gen_in_toggle_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_avail_en.get_mirrored_value()  ,  notif_mbox_ecc_cor_en.get_mirrored_value()  ,  notif_debug_locked_en.get_mirrored_value()  ,  notif_soc_req_lock_en.get_mirrored_value()  ,  notif_gen_in_toggle_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_DD3DCF0A SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_E6399B4A SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__ERROR_INTR_T_ERROR_BAD_FUSE_STS_23F67582_ERROR_CMD_FAIL_STS_B85845F8_ERROR_ICCM_BLOCKED_STS_E81E6AD2_ERROR_INTERNAL_STS_CAAD62E2_ERROR_INV_DEV_STS_6693E7DB_ERROR_MBOX_ECC_UNC_STS_30BFF330_ERROR_WDT_TIMER1_TIMEOUT_STS_6AAA9655_ERROR_WDT_TIMER2_TIMEOUT_STS_CDA8789F SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__error_intr_t_error_bad_fuse_sts_23f67582_error_cmd_fail_sts_b85845f8_error_iccm_blocked_sts_e81e6ad2_error_internal_sts_caad62e2_error_inv_dev_sts_6693e7db_error_mbox_ecc_unc_sts_30bff330_error_wdt_timer1_timeout_sts_6aaa9655_error_wdt_timer2_timeout_sts_cda8789f::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_sts_bit_cg[bt]) this.error_internal_sts_bit_cg[bt].sample(data[0 + bt]);
            foreach(error_inv_dev_sts_bit_cg[bt]) this.error_inv_dev_sts_bit_cg[bt].sample(data[1 + bt]);
            foreach(error_cmd_fail_sts_bit_cg[bt]) this.error_cmd_fail_sts_bit_cg[bt].sample(data[2 + bt]);
            foreach(error_bad_fuse_sts_bit_cg[bt]) this.error_bad_fuse_sts_bit_cg[bt].sample(data[3 + bt]);
            foreach(error_iccm_blocked_sts_bit_cg[bt]) this.error_iccm_blocked_sts_bit_cg[bt].sample(data[4 + bt]);
            foreach(error_mbox_ecc_unc_sts_bit_cg[bt]) this.error_mbox_ecc_unc_sts_bit_cg[bt].sample(data[5 + bt]);
            foreach(error_wdt_timer1_timeout_sts_bit_cg[bt]) this.error_wdt_timer1_timeout_sts_bit_cg[bt].sample(data[6 + bt]);
            foreach(error_wdt_timer2_timeout_sts_bit_cg[bt]) this.error_wdt_timer2_timeout_sts_bit_cg[bt].sample(data[7 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_internal_sts*/  ,  data[1:1]/*error_inv_dev_sts*/  ,  data[2:2]/*error_cmd_fail_sts*/  ,  data[3:3]/*error_bad_fuse_sts*/  ,  data[4:4]/*error_iccm_blocked_sts*/  ,  data[5:5]/*error_mbox_ecc_unc_sts*/  ,  data[6:6]/*error_wdt_timer1_timeout_sts*/  ,  data[7:7]/*error_wdt_timer2_timeout_sts*/   );
        end
    endfunction

    function void soc_ifc_reg__intr_block_t__error_intr_t_error_bad_fuse_sts_23f67582_error_cmd_fail_sts_b85845f8_error_iccm_blocked_sts_e81e6ad2_error_internal_sts_caad62e2_error_inv_dev_sts_6693e7db_error_mbox_ecc_unc_sts_30bff330_error_wdt_timer1_timeout_sts_6aaa9655_error_wdt_timer2_timeout_sts_cda8789f::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_sts_bit_cg[bt]) this.error_internal_sts_bit_cg[bt].sample(error_internal_sts.get_mirrored_value() >> bt);
            foreach(error_inv_dev_sts_bit_cg[bt]) this.error_inv_dev_sts_bit_cg[bt].sample(error_inv_dev_sts.get_mirrored_value() >> bt);
            foreach(error_cmd_fail_sts_bit_cg[bt]) this.error_cmd_fail_sts_bit_cg[bt].sample(error_cmd_fail_sts.get_mirrored_value() >> bt);
            foreach(error_bad_fuse_sts_bit_cg[bt]) this.error_bad_fuse_sts_bit_cg[bt].sample(error_bad_fuse_sts.get_mirrored_value() >> bt);
            foreach(error_iccm_blocked_sts_bit_cg[bt]) this.error_iccm_blocked_sts_bit_cg[bt].sample(error_iccm_blocked_sts.get_mirrored_value() >> bt);
            foreach(error_mbox_ecc_unc_sts_bit_cg[bt]) this.error_mbox_ecc_unc_sts_bit_cg[bt].sample(error_mbox_ecc_unc_sts.get_mirrored_value() >> bt);
            foreach(error_wdt_timer1_timeout_sts_bit_cg[bt]) this.error_wdt_timer1_timeout_sts_bit_cg[bt].sample(error_wdt_timer1_timeout_sts.get_mirrored_value() >> bt);
            foreach(error_wdt_timer2_timeout_sts_bit_cg[bt]) this.error_wdt_timer2_timeout_sts_bit_cg[bt].sample(error_wdt_timer2_timeout_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_internal_sts.get_mirrored_value()  ,  error_inv_dev_sts.get_mirrored_value()  ,  error_cmd_fail_sts.get_mirrored_value()  ,  error_bad_fuse_sts.get_mirrored_value()  ,  error_iccm_blocked_sts.get_mirrored_value()  ,  error_mbox_ecc_unc_sts.get_mirrored_value()  ,  error_wdt_timer1_timeout_sts.get_mirrored_value()  ,  error_wdt_timer2_timeout_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__NOTIF_INTR_T_NOTIF_CMD_AVAIL_STS_1871606B_NOTIF_DEBUG_LOCKED_STS_5F024102_NOTIF_GEN_IN_TOGGLE_STS_59F84B64_NOTIF_MBOX_ECC_COR_STS_5C3D26BB_NOTIF_SOC_REQ_LOCK_STS_DEDDDE70 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__notif_intr_t_notif_cmd_avail_sts_1871606b_notif_debug_locked_sts_5f024102_notif_gen_in_toggle_sts_59f84b64_notif_mbox_ecc_cor_sts_5c3d26bb_notif_soc_req_lock_sts_deddde70::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_avail_sts_bit_cg[bt]) this.notif_cmd_avail_sts_bit_cg[bt].sample(data[0 + bt]);
            foreach(notif_mbox_ecc_cor_sts_bit_cg[bt]) this.notif_mbox_ecc_cor_sts_bit_cg[bt].sample(data[1 + bt]);
            foreach(notif_debug_locked_sts_bit_cg[bt]) this.notif_debug_locked_sts_bit_cg[bt].sample(data[2 + bt]);
            foreach(notif_soc_req_lock_sts_bit_cg[bt]) this.notif_soc_req_lock_sts_bit_cg[bt].sample(data[3 + bt]);
            foreach(notif_gen_in_toggle_sts_bit_cg[bt]) this.notif_gen_in_toggle_sts_bit_cg[bt].sample(data[4 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_avail_sts*/  ,  data[1:1]/*notif_mbox_ecc_cor_sts*/  ,  data[2:2]/*notif_debug_locked_sts*/  ,  data[3:3]/*notif_soc_req_lock_sts*/  ,  data[4:4]/*notif_gen_in_toggle_sts*/   );
        end
    endfunction

    function void soc_ifc_reg__intr_block_t__notif_intr_t_notif_cmd_avail_sts_1871606b_notif_debug_locked_sts_5f024102_notif_gen_in_toggle_sts_59f84b64_notif_mbox_ecc_cor_sts_5c3d26bb_notif_soc_req_lock_sts_deddde70::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_avail_sts_bit_cg[bt]) this.notif_cmd_avail_sts_bit_cg[bt].sample(notif_cmd_avail_sts.get_mirrored_value() >> bt);
            foreach(notif_mbox_ecc_cor_sts_bit_cg[bt]) this.notif_mbox_ecc_cor_sts_bit_cg[bt].sample(notif_mbox_ecc_cor_sts.get_mirrored_value() >> bt);
            foreach(notif_debug_locked_sts_bit_cg[bt]) this.notif_debug_locked_sts_bit_cg[bt].sample(notif_debug_locked_sts.get_mirrored_value() >> bt);
            foreach(notif_soc_req_lock_sts_bit_cg[bt]) this.notif_soc_req_lock_sts_bit_cg[bt].sample(notif_soc_req_lock_sts.get_mirrored_value() >> bt);
            foreach(notif_gen_in_toggle_sts_bit_cg[bt]) this.notif_gen_in_toggle_sts_bit_cg[bt].sample(notif_gen_in_toggle_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_avail_sts.get_mirrored_value()  ,  notif_mbox_ecc_cor_sts.get_mirrored_value()  ,  notif_debug_locked_sts.get_mirrored_value()  ,  notif_soc_req_lock_sts.get_mirrored_value()  ,  notif_gen_in_toggle_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__ERROR_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__error_intr_trig_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_trig_bit_cg[bt]) this.error_internal_trig_bit_cg[bt].sample(data[0 + bt]);
            foreach(error_inv_dev_trig_bit_cg[bt]) this.error_inv_dev_trig_bit_cg[bt].sample(data[1 + bt]);
            foreach(error_cmd_fail_trig_bit_cg[bt]) this.error_cmd_fail_trig_bit_cg[bt].sample(data[2 + bt]);
            foreach(error_bad_fuse_trig_bit_cg[bt]) this.error_bad_fuse_trig_bit_cg[bt].sample(data[3 + bt]);
            foreach(error_iccm_blocked_trig_bit_cg[bt]) this.error_iccm_blocked_trig_bit_cg[bt].sample(data[4 + bt]);
            foreach(error_mbox_ecc_unc_trig_bit_cg[bt]) this.error_mbox_ecc_unc_trig_bit_cg[bt].sample(data[5 + bt]);
            foreach(error_wdt_timer1_timeout_trig_bit_cg[bt]) this.error_wdt_timer1_timeout_trig_bit_cg[bt].sample(data[6 + bt]);
            foreach(error_wdt_timer2_timeout_trig_bit_cg[bt]) this.error_wdt_timer2_timeout_trig_bit_cg[bt].sample(data[7 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_internal_trig*/  ,  data[1:1]/*error_inv_dev_trig*/  ,  data[2:2]/*error_cmd_fail_trig*/  ,  data[3:3]/*error_bad_fuse_trig*/  ,  data[4:4]/*error_iccm_blocked_trig*/  ,  data[5:5]/*error_mbox_ecc_unc_trig*/  ,  data[6:6]/*error_wdt_timer1_timeout_trig*/  ,  data[7:7]/*error_wdt_timer2_timeout_trig*/   );
        end
    endfunction

    function void soc_ifc_reg__intr_block_t__error_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_trig_bit_cg[bt]) this.error_internal_trig_bit_cg[bt].sample(error_internal_trig.get_mirrored_value() >> bt);
            foreach(error_inv_dev_trig_bit_cg[bt]) this.error_inv_dev_trig_bit_cg[bt].sample(error_inv_dev_trig.get_mirrored_value() >> bt);
            foreach(error_cmd_fail_trig_bit_cg[bt]) this.error_cmd_fail_trig_bit_cg[bt].sample(error_cmd_fail_trig.get_mirrored_value() >> bt);
            foreach(error_bad_fuse_trig_bit_cg[bt]) this.error_bad_fuse_trig_bit_cg[bt].sample(error_bad_fuse_trig.get_mirrored_value() >> bt);
            foreach(error_iccm_blocked_trig_bit_cg[bt]) this.error_iccm_blocked_trig_bit_cg[bt].sample(error_iccm_blocked_trig.get_mirrored_value() >> bt);
            foreach(error_mbox_ecc_unc_trig_bit_cg[bt]) this.error_mbox_ecc_unc_trig_bit_cg[bt].sample(error_mbox_ecc_unc_trig.get_mirrored_value() >> bt);
            foreach(error_wdt_timer1_timeout_trig_bit_cg[bt]) this.error_wdt_timer1_timeout_trig_bit_cg[bt].sample(error_wdt_timer1_timeout_trig.get_mirrored_value() >> bt);
            foreach(error_wdt_timer2_timeout_trig_bit_cg[bt]) this.error_wdt_timer2_timeout_trig_bit_cg[bt].sample(error_wdt_timer2_timeout_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_internal_trig.get_mirrored_value()  ,  error_inv_dev_trig.get_mirrored_value()  ,  error_cmd_fail_trig.get_mirrored_value()  ,  error_bad_fuse_trig.get_mirrored_value()  ,  error_iccm_blocked_trig.get_mirrored_value()  ,  error_mbox_ecc_unc_trig.get_mirrored_value()  ,  error_wdt_timer1_timeout_trig.get_mirrored_value()  ,  error_wdt_timer2_timeout_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__NOTIF_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__notif_intr_trig_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_avail_trig_bit_cg[bt]) this.notif_cmd_avail_trig_bit_cg[bt].sample(data[0 + bt]);
            foreach(notif_mbox_ecc_cor_trig_bit_cg[bt]) this.notif_mbox_ecc_cor_trig_bit_cg[bt].sample(data[1 + bt]);
            foreach(notif_debug_locked_trig_bit_cg[bt]) this.notif_debug_locked_trig_bit_cg[bt].sample(data[2 + bt]);
            foreach(notif_soc_req_lock_trig_bit_cg[bt]) this.notif_soc_req_lock_trig_bit_cg[bt].sample(data[3 + bt]);
            foreach(notif_gen_in_toggle_trig_bit_cg[bt]) this.notif_gen_in_toggle_trig_bit_cg[bt].sample(data[4 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_avail_trig*/  ,  data[1:1]/*notif_mbox_ecc_cor_trig*/  ,  data[2:2]/*notif_debug_locked_trig*/  ,  data[3:3]/*notif_soc_req_lock_trig*/  ,  data[4:4]/*notif_gen_in_toggle_trig*/   );
        end
    endfunction

    function void soc_ifc_reg__intr_block_t__notif_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_avail_trig_bit_cg[bt]) this.notif_cmd_avail_trig_bit_cg[bt].sample(notif_cmd_avail_trig.get_mirrored_value() >> bt);
            foreach(notif_mbox_ecc_cor_trig_bit_cg[bt]) this.notif_mbox_ecc_cor_trig_bit_cg[bt].sample(notif_mbox_ecc_cor_trig.get_mirrored_value() >> bt);
            foreach(notif_debug_locked_trig_bit_cg[bt]) this.notif_debug_locked_trig_bit_cg[bt].sample(notif_debug_locked_trig.get_mirrored_value() >> bt);
            foreach(notif_soc_req_lock_trig_bit_cg[bt]) this.notif_soc_req_lock_trig_bit_cg[bt].sample(notif_soc_req_lock_trig.get_mirrored_value() >> bt);
            foreach(notif_gen_in_toggle_trig_bit_cg[bt]) this.notif_gen_in_toggle_trig_bit_cg[bt].sample(notif_gen_in_toggle_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_avail_trig.get_mirrored_value()  ,  notif_mbox_ecc_cor_trig.get_mirrored_value()  ,  notif_debug_locked_trig.get_mirrored_value()  ,  notif_soc_req_lock_trig.get_mirrored_value()  ,  notif_gen_in_toggle_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_608F1141 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_608f1141::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_608f1141::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_916AB5DF SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_916ab5df::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_916ab5df::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_B2A56031 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_b2a56031::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_b2a56031::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_FB7D2433 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_fb7d2433::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_fb7d2433::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_25E76B6F SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_25e76b6f::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_25e76b6f::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_26B97E39 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_26b97e39::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_26b97e39::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_A2F61F82 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_a2f61f82::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_a2f61f82::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_D46457CD SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_d46457cd::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_d46457cd::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_A06F0954 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_a06f0954::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_a06f0954::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_00E49272 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_00e49272::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_00e49272::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_EE53DED8 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_ee53ded8::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_ee53ded8::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_B9BDDABE SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_b9bddabe::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_b9bddabe::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_57528CC1 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_57528cc1::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_57528cc1::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_15E6ED7E SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_F762EA9C SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_f762ea9c::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_f762ea9c::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_AA8718C6 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_aa8718c6::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_aa8718c6::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_26FA5955 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_26fa5955::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_26fa5955::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_3E43D258 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_3e43d258::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_3e43d258::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_9F1632FD SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_9f1632fd::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_9f1632fd::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_AA999FDC SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_aa999fdc::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_aa999fdc::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_404E12DB SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_404e12db::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_404e12db::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_90D52137 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_90d52137::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_90d52137::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_A6DB6FFF SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_a6db6fff::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_a6db6fff::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_51891FB1 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_51891fb1::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_51891fb1::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_246489BD SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_246489bd::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_246489bd::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_D6ED4D1E SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_d6ed4d1e::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_d6ed4d1e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

`endif