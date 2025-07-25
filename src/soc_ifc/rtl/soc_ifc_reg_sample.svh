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
            foreach(crypto_err_bit_cg[bt]) this.crypto_err_bit_cg[bt].sample(data[3 + bt]);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(data[4 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*iccm_ecc_unc*/  ,  data[1:1]/*dccm_ecc_unc*/  ,  data[2:2]/*nmi_pin*/  ,  data[3:3]/*crypto_err*/  ,  data[31:4]/*rsvd*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_HW_ERROR_FATAL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(iccm_ecc_unc_bit_cg[bt]) this.iccm_ecc_unc_bit_cg[bt].sample(iccm_ecc_unc.get_mirrored_value() >> bt);
            foreach(dccm_ecc_unc_bit_cg[bt]) this.dccm_ecc_unc_bit_cg[bt].sample(dccm_ecc_unc.get_mirrored_value() >> bt);
            foreach(nmi_pin_bit_cg[bt]) this.nmi_pin_bit_cg[bt].sample(nmi_pin.get_mirrored_value() >> bt);
            foreach(crypto_err_bit_cg[bt]) this.crypto_err_bit_cg[bt].sample(crypto_err.get_mirrored_value() >> bt);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(rsvd.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( iccm_ecc_unc.get_mirrored_value()  ,  dccm_ecc_unc.get_mirrored_value()  ,  nmi_pin.get_mirrored_value()  ,  crypto_err.get_mirrored_value()  ,  rsvd.get_mirrored_value()   );
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
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(data[3 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*mbox_prot_no_lock*/  ,  data[1:1]/*mbox_prot_ooo*/  ,  data[2:2]/*mbox_ecc_unc*/  ,  data[31:3]/*rsvd*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_HW_ERROR_NON_FATAL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mbox_prot_no_lock_bit_cg[bt]) this.mbox_prot_no_lock_bit_cg[bt].sample(mbox_prot_no_lock.get_mirrored_value() >> bt);
            foreach(mbox_prot_ooo_bit_cg[bt]) this.mbox_prot_ooo_bit_cg[bt].sample(mbox_prot_ooo.get_mirrored_value() >> bt);
            foreach(mbox_ecc_unc_bit_cg[bt]) this.mbox_ecc_unc_bit_cg[bt].sample(mbox_ecc_unc.get_mirrored_value() >> bt);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(rsvd.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( mbox_prot_no_lock.get_mirrored_value()  ,  mbox_prot_ooo.get_mirrored_value()  ,  mbox_ecc_unc.get_mirrored_value()  ,  rsvd.get_mirrored_value()   );
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
            foreach(idevid_csr_ready_bit_cg[bt]) this.idevid_csr_ready_bit_cg[bt].sample(data[24 + bt]);
            foreach(boot_fsm_ps_bit_cg[bt]) this.boot_fsm_ps_bit_cg[bt].sample(data[25 + bt]);
            foreach(ready_for_mb_processing_bit_cg[bt]) this.ready_for_mb_processing_bit_cg[bt].sample(data[28 + bt]);
            foreach(ready_for_runtime_bit_cg[bt]) this.ready_for_runtime_bit_cg[bt].sample(data[29 + bt]);
            foreach(ready_for_fuses_bit_cg[bt]) this.ready_for_fuses_bit_cg[bt].sample(data[30 + bt]);
            foreach(mailbox_flow_done_bit_cg[bt]) this.mailbox_flow_done_bit_cg[bt].sample(data[31 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[23:0]/*status*/  ,  data[24:24]/*idevid_csr_ready*/  ,  data[27:25]/*boot_fsm_ps*/  ,  data[28:28]/*ready_for_mb_processing*/  ,  data[29:29]/*ready_for_runtime*/  ,  data[30:30]/*ready_for_fuses*/  ,  data[31:31]/*mailbox_flow_done*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_FLOW_STATUS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(status_bit_cg[bt]) this.status_bit_cg[bt].sample(status.get_mirrored_value() >> bt);
            foreach(idevid_csr_ready_bit_cg[bt]) this.idevid_csr_ready_bit_cg[bt].sample(idevid_csr_ready.get_mirrored_value() >> bt);
            foreach(boot_fsm_ps_bit_cg[bt]) this.boot_fsm_ps_bit_cg[bt].sample(boot_fsm_ps.get_mirrored_value() >> bt);
            foreach(ready_for_mb_processing_bit_cg[bt]) this.ready_for_mb_processing_bit_cg[bt].sample(ready_for_mb_processing.get_mirrored_value() >> bt);
            foreach(ready_for_runtime_bit_cg[bt]) this.ready_for_runtime_bit_cg[bt].sample(ready_for_runtime.get_mirrored_value() >> bt);
            foreach(ready_for_fuses_bit_cg[bt]) this.ready_for_fuses_bit_cg[bt].sample(ready_for_fuses.get_mirrored_value() >> bt);
            foreach(mailbox_flow_done_bit_cg[bt]) this.mailbox_flow_done_bit_cg[bt].sample(mailbox_flow_done.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( status.get_mirrored_value()  ,  idevid_csr_ready.get_mirrored_value()  ,  boot_fsm_ps.get_mirrored_value()  ,  ready_for_mb_processing.get_mirrored_value()  ,  ready_for_runtime.get_mirrored_value()  ,  ready_for_fuses.get_mirrored_value()  ,  mailbox_flow_done.get_mirrored_value()   );
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

    /*----------------------- SOC_IFC_REG__CPTRA_MBOX_VALID_AXI_USER SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_MBOX_VALID_AXI_USER::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(AXI_USER_bit_cg[bt]) this.AXI_USER_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*AXI_USER*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_MBOX_VALID_AXI_USER::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(AXI_USER_bit_cg[bt]) this.AXI_USER_bit_cg[bt].sample(AXI_USER.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( AXI_USER.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_MBOX_AXI_USER_LOCK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_MBOX_AXI_USER_LOCK::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__CPTRA_MBOX_AXI_USER_LOCK::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LOCK_bit_cg[bt]) this.LOCK_bit_cg[bt].sample(LOCK.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( LOCK.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_TRNG_VALID_AXI_USER SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_TRNG_VALID_AXI_USER::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(AXI_USER_bit_cg[bt]) this.AXI_USER_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*AXI_USER*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_TRNG_VALID_AXI_USER::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(AXI_USER_bit_cg[bt]) this.AXI_USER_bit_cg[bt].sample(AXI_USER.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( AXI_USER.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_TRNG_AXI_USER_LOCK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_TRNG_AXI_USER_LOCK::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__CPTRA_TRNG_AXI_USER_LOCK::sample_values();
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

    /*----------------------- SOC_IFC_REG__CPTRA_TRNG_CTRL SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_TRNG_CTRL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(clear_bit_cg[bt]) this.clear_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*clear*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_TRNG_CTRL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(clear_bit_cg[bt]) this.clear_bit_cg[bt].sample(clear.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( clear.get_mirrored_value()   );
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
            foreach(CPTRA_GENERATION_bit_cg[bt]) this.CPTRA_GENERATION_bit_cg[bt].sample(data[0 + bt]);
            foreach(SOC_STEPPING_ID_bit_cg[bt]) this.SOC_STEPPING_ID_bit_cg[bt].sample(data[16 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[15:0]/*CPTRA_GENERATION*/  ,  data[31:16]/*SOC_STEPPING_ID*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_HW_REV_ID::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(CPTRA_GENERATION_bit_cg[bt]) this.CPTRA_GENERATION_bit_cg[bt].sample(CPTRA_GENERATION.get_mirrored_value() >> bt);
            foreach(SOC_STEPPING_ID_bit_cg[bt]) this.SOC_STEPPING_ID_bit_cg[bt].sample(SOC_STEPPING_ID.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( CPTRA_GENERATION.get_mirrored_value()  ,  SOC_STEPPING_ID.get_mirrored_value()   );
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
            foreach(Fuse_Granularity_bit_cg[bt]) this.Fuse_Granularity_bit_cg[bt].sample(data[1 + bt]);
            foreach(RSVD_en_bit_cg[bt]) this.RSVD_en_bit_cg[bt].sample(data[2 + bt]);
            foreach(LMS_acc_en_bit_cg[bt]) this.LMS_acc_en_bit_cg[bt].sample(data[4 + bt]);
            foreach(SUBSYSTEM_MODE_en_bit_cg[bt]) this.SUBSYSTEM_MODE_en_bit_cg[bt].sample(data[5 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*iTRNG_en*/  ,  data[1:1]/*Fuse_Granularity*/  ,  data[3:2]/*RSVD_en*/  ,  data[4:4]/*LMS_acc_en*/  ,  data[5:5]/*SUBSYSTEM_MODE_en*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_HW_CONFIG::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(iTRNG_en_bit_cg[bt]) this.iTRNG_en_bit_cg[bt].sample(iTRNG_en.get_mirrored_value() >> bt);
            foreach(Fuse_Granularity_bit_cg[bt]) this.Fuse_Granularity_bit_cg[bt].sample(Fuse_Granularity.get_mirrored_value() >> bt);
            foreach(RSVD_en_bit_cg[bt]) this.RSVD_en_bit_cg[bt].sample(RSVD_en.get_mirrored_value() >> bt);
            foreach(LMS_acc_en_bit_cg[bt]) this.LMS_acc_en_bit_cg[bt].sample(LMS_acc_en.get_mirrored_value() >> bt);
            foreach(SUBSYSTEM_MODE_en_bit_cg[bt]) this.SUBSYSTEM_MODE_en_bit_cg[bt].sample(SUBSYSTEM_MODE_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( iTRNG_en.get_mirrored_value()  ,  Fuse_Granularity.get_mirrored_value()  ,  RSVD_en.get_mirrored_value()  ,  LMS_acc_en.get_mirrored_value()  ,  SUBSYSTEM_MODE_en.get_mirrored_value()   );
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

    /*----------------------- SOC_IFC_REG__CPTRA_FUSE_VALID_AXI_USER SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_FUSE_VALID_AXI_USER::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(AXI_USER_bit_cg[bt]) this.AXI_USER_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*AXI_USER*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_FUSE_VALID_AXI_USER::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(AXI_USER_bit_cg[bt]) this.AXI_USER_bit_cg[bt].sample(AXI_USER.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( AXI_USER.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_FUSE_AXI_USER_LOCK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_FUSE_AXI_USER_LOCK::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__CPTRA_FUSE_AXI_USER_LOCK::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LOCK_bit_cg[bt]) this.LOCK_bit_cg[bt].sample(LOCK.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( LOCK.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_CFG SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_WDT_CFG::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(TIMEOUT_bit_cg[bt]) this.TIMEOUT_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*TIMEOUT*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_WDT_CFG::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(TIMEOUT_bit_cg[bt]) this.TIMEOUT_bit_cg[bt].sample(TIMEOUT.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( TIMEOUT.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_ITRNG_ENTROPY_CONFIG_0 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_iTRNG_ENTROPY_CONFIG_0::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(low_threshold_bit_cg[bt]) this.low_threshold_bit_cg[bt].sample(data[0 + bt]);
            foreach(high_threshold_bit_cg[bt]) this.high_threshold_bit_cg[bt].sample(data[16 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[15:0]/*low_threshold*/  ,  data[31:16]/*high_threshold*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_iTRNG_ENTROPY_CONFIG_0::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(low_threshold_bit_cg[bt]) this.low_threshold_bit_cg[bt].sample(low_threshold.get_mirrored_value() >> bt);
            foreach(high_threshold_bit_cg[bt]) this.high_threshold_bit_cg[bt].sample(high_threshold.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( low_threshold.get_mirrored_value()  ,  high_threshold.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_ITRNG_ENTROPY_CONFIG_1 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_iTRNG_ENTROPY_CONFIG_1::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(repetition_count_bit_cg[bt]) this.repetition_count_bit_cg[bt].sample(data[0 + bt]);
            foreach(RSVD_bit_cg[bt]) this.RSVD_bit_cg[bt].sample(data[16 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[15:0]/*repetition_count*/  ,  data[31:16]/*RSVD*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_iTRNG_ENTROPY_CONFIG_1::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(repetition_count_bit_cg[bt]) this.repetition_count_bit_cg[bt].sample(repetition_count.get_mirrored_value() >> bt);
            foreach(RSVD_bit_cg[bt]) this.RSVD_bit_cg[bt].sample(RSVD.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( repetition_count.get_mirrored_value()  ,  RSVD.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_RSVD_REG SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_RSVD_REG::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(RSVD_bit_cg[bt]) this.RSVD_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*RSVD*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_RSVD_REG::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(RSVD_bit_cg[bt]) this.RSVD_bit_cg[bt].sample(RSVD.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( RSVD.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_HW_CAPABILITIES SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_HW_CAPABILITIES::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cap_bit_cg[bt]) this.cap_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cap*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_HW_CAPABILITIES::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cap_bit_cg[bt]) this.cap_bit_cg[bt].sample(cap.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cap.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_FW_CAPABILITIES SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_FW_CAPABILITIES::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cap_bit_cg[bt]) this.cap_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cap*/   );
        end
    endfunction

    function void soc_ifc_reg__CPTRA_FW_CAPABILITIES::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cap_bit_cg[bt]) this.cap_bit_cg[bt].sample(cap.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cap.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_CAP_LOCK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_CAP_LOCK::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__CPTRA_CAP_LOCK::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lock_bit_cg[bt]) this.lock_bit_cg[bt].sample(lock.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( lock.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_OWNER_PK_HASH SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_OWNER_PK_HASH::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__CPTRA_OWNER_PK_HASH::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(hash_bit_cg[bt]) this.hash_bit_cg[bt].sample(hash.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( hash.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__CPTRA_OWNER_PK_HASH_LOCK SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__CPTRA_OWNER_PK_HASH_LOCK::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__CPTRA_OWNER_PK_HASH_LOCK::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(lock_bit_cg[bt]) this.lock_bit_cg[bt].sample(lock.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( lock.get_mirrored_value()   );
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

    /*----------------------- SOC_IFC_REG__FUSE_VENDOR_PK_HASH SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_vendor_pk_hash::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__fuse_vendor_pk_hash::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(hash_bit_cg[bt]) this.hash_bit_cg[bt].sample(hash.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( hash.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_ECC_REVOCATION SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_ecc_revocation::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(ecc_revocation_bit_cg[bt]) this.ecc_revocation_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[3:0]/*ecc_revocation*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_ecc_revocation::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(ecc_revocation_bit_cg[bt]) this.ecc_revocation_bit_cg[bt].sample(ecc_revocation.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( ecc_revocation.get_mirrored_value()   );
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

    /*----------------------- SOC_IFC_REG__FUSE_MLDSA_REVOCATION SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_mldsa_revocation::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mldsa_revocation_bit_cg[bt]) this.mldsa_revocation_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[3:0]/*mldsa_revocation*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_mldsa_revocation::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mldsa_revocation_bit_cg[bt]) this.mldsa_revocation_bit_cg[bt].sample(mldsa_revocation.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( mldsa_revocation.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_SOC_STEPPING_ID SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_soc_stepping_id::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(soc_stepping_id_bit_cg[bt]) this.soc_stepping_id_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[15:0]/*soc_stepping_id*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_soc_stepping_id::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(soc_stepping_id_bit_cg[bt]) this.soc_stepping_id_bit_cg[bt].sample(soc_stepping_id.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( soc_stepping_id.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_MANUF_DBG_UNLOCK_TOKEN SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_manuf_dbg_unlock_token::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(token_bit_cg[bt]) this.token_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*token*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_manuf_dbg_unlock_token::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(token_bit_cg[bt]) this.token_bit_cg[bt].sample(token.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( token.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_PQC_KEY_TYPE SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_pqc_key_type::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(key_type_bit_cg[bt]) this.key_type_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[1:0]/*key_type*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_pqc_key_type::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(key_type_bit_cg[bt]) this.key_type_bit_cg[bt].sample(key_type.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( key_type.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_SOC_MANIFEST_SVN SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_soc_manifest_svn::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__fuse_soc_manifest_svn::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(svn_bit_cg[bt]) this.svn_bit_cg[bt].sample(svn.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( svn.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__FUSE_SOC_MANIFEST_MAX_SVN SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__fuse_soc_manifest_max_svn::sample(uvm_reg_data_t  data,
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
            this.fld_cg.sample( data[7:0]/*svn*/   );
        end
    endfunction

    function void soc_ifc_reg__fuse_soc_manifest_max_svn::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(svn_bit_cg[bt]) this.svn_bit_cg[bt].sample(svn.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( svn.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_CALIPTRA_BASE_ADDR_L SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_CALIPTRA_BASE_ADDR_L::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_l*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_CALIPTRA_BASE_ADDR_L::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(addr_l.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_l.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_CALIPTRA_BASE_ADDR_H SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_CALIPTRA_BASE_ADDR_H::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_h*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_CALIPTRA_BASE_ADDR_H::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(addr_h.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_h.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_MCI_BASE_ADDR_L SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_MCI_BASE_ADDR_L::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_l*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_MCI_BASE_ADDR_L::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(addr_l.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_l.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_MCI_BASE_ADDR_H SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_MCI_BASE_ADDR_H::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_h*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_MCI_BASE_ADDR_H::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(addr_h.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_h.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_RECOVERY_IFC_BASE_ADDR_L SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_RECOVERY_IFC_BASE_ADDR_L::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_l*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_RECOVERY_IFC_BASE_ADDR_L::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(addr_l.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_l.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_RECOVERY_IFC_BASE_ADDR_H SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_RECOVERY_IFC_BASE_ADDR_H::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_h*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_RECOVERY_IFC_BASE_ADDR_H::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(addr_h.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_h.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_OTP_FC_BASE_ADDR_L SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_OTP_FC_BASE_ADDR_L::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_l*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_OTP_FC_BASE_ADDR_L::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(addr_l.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_l.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_OTP_FC_BASE_ADDR_H SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_OTP_FC_BASE_ADDR_H::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_h*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_OTP_FC_BASE_ADDR_H::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(addr_h.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_h.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_UDS_SEED_BASE_ADDR_L SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_UDS_SEED_BASE_ADDR_L::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_l*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_UDS_SEED_BASE_ADDR_L::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(addr_l.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_l.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_UDS_SEED_BASE_ADDR_H SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_UDS_SEED_BASE_ADDR_H::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_h*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_UDS_SEED_BASE_ADDR_H::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(addr_h.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_h.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(offset_bit_cg[bt]) this.offset_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*offset*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(offset_bit_cg[bt]) this.offset_bit_cg[bt].sample(offset.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( offset.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(num_bit_cg[bt]) this.num_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*num*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(num_bit_cg[bt]) this.num_bit_cg[bt].sample(num.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( num.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_DEBUG_INTENT SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_DEBUG_INTENT::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(debug_intent_bit_cg[bt]) this.debug_intent_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*debug_intent*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_DEBUG_INTENT::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(debug_intent_bit_cg[bt]) this.debug_intent_bit_cg[bt].sample(debug_intent.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( debug_intent.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_CALIPTRA_DMA_AXI_USER SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_CALIPTRA_DMA_AXI_USER::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__SS_CALIPTRA_DMA_AXI_USER::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(user_bit_cg[bt]) this.user_bit_cg[bt].sample(user.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( user.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_l*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_l_bit_cg[bt]) this.addr_l_bit_cg[bt].sample(addr_l.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_l.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*addr_h*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(addr_h_bit_cg[bt]) this.addr_h_bit_cg[bt].sample(addr_h.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( addr_h.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_STRAP_GENERIC SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_STRAP_GENERIC::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(data_bit_cg[bt]) this.data_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*data*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_STRAP_GENERIC::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(data_bit_cg[bt]) this.data_bit_cg[bt].sample(data.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_DBG_SERVICE_REG_REQ SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_DBG_SERVICE_REG_REQ::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(MANUF_DBG_UNLOCK_REQ_bit_cg[bt]) this.MANUF_DBG_UNLOCK_REQ_bit_cg[bt].sample(data[0 + bt]);
            foreach(PROD_DBG_UNLOCK_REQ_bit_cg[bt]) this.PROD_DBG_UNLOCK_REQ_bit_cg[bt].sample(data[1 + bt]);
            foreach(UDS_PROGRAM_REQ_bit_cg[bt]) this.UDS_PROGRAM_REQ_bit_cg[bt].sample(data[2 + bt]);
            foreach(RSVD_bit_cg[bt]) this.RSVD_bit_cg[bt].sample(data[3 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*MANUF_DBG_UNLOCK_REQ*/  ,  data[1:1]/*PROD_DBG_UNLOCK_REQ*/  ,  data[2:2]/*UDS_PROGRAM_REQ*/  ,  data[31:3]/*RSVD*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_DBG_SERVICE_REG_REQ::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(MANUF_DBG_UNLOCK_REQ_bit_cg[bt]) this.MANUF_DBG_UNLOCK_REQ_bit_cg[bt].sample(MANUF_DBG_UNLOCK_REQ.get_mirrored_value() >> bt);
            foreach(PROD_DBG_UNLOCK_REQ_bit_cg[bt]) this.PROD_DBG_UNLOCK_REQ_bit_cg[bt].sample(PROD_DBG_UNLOCK_REQ.get_mirrored_value() >> bt);
            foreach(UDS_PROGRAM_REQ_bit_cg[bt]) this.UDS_PROGRAM_REQ_bit_cg[bt].sample(UDS_PROGRAM_REQ.get_mirrored_value() >> bt);
            foreach(RSVD_bit_cg[bt]) this.RSVD_bit_cg[bt].sample(RSVD.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( MANUF_DBG_UNLOCK_REQ.get_mirrored_value()  ,  PROD_DBG_UNLOCK_REQ.get_mirrored_value()  ,  UDS_PROGRAM_REQ.get_mirrored_value()  ,  RSVD.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_DBG_SERVICE_REG_RSP SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_DBG_SERVICE_REG_RSP::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(MANUF_DBG_UNLOCK_SUCCESS_bit_cg[bt]) this.MANUF_DBG_UNLOCK_SUCCESS_bit_cg[bt].sample(data[0 + bt]);
            foreach(MANUF_DBG_UNLOCK_FAIL_bit_cg[bt]) this.MANUF_DBG_UNLOCK_FAIL_bit_cg[bt].sample(data[1 + bt]);
            foreach(MANUF_DBG_UNLOCK_IN_PROGRESS_bit_cg[bt]) this.MANUF_DBG_UNLOCK_IN_PROGRESS_bit_cg[bt].sample(data[2 + bt]);
            foreach(PROD_DBG_UNLOCK_SUCCESS_bit_cg[bt]) this.PROD_DBG_UNLOCK_SUCCESS_bit_cg[bt].sample(data[3 + bt]);
            foreach(PROD_DBG_UNLOCK_FAIL_bit_cg[bt]) this.PROD_DBG_UNLOCK_FAIL_bit_cg[bt].sample(data[4 + bt]);
            foreach(PROD_DBG_UNLOCK_IN_PROGRESS_bit_cg[bt]) this.PROD_DBG_UNLOCK_IN_PROGRESS_bit_cg[bt].sample(data[5 + bt]);
            foreach(UDS_PROGRAM_SUCCESS_bit_cg[bt]) this.UDS_PROGRAM_SUCCESS_bit_cg[bt].sample(data[6 + bt]);
            foreach(UDS_PROGRAM_FAIL_bit_cg[bt]) this.UDS_PROGRAM_FAIL_bit_cg[bt].sample(data[7 + bt]);
            foreach(UDS_PROGRAM_IN_PROGRESS_bit_cg[bt]) this.UDS_PROGRAM_IN_PROGRESS_bit_cg[bt].sample(data[8 + bt]);
            foreach(TAP_MAILBOX_AVAILABLE_bit_cg[bt]) this.TAP_MAILBOX_AVAILABLE_bit_cg[bt].sample(data[9 + bt]);
            foreach(RSVD_bit_cg[bt]) this.RSVD_bit_cg[bt].sample(data[10 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*MANUF_DBG_UNLOCK_SUCCESS*/  ,  data[1:1]/*MANUF_DBG_UNLOCK_FAIL*/  ,  data[2:2]/*MANUF_DBG_UNLOCK_IN_PROGRESS*/  ,  data[3:3]/*PROD_DBG_UNLOCK_SUCCESS*/  ,  data[4:4]/*PROD_DBG_UNLOCK_FAIL*/  ,  data[5:5]/*PROD_DBG_UNLOCK_IN_PROGRESS*/  ,  data[6:6]/*UDS_PROGRAM_SUCCESS*/  ,  data[7:7]/*UDS_PROGRAM_FAIL*/  ,  data[8:8]/*UDS_PROGRAM_IN_PROGRESS*/  ,  data[9:9]/*TAP_MAILBOX_AVAILABLE*/  ,  data[31:10]/*RSVD*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_DBG_SERVICE_REG_RSP::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(MANUF_DBG_UNLOCK_SUCCESS_bit_cg[bt]) this.MANUF_DBG_UNLOCK_SUCCESS_bit_cg[bt].sample(MANUF_DBG_UNLOCK_SUCCESS.get_mirrored_value() >> bt);
            foreach(MANUF_DBG_UNLOCK_FAIL_bit_cg[bt]) this.MANUF_DBG_UNLOCK_FAIL_bit_cg[bt].sample(MANUF_DBG_UNLOCK_FAIL.get_mirrored_value() >> bt);
            foreach(MANUF_DBG_UNLOCK_IN_PROGRESS_bit_cg[bt]) this.MANUF_DBG_UNLOCK_IN_PROGRESS_bit_cg[bt].sample(MANUF_DBG_UNLOCK_IN_PROGRESS.get_mirrored_value() >> bt);
            foreach(PROD_DBG_UNLOCK_SUCCESS_bit_cg[bt]) this.PROD_DBG_UNLOCK_SUCCESS_bit_cg[bt].sample(PROD_DBG_UNLOCK_SUCCESS.get_mirrored_value() >> bt);
            foreach(PROD_DBG_UNLOCK_FAIL_bit_cg[bt]) this.PROD_DBG_UNLOCK_FAIL_bit_cg[bt].sample(PROD_DBG_UNLOCK_FAIL.get_mirrored_value() >> bt);
            foreach(PROD_DBG_UNLOCK_IN_PROGRESS_bit_cg[bt]) this.PROD_DBG_UNLOCK_IN_PROGRESS_bit_cg[bt].sample(PROD_DBG_UNLOCK_IN_PROGRESS.get_mirrored_value() >> bt);
            foreach(UDS_PROGRAM_SUCCESS_bit_cg[bt]) this.UDS_PROGRAM_SUCCESS_bit_cg[bt].sample(UDS_PROGRAM_SUCCESS.get_mirrored_value() >> bt);
            foreach(UDS_PROGRAM_FAIL_bit_cg[bt]) this.UDS_PROGRAM_FAIL_bit_cg[bt].sample(UDS_PROGRAM_FAIL.get_mirrored_value() >> bt);
            foreach(UDS_PROGRAM_IN_PROGRESS_bit_cg[bt]) this.UDS_PROGRAM_IN_PROGRESS_bit_cg[bt].sample(UDS_PROGRAM_IN_PROGRESS.get_mirrored_value() >> bt);
            foreach(TAP_MAILBOX_AVAILABLE_bit_cg[bt]) this.TAP_MAILBOX_AVAILABLE_bit_cg[bt].sample(TAP_MAILBOX_AVAILABLE.get_mirrored_value() >> bt);
            foreach(RSVD_bit_cg[bt]) this.RSVD_bit_cg[bt].sample(RSVD.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( MANUF_DBG_UNLOCK_SUCCESS.get_mirrored_value()  ,  MANUF_DBG_UNLOCK_FAIL.get_mirrored_value()  ,  MANUF_DBG_UNLOCK_IN_PROGRESS.get_mirrored_value()  ,  PROD_DBG_UNLOCK_SUCCESS.get_mirrored_value()  ,  PROD_DBG_UNLOCK_FAIL.get_mirrored_value()  ,  PROD_DBG_UNLOCK_IN_PROGRESS.get_mirrored_value()  ,  UDS_PROGRAM_SUCCESS.get_mirrored_value()  ,  UDS_PROGRAM_FAIL.get_mirrored_value()  ,  UDS_PROGRAM_IN_PROGRESS.get_mirrored_value()  ,  TAP_MAILBOX_AVAILABLE.get_mirrored_value()  ,  RSVD.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_SOC_DBG_UNLOCK_LEVEL SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_SOC_DBG_UNLOCK_LEVEL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LEVEL_bit_cg[bt]) this.LEVEL_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*LEVEL*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_SOC_DBG_UNLOCK_LEVEL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(LEVEL_bit_cg[bt]) this.LEVEL_bit_cg[bt].sample(LEVEL.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( LEVEL.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- SOC_IFC_REG__SS_GENERIC_FW_EXEC_CTRL SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__SS_GENERIC_FW_EXEC_CTRL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(go_bit_cg[bt]) this.go_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*go*/   );
        end
    endfunction

    function void soc_ifc_reg__SS_GENERIC_FW_EXEC_CTRL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(go_bit_cg[bt]) this.go_bit_cg[bt].sample(go.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( go.get_mirrored_value()   );
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
            foreach(mask_crypto_err_bit_cg[bt]) this.mask_crypto_err_bit_cg[bt].sample(data[3 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*mask_iccm_ecc_unc*/  ,  data[1:1]/*mask_dccm_ecc_unc*/  ,  data[2:2]/*mask_nmi_pin*/  ,  data[3:3]/*mask_crypto_err*/   );
        end
    endfunction

    function void soc_ifc_reg__internal_hw_error_fatal_mask::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(mask_iccm_ecc_unc_bit_cg[bt]) this.mask_iccm_ecc_unc_bit_cg[bt].sample(mask_iccm_ecc_unc.get_mirrored_value() >> bt);
            foreach(mask_dccm_ecc_unc_bit_cg[bt]) this.mask_dccm_ecc_unc_bit_cg[bt].sample(mask_dccm_ecc_unc.get_mirrored_value() >> bt);
            foreach(mask_nmi_pin_bit_cg[bt]) this.mask_nmi_pin_bit_cg[bt].sample(mask_nmi_pin.get_mirrored_value() >> bt);
            foreach(mask_crypto_err_bit_cg[bt]) this.mask_crypto_err_bit_cg[bt].sample(mask_crypto_err.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( mask_iccm_ecc_unc.get_mirrored_value()  ,  mask_dccm_ecc_unc.get_mirrored_value()  ,  mask_nmi_pin.get_mirrored_value()  ,  mask_crypto_err.get_mirrored_value()   );
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
            foreach(notif_scan_mode_en_bit_cg[bt]) this.notif_scan_mode_en_bit_cg[bt].sample(data[3 + bt]);
            foreach(notif_soc_req_lock_en_bit_cg[bt]) this.notif_soc_req_lock_en_bit_cg[bt].sample(data[4 + bt]);
            foreach(notif_gen_in_toggle_en_bit_cg[bt]) this.notif_gen_in_toggle_en_bit_cg[bt].sample(data[5 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_avail_en*/  ,  data[1:1]/*notif_mbox_ecc_cor_en*/  ,  data[2:2]/*notif_debug_locked_en*/  ,  data[3:3]/*notif_scan_mode_en*/  ,  data[4:4]/*notif_soc_req_lock_en*/  ,  data[5:5]/*notif_gen_in_toggle_en*/   );
        end
    endfunction

    function void soc_ifc_reg__intr_block_t__notif_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_avail_en_bit_cg[bt]) this.notif_cmd_avail_en_bit_cg[bt].sample(notif_cmd_avail_en.get_mirrored_value() >> bt);
            foreach(notif_mbox_ecc_cor_en_bit_cg[bt]) this.notif_mbox_ecc_cor_en_bit_cg[bt].sample(notif_mbox_ecc_cor_en.get_mirrored_value() >> bt);
            foreach(notif_debug_locked_en_bit_cg[bt]) this.notif_debug_locked_en_bit_cg[bt].sample(notif_debug_locked_en.get_mirrored_value() >> bt);
            foreach(notif_scan_mode_en_bit_cg[bt]) this.notif_scan_mode_en_bit_cg[bt].sample(notif_scan_mode_en.get_mirrored_value() >> bt);
            foreach(notif_soc_req_lock_en_bit_cg[bt]) this.notif_soc_req_lock_en_bit_cg[bt].sample(notif_soc_req_lock_en.get_mirrored_value() >> bt);
            foreach(notif_gen_in_toggle_en_bit_cg[bt]) this.notif_gen_in_toggle_en_bit_cg[bt].sample(notif_gen_in_toggle_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_avail_en.get_mirrored_value()  ,  notif_mbox_ecc_cor_en.get_mirrored_value()  ,  notif_debug_locked_en.get_mirrored_value()  ,  notif_scan_mode_en.get_mirrored_value()  ,  notif_soc_req_lock_en.get_mirrored_value()  ,  notif_gen_in_toggle_en.get_mirrored_value()   );
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

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__NOTIF_INTR_T_NOTIF_CMD_AVAIL_STS_1871606B_NOTIF_DEBUG_LOCKED_STS_5F024102_NOTIF_GEN_IN_TOGGLE_STS_59F84B64_NOTIF_MBOX_ECC_COR_STS_5C3D26BB_NOTIF_SCAN_MODE_STS_122F6367_NOTIF_SOC_REQ_LOCK_STS_DEDDDE70 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__notif_intr_t_notif_cmd_avail_sts_1871606b_notif_debug_locked_sts_5f024102_notif_gen_in_toggle_sts_59f84b64_notif_mbox_ecc_cor_sts_5c3d26bb_notif_scan_mode_sts_122f6367_notif_soc_req_lock_sts_deddde70::sample(uvm_reg_data_t  data,
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
            foreach(notif_scan_mode_sts_bit_cg[bt]) this.notif_scan_mode_sts_bit_cg[bt].sample(data[3 + bt]);
            foreach(notif_soc_req_lock_sts_bit_cg[bt]) this.notif_soc_req_lock_sts_bit_cg[bt].sample(data[4 + bt]);
            foreach(notif_gen_in_toggle_sts_bit_cg[bt]) this.notif_gen_in_toggle_sts_bit_cg[bt].sample(data[5 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_avail_sts*/  ,  data[1:1]/*notif_mbox_ecc_cor_sts*/  ,  data[2:2]/*notif_debug_locked_sts*/  ,  data[3:3]/*notif_scan_mode_sts*/  ,  data[4:4]/*notif_soc_req_lock_sts*/  ,  data[5:5]/*notif_gen_in_toggle_sts*/   );
        end
    endfunction

    function void soc_ifc_reg__intr_block_t__notif_intr_t_notif_cmd_avail_sts_1871606b_notif_debug_locked_sts_5f024102_notif_gen_in_toggle_sts_59f84b64_notif_mbox_ecc_cor_sts_5c3d26bb_notif_scan_mode_sts_122f6367_notif_soc_req_lock_sts_deddde70::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_avail_sts_bit_cg[bt]) this.notif_cmd_avail_sts_bit_cg[bt].sample(notif_cmd_avail_sts.get_mirrored_value() >> bt);
            foreach(notif_mbox_ecc_cor_sts_bit_cg[bt]) this.notif_mbox_ecc_cor_sts_bit_cg[bt].sample(notif_mbox_ecc_cor_sts.get_mirrored_value() >> bt);
            foreach(notif_debug_locked_sts_bit_cg[bt]) this.notif_debug_locked_sts_bit_cg[bt].sample(notif_debug_locked_sts.get_mirrored_value() >> bt);
            foreach(notif_scan_mode_sts_bit_cg[bt]) this.notif_scan_mode_sts_bit_cg[bt].sample(notif_scan_mode_sts.get_mirrored_value() >> bt);
            foreach(notif_soc_req_lock_sts_bit_cg[bt]) this.notif_soc_req_lock_sts_bit_cg[bt].sample(notif_soc_req_lock_sts.get_mirrored_value() >> bt);
            foreach(notif_gen_in_toggle_sts_bit_cg[bt]) this.notif_gen_in_toggle_sts_bit_cg[bt].sample(notif_gen_in_toggle_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_avail_sts.get_mirrored_value()  ,  notif_mbox_ecc_cor_sts.get_mirrored_value()  ,  notif_debug_locked_sts.get_mirrored_value()  ,  notif_scan_mode_sts.get_mirrored_value()  ,  notif_soc_req_lock_sts.get_mirrored_value()  ,  notif_gen_in_toggle_sts.get_mirrored_value()   );
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
            foreach(notif_scan_mode_trig_bit_cg[bt]) this.notif_scan_mode_trig_bit_cg[bt].sample(data[3 + bt]);
            foreach(notif_soc_req_lock_trig_bit_cg[bt]) this.notif_soc_req_lock_trig_bit_cg[bt].sample(data[4 + bt]);
            foreach(notif_gen_in_toggle_trig_bit_cg[bt]) this.notif_gen_in_toggle_trig_bit_cg[bt].sample(data[5 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_avail_trig*/  ,  data[1:1]/*notif_mbox_ecc_cor_trig*/  ,  data[2:2]/*notif_debug_locked_trig*/  ,  data[3:3]/*notif_scan_mode_trig*/  ,  data[4:4]/*notif_soc_req_lock_trig*/  ,  data[5:5]/*notif_gen_in_toggle_trig*/   );
        end
    endfunction

    function void soc_ifc_reg__intr_block_t__notif_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_avail_trig_bit_cg[bt]) this.notif_cmd_avail_trig_bit_cg[bt].sample(notif_cmd_avail_trig.get_mirrored_value() >> bt);
            foreach(notif_mbox_ecc_cor_trig_bit_cg[bt]) this.notif_mbox_ecc_cor_trig_bit_cg[bt].sample(notif_mbox_ecc_cor_trig.get_mirrored_value() >> bt);
            foreach(notif_debug_locked_trig_bit_cg[bt]) this.notif_debug_locked_trig_bit_cg[bt].sample(notif_debug_locked_trig.get_mirrored_value() >> bt);
            foreach(notif_scan_mode_trig_bit_cg[bt]) this.notif_scan_mode_trig_bit_cg[bt].sample(notif_scan_mode_trig.get_mirrored_value() >> bt);
            foreach(notif_soc_req_lock_trig_bit_cg[bt]) this.notif_soc_req_lock_trig_bit_cg[bt].sample(notif_soc_req_lock_trig.get_mirrored_value() >> bt);
            foreach(notif_gen_in_toggle_trig_bit_cg[bt]) this.notif_gen_in_toggle_trig_bit_cg[bt].sample(notif_gen_in_toggle_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_avail_trig.get_mirrored_value()  ,  notif_mbox_ecc_cor_trig.get_mirrored_value()  ,  notif_debug_locked_trig.get_mirrored_value()  ,  notif_scan_mode_trig.get_mirrored_value()  ,  notif_soc_req_lock_trig.get_mirrored_value()  ,  notif_gen_in_toggle_trig.get_mirrored_value()   );
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

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_FBF3C714 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_fbf3c714::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_t_cnt_fbf3c714::sample_values();
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

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_F5D8AFE0 SAMPLE FUNCTIONS -----------------------*/
    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_f5d8afe0::sample(uvm_reg_data_t  data,
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

    function void soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_f5d8afe0::sample_values();
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
