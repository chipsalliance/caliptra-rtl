#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

"""Purpose: Generates a set of covergroups and related signal insantiations for SoC registers""" 






soc_regs_txt = """
    CPTRA_HW_ERROR_FATAL
    CPTRA_HW_ERROR_NON_FATAL
    CPTRA_FW_ERROR_FATAL
    CPTRA_FW_ERROR_NON_FATAL
    CPTRA_HW_ERROR_ENC
    CPTRA_FW_ERROR_ENC
    CPTRA_FW_EXTENDED_ERROR_INFO 8
    CPTRA_BOOT_STATUS
    CPTRA_FLOW_STATUS
    CPTRA_RESET_REASON
    CPTRA_SECURITY_STATE
    CPTRA_MBOX_VALID_AXI_USER 5
    CPTRA_MBOX_AXI_USER_LOCK 5
    CPTRA_TRNG_VALID_AXI_USER
    CPTRA_TRNG_AXI_USER_LOCK
    CPTRA_TRNG_DATA 12
    CPTRA_TRNG_CTRL
    CPTRA_TRNG_STATUS
    CPTRA_FUSE_WR_DONE
    CPTRA_TIMER_CONFIG
    CPTRA_BOOTFSM_GO
    CPTRA_DBG_MANUF_SERVICE_REG
    CPTRA_CLK_GATING_EN
    CPTRA_GENERIC_INPUT_WIRES 2
    CPTRA_GENERIC_OUTPUT_WIRES 2
    CPTRA_HW_REV_ID
    CPTRA_FW_REV_ID 2
    CPTRA_HW_CONFIG
    CPTRA_WDT_TIMER1_EN
    CPTRA_WDT_TIMER1_CTRL
    CPTRA_WDT_TIMER1_TIMEOUT_PERIOD 2
    CPTRA_WDT_TIMER2_EN
    CPTRA_WDT_TIMER2_CTRL
    CPTRA_WDT_TIMER2_TIMEOUT_PERIOD 2
    CPTRA_WDT_STATUS
    CPTRA_FUSE_VALID_AXI_USER
    CPTRA_FUSE_AXI_USER_LOCK
    CPTRA_WDT_CFG 2
    CPTRA_iTRNG_ENTROPY_CONFIG_0
    CPTRA_iTRNG_ENTROPY_CONFIG_1
    CPTRA_RSVD_REG 2
    CPTRA_HW_CAPABILITIES
    CPTRA_FW_CAPABILITIES 
    CPTRA_CAP_LOCK
    CPTRA_OWNER_PK_HASH 12
    CPTRA_OWNER_PK_HASH_LOCK
    fuse_uds_seed 16
    fuse_field_entropy 8
    fuse_vendor_pk_hash 12
    fuse_ecc_revocation
    fuse_fmc_key_manifest_svn
    fuse_runtime_svn 4
    fuse_anti_rollback_disable
    fuse_idevid_cert_attr 24
    fuse_idevid_manuf_hsm_id 4
    fuse_lms_revocation
    fuse_mldsa_revocation
    fuse_soc_stepping_id
    fuse_manuf_dbg_unlock_token 16
    fuse_pqc_key_type
    fuse_soc_manifest_svn 4
    fuse_soc_manifest_max_svn
    fuse_uds_seed 4
    SS_CALIPTRA_BASE_ADDR_L
    SS_CALIPTRA_BASE_ADDR_H
    SS_MCI_BASE_ADDR_L
    SS_MCI_BASE_ADDR_H
    SS_RECOVERY_IFC_BASE_ADDR_L
    SS_RECOVERY_IFC_BASE_ADDR_H
    SS_OTP_FC_BASE_ADDR_L
    SS_OTP_FC_BASE_ADDR_H
    SS_UDS_SEED_BASE_ADDR_L
    SS_UDS_SEED_BASE_ADDR_H
    SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET
    SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES
    SS_DEBUG_INTENT
    SS_CALIPTRA_DMA_AXI_USER
    SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L
    SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H
    SS_KEY_RELEASE_BASE_ADDR_L
    SS_KEY_RELEASE_BASE_ADDR_H
    SS_KEY_RELEASE_SIZE
    SS_OCP_LOCK_CTRL
    SS_STRAP_GENERIC 4
    SS_DBG_SERVICE_REG_REQ
    SS_DBG_SERVICE_REG_RSP
    SS_SOC_DBG_UNLOCK_LEVEL 2
    SS_GENERIC_FW_EXEC_CTRL 4
    internal_obf_key 8
    internal_iccm_lock
    internal_fw_update_reset
    internal_fw_update_reset_wait_cycles
    internal_nmi_vector
    internal_hw_error_fatal_mask
    internal_hw_error_non_fatal_mask
    internal_fw_error_fatal_mask
    internal_fw_error_non_fatal_mask
    internal_rv_mtime_l
    internal_rv_mtime_h
    internal_rv_mtimecmp_l
    internal_rv_mtimecmp_h
    intr_brf_global_intr_en_r
    intr_brf_error_intr_en_r
    intr_brf_notif_intr_en_r
    intr_brf_error_global_intr_r
    intr_brf_notif_global_intr_r
    intr_brf_error_internal_intr_r
    intr_brf_notif_internal_intr_r
    intr_brf_error_intr_trig_r
    intr_brf_notif_intr_trig_r
    intr_brf_error_internal_intr_count_r
    intr_brf_error_inv_dev_intr_count_r
    intr_brf_error_cmd_fail_intr_count_r
    intr_brf_error_bad_fuse_intr_count_r
    intr_brf_error_iccm_blocked_intr_count_r
    intr_brf_error_mbox_ecc_unc_intr_count_r
    intr_brf_error_wdt_timer1_timeout_intr_count_r
    intr_brf_error_wdt_timer2_timeout_intr_count_r
    intr_brf_notif_cmd_avail_intr_count_r
    intr_brf_notif_mbox_ecc_cor_intr_count_r
    intr_brf_notif_debug_locked_intr_count_r
    intr_brf_notif_scan_mode_intr_count_r
    intr_brf_notif_soc_req_lock_intr_count_r
    intr_brf_notif_gen_in_toggle_intr_count_r
    intr_brf_error_internal_intr_count_incr_r
    intr_brf_error_inv_dev_intr_count_incr_r
    intr_brf_error_cmd_fail_intr_count_incr_r
    intr_brf_error_bad_fuse_intr_count_incr_r
    intr_brf_error_iccm_blocked_intr_count_incr_r
    intr_brf_error_mbox_ecc_unc_intr_count_incr_r
    intr_brf_error_wdt_timer1_timeout_intr_count_incr_r
    intr_brf_error_wdt_timer2_timeout_intr_count_incr_r
    intr_brf_notif_cmd_avail_intr_count_incr_r
    intr_brf_notif_mbox_ecc_cor_intr_count_incr_r
    intr_brf_notif_debug_locked_intr_count_incr_r
    intr_brf_notif_scan_mode_intr_count_incr_r
    intr_brf_notif_soc_req_lock_intr_count_incr_r
    intr_brf_notif_gen_in_toggle_intr_count_incr_r
"""
#   sha_acc_intr_brf_global_intr_en_r
#   sha_acc_intr_brf_error_intr_en_r
#   sha_acc_intr_brf_notif_intr_en_r
#   sha_acc_intr_brf_error_global_intr_r
#   sha_acc_intr_brf_notif_global_intr_r
#   sha_acc_intr_brf_error_internal_intr_r
#   sha_acc_intr_brf_notif_internal_intr_r
#   sha_acc_intr_brf_error_intr_trig_r
#   sha_acc_intr_brf_notif_intr_trig_r
#   sha_acc_intr_brf_error0_intr_count_r
#   sha_acc_intr_brf_error1_intr_count_r
#   sha_acc_intr_brf_error2_intr_count_r
#   sha_acc_intr_brf_error3_intr_count_r
#   sha_acc_intr_brf_notif_cmd_done_intr_count_r
#   sha_acc_intr_brf_error0_intr_count_incr_r
#   sha_acc_intr_brf_error1_intr_count_incr_r
#   sha_acc_intr_brf_error2_intr_count_incr_r
#   sha_acc_intr_brf_error3_intr_count_incr_r
#   sha_acc_intr_brf_notif_cmd_done_intr_count_incr_r

commented_regs = set( "CPTRA_SECURITY_STATE CPTRA_HW_REV_ID CPTRA_HW_CONFIG".split())

def main():

    wr_rd_bins_txt = "bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);"
    ignore_bins_txt = "ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};"

    soc_regs = (reg.strip().split() for reg in soc_regs_txt.strip().splitlines())
    soc_regs = [(r[0], int(r[1])) if len(r) == 2 else (r[0], 1) for r in soc_regs] 


    print()
    print ("  // ------------------------------------------------------------------- ")
    print ("  // begin SCRIPT_OUTPUT") 
    print ("  // ------------------------------------------------------------------- \n")

    print (f"\n  // ------------------- COVERGROUP related signals & assigns -------------------\n")


    for rname,width in  soc_regs:
        cb = "  // " if rname in commented_regs else "  "
    
        if rname.startswith("intr_brf_"):    
            tickdef_prefix = rname.replace("intr_brf_","`CLP_SOC_IFC_REG_INTR_BLOCK_RF_").upper()
        elif rname.startswith("sha_acc_intr_brf_"): 
            tickdef_prefix = rname.replace("sha_acc_intr_brf_","`CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_").upper()
        else:
            tickdef_prefix = f"`CLP_SOC_IFC_REG_{rname.upper()}" 

        if width == 1:
            print (f"{cb}logic          hit_{rname};") 
            print (f"{cb}logic [3:0]    bus_{rname};"); 
            # print (f"{cb}logic [31:0]   full_addr_{rname} = `CLP_SOC_IFC_REG_{rname.upper()};\n") 
            print (f"{cb}logic [31:0]   full_addr_{rname} = {tickdef_prefix};\n") 
        else: 
            print (f"{cb}logic          hit_{rname}[0:{width-1}];") 
            print (f"{cb}logic [3:0]    bus_{rname}[0:{width-1}];"); 
            print (f"{cb}logic [31:0]   full_addr_{rname}[0:{width-1}];")
            for i in range(width): 
                # print (f"{cb}assign         full_addr_{rname}[{i}] = `CLP_SOC_IFC_REG_{rname.upper()}_{i};") 
                print (f"{cb}assign         full_addr_{rname}[{i}] = {tickdef_prefix}_{i};") 
            print()
    print()

    for rname,width in  soc_regs:
        cb = "  // " if rname in commented_regs else "  "

        if width == 1:
            print (f"{cb}" + "assign hit_%s = (soc_ifc_reg_req_data.addr == full_addr_%s[AXI_ADDR_WIDTH-1:0]);" % (rname, rname))
            print (f"{cb}" + "assign bus_%s = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_%s}};\n" % (rname, rname))
        else: 
            for i in range(width): 
                print (f"{cb}" + "assign hit_%s[%d] = (soc_ifc_reg_req_data.addr == full_addr_%s[%d][18-1:0]);" % (rname, i, rname, i))
                print (f"{cb}" + "assign bus_%s[%d] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_%s[%d]}};\n" % (rname, i, rname, i))


    for rname,width in  soc_regs:
        cb = "  // " if rname in commented_regs else "  "

        rname_mod = rname
        if rname.startswith("intr_brf_"):    
            rname_mod = rname.replace("intr_brf_","intr_block_rf.")


        #  automatic logic [0:0] next_c = field_storage.intr_block_rf.notif_intr_en_r.notif_soc_req_lock_en.value;

        if width == 1:
            print (f"{cb}// ----------------------- COVERGROUP {rname} -----------------------")
            print (f"{cb}covergroup soc_ifc_{rname}_cg (ref logic [3:0] bus_event) @(posedge clk);")
            print (f"  {cb}{rname}_cp : coverpoint i_soc_ifc_reg.field_storage.{rname_mod};") 
            print (f"  {cb}bus_{rname}_cp : coverpoint bus_event", '{') 
            print (f"    {cb}{wr_rd_bins_txt}") 
            print (f"    {cb}{ignore_bins_txt}")
            print (f"{cb}", ' }')
            print (f"{cb}endgroup\n")
        else:
            print (f"{cb}// ----------------------- COVERGROUP {rname} [0:{width-1}] -----------------------")
            print (f"{cb}covergroup soc_ifc_{rname}_cg (ref logic [3:0] bus_event[0:{width-1}]) @(posedge clk);")
            for i in range(width): 
                print (f"  {cb}{rname}{i}_cp : coverpoint i_soc_ifc_reg.field_storage.{rname_mod}[{i}];") 
                print (f"  {cb}bus_{rname}{i}_cp : coverpoint bus_event[{i}]", '{') 
                print (f"    {cb}{wr_rd_bins_txt}") 
                print (f"    {cb}{ignore_bins_txt}")
                print (f"{cb}", ' }')
            print (f"{cb}endgroup\n")


    print (f"\n  // ----------------------- COVERGROUP Instantiations -----------------------\n")

    for rname,width in  soc_regs:
        cb = "  // " if rname in commented_regs else "  "
       
        print (f"{cb}soc_ifc_{rname}_cg {rname}_cg = new(bus_{rname});")


    print()
    print ("  // ------------------------------------------------------------------- ")
    print ("  // end SCRIPT_OUTPUT") 
    print ("  // ------------------------------------------------------------------- \n")


    print ("endinterface\n")
    print ()
    print ("`endif\n")

if __name__ == '__main__':
    main()

