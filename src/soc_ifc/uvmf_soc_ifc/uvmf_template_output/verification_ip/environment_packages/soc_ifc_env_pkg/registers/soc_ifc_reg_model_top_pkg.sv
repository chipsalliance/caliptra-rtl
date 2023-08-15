//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
// Placeholder for complete register model.  This placeholder allows
//  compilation of generated environment without modification.
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

package soc_ifc_reg_model_top_pkg;

   import uvm_pkg::*;
// pragma uvmf custom additional_imports begin
    import soc_ifc_reg_uvm::*;
    import mbox_csr_uvm::*;
    import sha512_acc_csr_uvm::*;
    import soc_ifc_pkg::*;
    import mgc_apb3_v1_0_pkg::*; /* for apb3_host_apb3_transaction definition */
    import qvip_apb5_slave_params_pkg::*;
    import qvip_apb5_slave_pkg::*; /* for reg adapter definition used in callbacks */

    typedef apb3_host_apb3_transaction #(apb5_master_0_params::APB3_SLAVE_COUNT,
                                         apb5_master_0_params::APB3_PADDR_BIT_WIDTH,
                                         apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,
                                         apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_reg_transfer_t;

    typedef caliptra_reg2apb_adapter #(apb_reg_transfer_t,
                              apb5_master_0_params::APB3_SLAVE_COUNT,
                              apb5_master_0_params::APB3_PADDR_BIT_WIDTH,
                              apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,
                              apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_reg_adapter_t;

    typedef struct packed {
        bit boot_idle;
        bit boot_fuse;
        bit boot_fw_rst;
        bit boot_wait;
        bit boot_done;
    } boot_fn_state_s;

    typedef struct packed {
        bit mbox_idle;
        bit uc_cmd_stage;
        bit uc_dlen_stage;
        bit uc_data_stage;
        bit uc_receive_stage;
        bit uc_done_stage;
        bit soc_cmd_stage;
        bit soc_dlen_stage;
        bit soc_data_stage;
        bit soc_receive_stage;
        bit soc_done_stage;
        bit mbox_error;
    } mbox_fn_state_s;

// pragma uvmf custom additional_imports end

   `include "uvm_macros.svh"

   /* DEFINE REGISTER CLASSES */
// pragma uvmf custom define_register_classes begin

    // These macros are used to copy the "HARD" reset value to a new reset type, "NONCORE",
    // and then track the configuration of the provided register.
    // When called, these macros expect that a queue has already been created called "blk_flds".
    // The queue tracks all extant registers within the enclosing uvm_reg_block.
    // This macro removes from that queue the uvm_reg_field that was provided as an arguement.
    // This allows the calling context to check that the queue of blk_flds is empty at the end,
    // and thus enforce that a custom reset configuration is defined for all register fields.
    `define FLD_DO_CP_NONCORE_RST(fld_h) begin                   \
        if (fld_h.has_reset("HARD"))                             \
            fld_h.set_reset(fld_h.get_reset("HARD"), "NONCORE"); \
    end
    `define REG____CP_NONCORE_RST(reg_h) begin                                 \
        uvm_reg_field reg_flds[$];                                             \
        reg_h.get_fields(reg_flds);                                            \
        foreach (reg_flds[ii]) begin                                           \
            int del_idx[$];                                                    \
            `FLD_DO_CP_NONCORE_RST(reg_flds[ii])                               \
            del_idx = blk_flds.find_first_index(fl) with (fl == reg_flds[ii]); \
            blk_flds.delete(del_idx.pop_front());                              \
        end                                                                    \
    end
    `define REG_NO_CP_NONCORE_RST(reg_h) begin                                 \
        uvm_reg_field reg_flds[$];                                             \
        reg_h.get_fields(reg_flds);                                            \
        foreach (reg_flds[ii]) begin                                           \
            int del_idx[$];                                                    \
            del_idx = blk_flds.find_first_index(fl) with (fl == reg_flds[ii]); \
            blk_flds.delete(del_idx.pop_front());                              \
        end                                                                    \
    end
    `define FLD____CP_NONCORE_RST(fld_h) begin                              \
        int del_idx[$];                                                     \
        `FLD_DO_CP_NONCORE_RST(fld_h)                                       \
        del_idx = blk_flds.find_first_index(fl) with (fl == fld_h);         \
        blk_flds.delete(del_idx.pop_front());                               \
    end
    `define FLD_NO_CP_NONCORE_RST(fld_h) begin                              \
        int del_idx[$];                                                     \
        del_idx = blk_flds.find_first_index(fl) with (fl == fld_h);         \
        blk_flds.delete(del_idx.pop_front());                               \
    end
    // ------------------ END of reset config macros ------------------ //

    class soc_ifc_reg__intr_block_t_ext extends soc_ifc_reg__intr_block_t;
        uvm_reg_map soc_ifc_reg_intr_AHB_map;
        uvm_reg_map soc_ifc_reg_intr_APB_map;

        // HWSET has precedence over SW W1C, so use these variables to track
        // active hwset activity in case contention must be resolved
        bit [31:0] notif_internal_intr_r_hwset_active = 0;
        bit [31:0] error_internal_intr_r_hwset_active = 0;

        function new(string name = "soc_ifc_reg__intr_block_t_ext");
            super.new(name);
        endfunction : new

        // FIXME Manually maintaining a list here of registers that are configured
        //       as soft-resettable (i.e. cptra_rst_b instead of cptra_pwrgood)
        //       or noncore-resettable (i.e. cptra_noncore_rst_b instead of cptra_pwrgood)
        //       Ideally would be auto-generated.
        virtual function void configure_reset_values();
            // Track reset configuration against a queue of all registers in this block, to ensure each register is handled
            uvm_reg_field blk_flds[$];
            get_fields(blk_flds, UVM_NO_HIER);
            `REG____CP_NONCORE_RST(this.global_intr_en_r                           )
            `REG____CP_NONCORE_RST(this.error_intr_en_r                            )
            `REG____CP_NONCORE_RST(this.notif_intr_en_r                            )
            `REG____CP_NONCORE_RST(this.error_global_intr_r                        )
            `REG____CP_NONCORE_RST(this.notif_global_intr_r                        )
            `REG_NO_CP_NONCORE_RST(this.error_internal_intr_r                      )
            `REG____CP_NONCORE_RST(this.notif_internal_intr_r                      )
            `REG____CP_NONCORE_RST(this.error_intr_trig_r                          )
            `REG____CP_NONCORE_RST(this.notif_intr_trig_r                          )
            `REG_NO_CP_NONCORE_RST(this.error_internal_intr_count_r                )
            `REG_NO_CP_NONCORE_RST(this.error_inv_dev_intr_count_r                 )
            `REG_NO_CP_NONCORE_RST(this.error_cmd_fail_intr_count_r                )
            `REG_NO_CP_NONCORE_RST(this.error_bad_fuse_intr_count_r                )
            `REG_NO_CP_NONCORE_RST(this.error_iccm_blocked_intr_count_r            )
            `REG_NO_CP_NONCORE_RST(this.error_mbox_ecc_unc_intr_count_r            )
            `REG_NO_CP_NONCORE_RST(this.error_wdt_timer1_timeout_intr_count_r      )
            `REG_NO_CP_NONCORE_RST(this.error_wdt_timer2_timeout_intr_count_r      )
            `REG____CP_NONCORE_RST(this.notif_cmd_avail_intr_count_r               )
            `REG____CP_NONCORE_RST(this.notif_mbox_ecc_cor_intr_count_r            )
            `REG____CP_NONCORE_RST(this.notif_debug_locked_intr_count_r            )
            `REG____CP_NONCORE_RST(this.notif_scan_mode_intr_count_r               )
            `REG____CP_NONCORE_RST(this.notif_soc_req_lock_intr_count_r            )
            `REG____CP_NONCORE_RST(this.notif_gen_in_toggle_intr_count_r           )
            `REG____CP_NONCORE_RST(this.error_internal_intr_count_incr_r           )
            `REG____CP_NONCORE_RST(this.error_inv_dev_intr_count_incr_r            )
            `REG____CP_NONCORE_RST(this.error_cmd_fail_intr_count_incr_r           )
            `REG____CP_NONCORE_RST(this.error_bad_fuse_intr_count_incr_r           )
            `REG____CP_NONCORE_RST(this.error_iccm_blocked_intr_count_incr_r       )
            `REG____CP_NONCORE_RST(this.error_mbox_ecc_unc_intr_count_incr_r       )
            `REG____CP_NONCORE_RST(this.error_wdt_timer1_timeout_intr_count_incr_r )
            `REG____CP_NONCORE_RST(this.error_wdt_timer2_timeout_intr_count_incr_r )
            `REG____CP_NONCORE_RST(this.notif_cmd_avail_intr_count_incr_r          )
            `REG____CP_NONCORE_RST(this.notif_mbox_ecc_cor_intr_count_incr_r       )
            `REG____CP_NONCORE_RST(this.notif_debug_locked_intr_count_incr_r       )
            `REG____CP_NONCORE_RST(this.notif_scan_mode_intr_count_incr_r          )
            `REG____CP_NONCORE_RST(this.notif_soc_req_lock_intr_count_incr_r       )
            `REG____CP_NONCORE_RST(this.notif_gen_in_toggle_intr_count_incr_r      )
            while (blk_flds.size() != 0) begin
                uvm_reg_field cur_fld = blk_flds.pop_front();
                `uvm_error("SOC_IFC_REG__INTR_BLOCK_T_EXT", {"No extended reset configuration defined for ", cur_fld.get_full_name()})
            end
        endfunction

        virtual function void build();
            super.build();
            this.configure_reset_values();
            this.soc_ifc_reg_intr_AHB_map = create_map("intr_AHB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
            this.soc_ifc_reg_intr_APB_map = create_map("intr_APB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
        endfunction

        virtual function void build_ext_maps();
            uvm_reg regs[$];

            this.default_map.get_registers(regs, UVM_NO_HIER);
            foreach(regs[c_reg]) begin
                this.soc_ifc_reg_intr_AHB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
                this.soc_ifc_reg_intr_APB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
            end
        endfunction

    endclass : soc_ifc_reg__intr_block_t_ext

    class soc_ifc_reg_ext extends soc_ifc_reg;
        // default_map_ext has intr_block_rf_ext.default_map as a submap; the
        // native this.default_map adds intr_block_rf.default_map as submap
        // We need this additional map so that the new intr_block_rf_ext can be
        // initialized, and the default_map assigned to a parent. This allows
        // get_offset methods to work on member registers, so we can then add
        // them to the AHB/APB maps
        uvm_reg_map default_map_ext;
        uvm_reg_map soc_ifc_reg_AHB_map;
        uvm_reg_map soc_ifc_reg_APB_map;

        // This coexists with intr_block_rf (from the parent class), but
        // intr_block_rf is only added as a submap to default_map and
        // should never be used in practice
        rand soc_ifc_reg__intr_block_t_ext intr_block_rf_ext;

        // Tracks functional state of Boot FSM internally, without reference to
        // the value read from CPTRA_FLOW_STATUS
        boot_fn_state_s boot_fn_state_sigs;

        extern virtual function void reset(string kind = "HARD");
        function new(string name = "soc_ifc_reg_ext");
            super.new(name);
            boot_fn_state_sigs = '{boot_idle: 1'b1, default: 1'b0};
        endfunction : new

        // FIXME Manually maintaining a list here of registers that are configured
        //       as soft-resettable (i.e. cptra_rst_b instead of cptra_pwrgood)
        //       or noncore-resettable (i.e. cptra_noncore_rst_b instead of cptra_pwrgood)
        //       Ideally would be auto-generated.
        virtual function void configure_reset_values();
            // Track reset configuration against a queue of all fields in this block, to ensure each register is handled
            uvm_reg_field blk_flds[$];
            get_fields(blk_flds, UVM_NO_HIER);
                                                              `REG_NO_CP_NONCORE_RST(this.CPTRA_HW_ERROR_FATAL                 )
                                                              `REG_NO_CP_NONCORE_RST(this.CPTRA_HW_ERROR_NON_FATAL             )
                                                              `REG_NO_CP_NONCORE_RST(this.CPTRA_FW_ERROR_FATAL                 )
                                                              `REG_NO_CP_NONCORE_RST(this.CPTRA_FW_ERROR_NON_FATAL             )
                                                              `REG_NO_CP_NONCORE_RST(this.CPTRA_HW_ERROR_ENC                   )
                                                              `REG_NO_CP_NONCORE_RST(this.CPTRA_FW_ERROR_ENC                   )
            foreach(this.CPTRA_FW_EXTENDED_ERROR_INFO[ii])    `REG_NO_CP_NONCORE_RST(this.CPTRA_FW_EXTENDED_ERROR_INFO[ii]     )
                                                              `REG____CP_NONCORE_RST(this.CPTRA_BOOT_STATUS                    )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_FLOW_STATUS.status             )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_FLOW_STATUS.idevid_csr_ready   )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_FLOW_STATUS.boot_fsm_ps        )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_FLOW_STATUS.ready_for_fw       )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_FLOW_STATUS.ready_for_runtime  )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_FLOW_STATUS.ready_for_fuses    )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_FLOW_STATUS.mailbox_flow_done  )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_RESET_REASON.FW_UPD_RESET      )
                                                              `FLD_NO_CP_NONCORE_RST(this.CPTRA_RESET_REASON.WARM_RESET        )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_SECURITY_STATE.device_lifecycle)
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_SECURITY_STATE.debug_locked    )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_SECURITY_STATE.scan_mode       )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_SECURITY_STATE.rsvd            )
            foreach(this.CPTRA_MBOX_VALID_PAUSER[ii])         `REG____CP_NONCORE_RST(this.CPTRA_MBOX_VALID_PAUSER[ii]          )
            foreach(this.CPTRA_MBOX_PAUSER_LOCK[ii])          `REG____CP_NONCORE_RST(this.CPTRA_MBOX_PAUSER_LOCK[ii]           )
                                                              `REG____CP_NONCORE_RST(this.CPTRA_TRNG_VALID_PAUSER              )
                                                              `REG____CP_NONCORE_RST(this.CPTRA_TRNG_PAUSER_LOCK               )
            foreach(this.CPTRA_TRNG_DATA[ii])                 `REG____CP_NONCORE_RST(this.CPTRA_TRNG_DATA[ii]                  )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_TRNG_CTRL.clear                )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_TRNG_STATUS.DATA_REQ           )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_TRNG_STATUS.DATA_WR_DONE       )
                                                              `REG_NO_CP_NONCORE_RST(this.CPTRA_FUSE_WR_DONE                   )
                                                              `REG_NO_CP_NONCORE_RST(this.CPTRA_TIMER_CONFIG                   )
                                                              `REG____CP_NONCORE_RST(this.CPTRA_BOOTFSM_GO                     )
                                                              `REG____CP_NONCORE_RST(this.CPTRA_DBG_MANUF_SERVICE_REG          )
                                                              `REG____CP_NONCORE_RST(this.CPTRA_CLK_GATING_EN                  )
            foreach(this.CPTRA_GENERIC_INPUT_WIRES[ii])       `REG____CP_NONCORE_RST(this.CPTRA_GENERIC_INPUT_WIRES[ii]        )
            foreach(this.CPTRA_GENERIC_OUTPUT_WIRES[ii])      `REG____CP_NONCORE_RST(this.CPTRA_GENERIC_OUTPUT_WIRES[ii]       )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_HW_REV_ID.CPTRA_GENERATION     )
                                                              `FLD____CP_NONCORE_RST(this.CPTRA_HW_REV_ID.SOC_STEPPING_ID      )
            foreach(this.CPTRA_FW_REV_ID[ii])                 `REG____CP_NONCORE_RST(this.CPTRA_FW_REV_ID[ii]                  )
                                                              `REG____CP_NONCORE_RST(this.CPTRA_HW_CONFIG                      )
                                                              `REG____CP_NONCORE_RST(this.CPTRA_WDT_TIMER1_EN                  )
                                                              `REG____CP_NONCORE_RST(this.CPTRA_WDT_TIMER1_CTRL                )
            foreach(this.CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[ii]) `REG____CP_NONCORE_RST(this.CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[ii]  )
                                                              `REG____CP_NONCORE_RST(this.CPTRA_WDT_TIMER2_EN                  )
                                                              `REG____CP_NONCORE_RST(this.CPTRA_WDT_TIMER2_CTRL                )
            foreach(this.CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[ii]) `REG____CP_NONCORE_RST(this.CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[ii]  )
                                                              `REG____CP_NONCORE_RST(this.CPTRA_WDT_STATUS                     )
                                                              `REG_NO_CP_NONCORE_RST(this.CPTRA_FUSE_VALID_PAUSER              )
                                                              `REG_NO_CP_NONCORE_RST(this.CPTRA_FUSE_PAUSER_LOCK               )
            foreach(this.CPTRA_WDT_CFG[ii])                   `REG_NO_CP_NONCORE_RST(this.CPTRA_WDT_CFG[ii]                    )
            foreach(this.CPTRA_RSVD_REG[ii])                  `REG_NO_CP_NONCORE_RST(this.CPTRA_RSVD_REG[ii]                   )
            foreach(this.fuse_uds_seed[ii])                   `REG_NO_CP_NONCORE_RST(this.fuse_uds_seed[ii]                    )
            foreach(this.fuse_field_entropy[ii])              `REG_NO_CP_NONCORE_RST(this.fuse_field_entropy[ii]               )
            foreach(this.fuse_key_manifest_pk_hash[ii])       `REG_NO_CP_NONCORE_RST(this.fuse_key_manifest_pk_hash[ii]        )
                                                              `REG_NO_CP_NONCORE_RST(this.fuse_key_manifest_pk_hash_mask       )
            foreach(this.fuse_owner_pk_hash[ii])              `REG_NO_CP_NONCORE_RST(this.fuse_owner_pk_hash[ii]               )
                                                              `REG_NO_CP_NONCORE_RST(this.fuse_fmc_key_manifest_svn            )
            foreach(this.fuse_runtime_svn[ii])                `REG_NO_CP_NONCORE_RST(this.fuse_runtime_svn[ii]                 )
                                                              `REG_NO_CP_NONCORE_RST(this.fuse_anti_rollback_disable           )
            foreach(this.fuse_idevid_cert_attr[ii])           `REG_NO_CP_NONCORE_RST(this.fuse_idevid_cert_attr[ii]            )
            foreach(this.fuse_idevid_manuf_hsm_id[ii])        `REG_NO_CP_NONCORE_RST(this.fuse_idevid_manuf_hsm_id[ii]         )
                                                              `REG_NO_CP_NONCORE_RST(this.fuse_life_cycle                      )
                                                              `REG_NO_CP_NONCORE_RST(this.fuse_lms_verify                      )
                                                              `REG_NO_CP_NONCORE_RST(this.fuse_lms_revocation                  )
                                                              `REG_NO_CP_NONCORE_RST(this.fuse_soc_stepping_id                 )
            foreach(this.internal_obf_key[ii])                `REG_NO_CP_NONCORE_RST(this.internal_obf_key[ii]                 )
                                                              `REG____CP_NONCORE_RST(this.internal_iccm_lock                   )/* TODO also FW reset */
                                                              `REG____CP_NONCORE_RST(this.internal_fw_update_reset             )
                                                              `REG____CP_NONCORE_RST(this.internal_fw_update_reset_wait_cycles )
                                                              `REG____CP_NONCORE_RST(this.internal_nmi_vector                  )
                                                              `REG____CP_NONCORE_RST(this.internal_hw_error_fatal_mask         )
                                                              `REG____CP_NONCORE_RST(this.internal_hw_error_non_fatal_mask     )
                                                              `REG____CP_NONCORE_RST(this.internal_fw_error_fatal_mask         )
                                                              `REG____CP_NONCORE_RST(this.internal_fw_error_non_fatal_mask     )
                                                              `REG_NO_CP_NONCORE_RST(this.internal_rv_mtime_l                  )
                                                              `REG_NO_CP_NONCORE_RST(this.internal_rv_mtime_h                  )
                                                              `REG_NO_CP_NONCORE_RST(this.internal_rv_mtimecmp_l               )
                                                              `REG_NO_CP_NONCORE_RST(this.internal_rv_mtimecmp_h               )
            while (blk_flds.size() != 0) begin
                uvm_reg_field cur_fld = blk_flds.pop_front();
                `uvm_error("SOC_IFC_REG_EXT", {"No extended reset configuration defined for ", cur_fld.get_full_name()})
            end
        endfunction

        virtual function void build();
            super.build();
            this.configure_reset_values();
            this.intr_block_rf_ext = new("intr_block_rf_ext");
            this.intr_block_rf_ext.configure(this);
            this.intr_block_rf_ext.build(); // This configures the default_map, which is used to find reg offsets for other maps
            this.default_map_ext     = create_map("default_map_ext", 0, 4, UVM_LITTLE_ENDIAN);
            this.soc_ifc_reg_AHB_map = create_map("AHB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
            this.soc_ifc_reg_APB_map = create_map("APB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
        endfunction

        virtual function void build_ext_maps();
            uvm_reg        regs[$];
            uvm_reg_map    submaps[$];
            uvm_reg_addr_t intr_block_offset;

            this.default_map.get_registers(regs,    UVM_NO_HIER);
            this.default_map.get_submaps  (submaps, UVM_NO_HIER); // <-- these submaps are from this.intr_block_rf.default_map, per the inherited build() method

            foreach(regs[c_reg]) begin
                this.default_map_ext    .add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
                this.soc_ifc_reg_AHB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
                this.soc_ifc_reg_APB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
            end
            // Find offset used to add intr_block_rf.default_map to this.default_map, so we can
            // use the same offset to add submaps to intr_block_rf_ext
            foreach(submaps[c_submap]) begin
                if (submaps[c_submap].get_name() == "reg_map") begin
                    intr_block_offset = this.default_map.get_submap_offset(submaps[c_submap]);
                end
            end

            this.default_map_ext    .add_submap(this.intr_block_rf_ext.default_map, intr_block_offset);
            this.intr_block_rf_ext.build_ext_maps(); // This configures the AHB/APB maps
            this.soc_ifc_reg_AHB_map.add_submap(this.intr_block_rf_ext.soc_ifc_reg_intr_AHB_map, intr_block_offset);
            this.soc_ifc_reg_APB_map.add_submap(this.intr_block_rf_ext.soc_ifc_reg_intr_APB_map, intr_block_offset);

        endfunction

    endclass : soc_ifc_reg_ext

    function void soc_ifc_reg_ext::reset(string kind = "HARD");
        super.reset(kind);
        // BOOT FSM State Changes
        // "NONCORE" does not cause a state change - it results FROM state changes
        // TODO what to do for FW update?
        if (kind inside {"HARD", "SOFT"}) begin
            boot_fn_state_sigs = '{boot_idle: 1'b1, default: 1'b0};
        end
    endfunction

    class mbox_csr_ext extends mbox_csr;
        uvm_reg_map mbox_csr_AHB_map;
        uvm_reg_map mbox_csr_APB_map;

        uvm_event mbox_lock_clr_miss;
        uvm_event mbox_datain_to_dataout_predict;

        // This tracks expected functionality of the mailbox in a way that is
        // agnostic to the internal state machine implementation and strictly
        // observes the mailbox specification. This is what a more rigorous
        // verification approach should look like.
        // These are used in soc_ifc_predictor to perform calculations of
        // valid_requester/valid_receiver
        mbox_fn_state_s mbox_fn_state_sigs;

        uvm_reg_data_t mbox_data_q [$];
        uvm_reg_data_t mbox_resp_q [$];

        extern virtual function void reset(string kind = "HARD");
        function new(string name = "mbox_csr_ext");
            super.new(name);
            mbox_fn_state_sigs = '{mbox_idle: 1'b1, default: 1'b0};
            mbox_lock_clr_miss = new("mbox_lock_clr_miss");
            mbox_datain_to_dataout_predict = new("mbox_datain_to_dataout_predict");
        endfunction : new

        // FIXME Manually maintaining a list here of registers that are configured
        //       as soft-resettable (i.e. cptra_rst_b instead of cptra_pwrgood)
        //       or noncore-resettable (i.e. cptra_noncore_rst_b instead of cptra_pwrgood)
        //       Ideally would be auto-generated.
        virtual function void configure_reset_values();
            // Track reset configuration against a queue of all registers in this block, to ensure each register is handled
            uvm_reg_field blk_flds[$];
            get_fields(blk_flds, UVM_NO_HIER);
            `REG____CP_NONCORE_RST(this.mbox_lock   )
            `REG____CP_NONCORE_RST(this.mbox_user   )
            `REG____CP_NONCORE_RST(this.mbox_cmd    )
            `REG____CP_NONCORE_RST(this.mbox_dlen   )
            `REG____CP_NONCORE_RST(this.mbox_datain )
            `REG____CP_NONCORE_RST(this.mbox_dataout)
            `REG____CP_NONCORE_RST(this.mbox_execute)
            `REG____CP_NONCORE_RST(this.mbox_status )
            `REG____CP_NONCORE_RST(this.mbox_unlock )
            while (blk_flds.size() != 0) begin
                uvm_reg_field cur_fld = blk_flds.pop_front();
                `uvm_error("MBOX_CSR_EXT", {"No extended reset configuration defined for ", cur_fld.get_full_name()})
            end
        endfunction

        virtual function void build();
            super.build();
            this.configure_reset_values();
            this.mbox_csr_AHB_map = create_map("AHB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
            this.mbox_csr_APB_map = create_map("APB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
        endfunction

        virtual function void build_ext_maps();
            uvm_reg        regs[$];

            this.default_map.get_registers(regs, UVM_NO_HIER);

            foreach(regs[c_reg]) begin
                this.mbox_csr_AHB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
                this.mbox_csr_APB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
            end

        endfunction

    endclass : mbox_csr_ext

    function void mbox_csr_ext::reset(string kind = "HARD");
        super.reset(kind);
        // "SOFT" reset doesn't impact mbox registers until it propagates to the NONCORE reset.
        // Since there's a delay, wait until the NONCORE reset is called to clobber data queues and
        // reg model internal semaphores
        if (kind inside {"HARD", "NONCORE"}) begin
            mbox_data_q.delete();
            mbox_resp_q.delete();
            mbox_lock_clr_miss.reset();
            mbox_datain_to_dataout_predict.reset();

            // Mailbox State Changes
            // TODO what to do for FW update?
            mbox_fn_state_sigs = '{mbox_idle: 1'b1, default: 1'b0};
        end

    endfunction

    class sha512_acc_csr__intr_block_t_ext extends sha512_acc_csr__intr_block_t;
        uvm_reg_map sha512_acc_csr_intr_AHB_map;
        uvm_reg_map sha512_acc_csr_intr_APB_map;

        // HWSET has precedence over SW W1C, so use these variables to track
        // active hwset activity in case contention must be resolved
        bit [31:0] notif_internal_intr_r_hwset_active = 0;
        bit [31:0] error_internal_intr_r_hwset_active = 0;

        function new(string name = "sha512_acc_csr__intr_block_t_ext");
            super.new(name);
        endfunction : new

        // FIXME Manually maintaining a list here of registers that are configured
        //       as soft-resettable (i.e. cptra_rst_b instead of cptra_pwrgood)
        //       or noncore-resettable (i.e. cptra_noncore_rst_b instead of cptra_pwrgood)
        //       Ideally would be auto-generated.
        virtual function void configure_reset_values();
            // Track reset configuration against a queue of all registers in this block, to ensure each register is handled
            uvm_reg_field blk_flds[$];
            get_fields(blk_flds, UVM_NO_HIER);
            `REG____CP_NONCORE_RST(this.global_intr_en_r                 )
            `REG____CP_NONCORE_RST(this.error_intr_en_r                  )
            `REG____CP_NONCORE_RST(this.notif_intr_en_r                  )
            `REG____CP_NONCORE_RST(this.error_global_intr_r              )
            `REG____CP_NONCORE_RST(this.notif_global_intr_r              )
            `REG_NO_CP_NONCORE_RST(this.error_internal_intr_r            )
            `REG____CP_NONCORE_RST(this.notif_internal_intr_r            )
            `REG____CP_NONCORE_RST(this.error_intr_trig_r                )
            `REG____CP_NONCORE_RST(this.notif_intr_trig_r                )
            `REG_NO_CP_NONCORE_RST(this.error0_intr_count_r              )
            `REG_NO_CP_NONCORE_RST(this.error1_intr_count_r              )
            `REG_NO_CP_NONCORE_RST(this.error2_intr_count_r              )
            `REG_NO_CP_NONCORE_RST(this.error3_intr_count_r              )
            `REG____CP_NONCORE_RST(this.notif_cmd_done_intr_count_r      )
            `REG____CP_NONCORE_RST(this.error0_intr_count_incr_r         )
            `REG____CP_NONCORE_RST(this.error1_intr_count_incr_r         )
            `REG____CP_NONCORE_RST(this.error2_intr_count_incr_r         )
            `REG____CP_NONCORE_RST(this.error3_intr_count_incr_r         )
            `REG____CP_NONCORE_RST(this.notif_cmd_done_intr_count_incr_r )
            while (blk_flds.size() != 0) begin
                uvm_reg_field cur_fld = blk_flds.pop_front();
                `uvm_error("SHA512_ACC_CSR__INTR_BLOCK_T_EXT", {"No extended reset configuration defined for ", cur_fld.get_full_name()})
            end
        endfunction

        virtual function void build();
            super.build();
            this.configure_reset_values();
            this.sha512_acc_csr_intr_AHB_map = create_map("intr_AHB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
            this.sha512_acc_csr_intr_APB_map = create_map("intr_APB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
        endfunction

        virtual function void build_ext_maps();
            uvm_reg regs[$];

            this.default_map.get_registers(regs, UVM_NO_HIER);
            foreach(regs[c_reg]) begin
                this.sha512_acc_csr_intr_AHB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
                this.sha512_acc_csr_intr_APB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
            end
        endfunction

    endclass : sha512_acc_csr__intr_block_t_ext

    class sha512_acc_csr_ext extends sha512_acc_csr;
        // default_map_ext has intr_block_rf_ext.default_map as a submap; the
        // native this.default_map adds intr_block_rf.default_map as submap
        // We need this additional map so that the new intr_block_rf_ext can be
        // initialized, and the default_map assigned to a parent. This allows
        // get_offset methods to work on member registers, so we can then add
        // them to the AHB/APB maps
        uvm_reg_map default_map_ext;
        uvm_reg_map sha512_acc_csr_AHB_map;
        uvm_reg_map sha512_acc_csr_APB_map;

        // This coexists with intr_block_rf (from the parent class), but
        // intr_block_rf is only added as a submap to default_map and
        // should never be used in practice
        rand sha512_acc_csr__intr_block_t_ext intr_block_rf_ext;

        function new(string name = "sha512_acc_csr_ext");
            super.new(name);
        endfunction : new

        // FIXME Manually maintaining a list here of registers that are configured
        //       as soft-resettable (i.e. cptra_rst_b instead of cptra_pwrgood)
        //       or noncore-resettable (i.e. cptra_noncore_rst_b instead of cptra_pwrgood)
        //       Ideally would be auto-generated.
        virtual function void configure_reset_values();
            // Track reset configuration against a queue of all fields in this block, to ensure each register is handled
            uvm_reg_field blk_flds[$];
            get_fields(blk_flds, UVM_NO_HIER);
                                     `REG____CP_NONCORE_RST(this.LOCK          )
                                     `REG____CP_NONCORE_RST(this.USER          )
                                     `REG____CP_NONCORE_RST(this.MODE          )
                                     `REG____CP_NONCORE_RST(this.START_ADDRESS )
                                     `REG____CP_NONCORE_RST(this.DLEN          )
                                     `REG____CP_NONCORE_RST(this.DATAIN        )
                                     `REG____CP_NONCORE_RST(this.EXECUTE       )
                                     `REG____CP_NONCORE_RST(this.STATUS        )
            foreach(this.DIGEST[ii]) `REG____CP_NONCORE_RST(this.DIGEST[ii]    )
                                     `REG____CP_NONCORE_RST(this.CONTROL       )
            while (blk_flds.size() != 0) begin
                uvm_reg_field cur_fld = blk_flds.pop_front();
                `uvm_error("SHA512_ACC_CSR_EXT", {"No extended reset configuration defined for ", cur_fld.get_full_name()})
            end
        endfunction

        virtual function void build();
            super.build();
            this.configure_reset_values();
            this.intr_block_rf_ext = new("intr_block_rf_ext");
            this.intr_block_rf_ext.configure(this);
            this.intr_block_rf_ext.build(); // This configures the default_map, which is used to find reg offsets for other maps
            this.default_map_ext     = create_map("default_map_ext", 0, 4, UVM_LITTLE_ENDIAN);
            this.sha512_acc_csr_AHB_map = create_map("AHB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
            this.sha512_acc_csr_APB_map = create_map("APB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
        endfunction

        virtual function void build_ext_maps();
            uvm_reg        regs[$];
            uvm_reg_map    submaps[$];
            uvm_reg_addr_t intr_block_offset;

            this.default_map.get_registers(regs, UVM_NO_HIER);
            this.default_map.get_submaps  (submaps, UVM_NO_HIER); // <-- these submaps are from this.intr_block_rf.default_map, per the inherited build() method

            foreach(regs[c_reg]) begin
                this.default_map_ext       .add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
                this.sha512_acc_csr_AHB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
                this.sha512_acc_csr_APB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
            end

            // Find offset used to add intr_block_rf.default_map to this.default_map, so we can
            // use the same offset to add submaps to intr_block_rf_ext
            foreach(submaps[c_submap]) begin
                if (submaps[c_submap].get_name() == "reg_map") begin
                intr_block_offset = this.default_map.get_submap_offset(submaps[c_submap]);
                end
            end

            this.default_map_ext    .add_submap(this.intr_block_rf_ext.default_map, intr_block_offset);
            this.intr_block_rf_ext.build_ext_maps(); // This configures the AHB/APB maps
            this.sha512_acc_csr_AHB_map.add_submap(this.intr_block_rf_ext.sha512_acc_csr_intr_AHB_map, intr_block_offset);
            this.sha512_acc_csr_APB_map.add_submap(this.intr_block_rf_ext.sha512_acc_csr_intr_APB_map, intr_block_offset);

        endfunction

    endclass : sha512_acc_csr_ext

    // Scheduling helper class for delayed callback tasks
    `include "soc_ifc_reg_delay_job.svh"
    `include "soc_ifc_reg_delay_job_mbox_csr_mbox_prot_error.svh"
    `include "soc_ifc_reg_delay_job_intr_block_rf_ext.svh"

    // Callbacks for predicting reg-field updates
    `include "soc_ifc_reg_cbs_mbox_csr.svh"
    `include "soc_ifc_reg_cbs_mbox_csr_mbox_lock_lock.svh"
    `include "soc_ifc_reg_cbs_mbox_csr_mbox_cmd_command.svh"
    `include "soc_ifc_reg_cbs_mbox_csr_mbox_dlen_length.svh"
    `include "soc_ifc_reg_cbs_mbox_csr_mbox_datain_datain.svh"
    `include "soc_ifc_reg_cbs_mbox_csr_mbox_dataout_dataout.svh"
    `include "soc_ifc_reg_cbs_mbox_csr_mbox_status_status.svh"
    `include "soc_ifc_reg_cbs_mbox_csr_mbox_status_mbox_fsm_ps.svh"
    `include "soc_ifc_reg_cbs_mbox_csr_mbox_execute_execute.svh"
    `include "soc_ifc_reg_cbs_mbox_csr_mbox_unlock_unlock.svh"
    `include "soc_ifc_reg_cbs_intr_block_rf_ext_global_intr_en_r_base.svh"
    `include "soc_ifc_reg_cbs_intr_block_rf_ext_error_internal_intr_r_base.svh"
    `include "soc_ifc_reg_cbs_intr_block_rf_ext_error_intr_en_r_base.svh"
    `include "soc_ifc_reg_cbs_intr_block_rf_ext_error_intr_trig_r_base.svh"
    `include "soc_ifc_reg_cbs_intr_block_rf_ext_notif_internal_intr_r_base.svh"
    `include "soc_ifc_reg_cbs_intr_block_rf_ext_notif_intr_en_r_base.svh"
    `include "soc_ifc_reg_cbs_intr_block_rf_ext_notif_intr_trig_r_base.svh"
    `include "soc_ifc_reg_cbs_intr_block_rf_ext_internal.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_HW_ERROR_FATAL.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_HW_ERROR_NON_FATAL.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_DATA_DATA.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_PAUSER_LOCK_LOCK.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_REQ.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_WR_DONE.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_VALID_PAUSER_PAUSER.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_secret.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_fuse.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_key.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_internal.svh"
    `include "soc_ifc_reg_cbs_soc_ifc_reg_internal_fw_update_reset.svh"
    `include "soc_ifc_reg_cbs_sha512_acc_csr_LOCK_LOCK.svh"
    `include "soc_ifc_reg_cbs_sha512_acc_csr_EXECUTE_EXECUTE.svh"

    // Callback for sampling coverage
    `include "soc_ifc_reg_cbs_sample.svh"

// pragma uvmf custom define_register_classes end
// pragma uvmf custom define_block_map_coverage_class begin
   //--------------------------------------------------------------------
   // Class: soc_ifc_AHB_map_coverage
   // 
   // Coverage for the 'AHB_map' in 'soc_ifc_reg_model'
   //--------------------------------------------------------------------
   class soc_ifc_AHB_map_coverage extends uvm_object;
      `uvm_object_utils(soc_ifc_AHB_map_coverage)

      covergroup ra_cov(string name) with function sample(uvm_reg_addr_t addr, bit is_read);

         option.per_instance = 1;
         option.name = name; 

         // FIXME
         ADDR: coverpoint addr {
            bins example_reg0 = {'h0};
            bins example_reg1 = {'h1};
         }

         RW: coverpoint is_read {
            bins RD = {1};
            bins WR = {0};
         }

         ACCESS: cross ADDR, RW;

      endgroup: ra_cov

      function new(string name = "soc_ifc_AHB_map_coverage");
         ra_cov = new(name);
      endfunction: new

      function void sample(uvm_reg_addr_t offset, bit is_read);
         ra_cov.sample(offset, is_read);
      endfunction: sample

   endclass: soc_ifc_AHB_map_coverage
   //--------------------------------------------------------------------
   // Class: soc_ifc_APB_map_coverage
   // 
   // Coverage for the 'APB_map' in 'soc_ifc_reg_model'
   //--------------------------------------------------------------------
   class soc_ifc_APB_map_coverage extends uvm_object;
      `uvm_object_utils(soc_ifc_APB_map_coverage)

      covergroup ra_cov(string name) with function sample(uvm_reg_addr_t addr, bit is_read);

         option.per_instance = 1;
         option.name = name; 

         // FIXME
         ADDR: coverpoint addr {
            bins example_reg0 = {'h0};
            bins example_reg1 = {'h1};
         }

         RW: coverpoint is_read {
            bins RD = {1};
            bins WR = {0};
         }

         ACCESS: cross ADDR, RW;

      endgroup: ra_cov

      function new(string name = "soc_ifc_APB_map_coverage");
         ra_cov = new(name);
      endfunction: new

      function void sample(uvm_reg_addr_t offset, bit is_read);
         ra_cov.sample(offset, is_read);
      endfunction: sample

   endclass: soc_ifc_APB_map_coverage
// pragma uvmf custom define_block_map_coverage_class end

   //--------------------------------------------------------------------
   // Class: soc_ifc_reg_model_top
   // 
   //--------------------------------------------------------------------
   class soc_ifc_reg_model_top extends uvm_reg_block;
      `uvm_object_utils(soc_ifc_reg_model_top)
// pragma uvmf custom instantiate_registers_within_block begin
        rand uvm_mem            mbox_mem_rm;
        rand mbox_csr_ext       mbox_csr_rm;
        rand sha512_acc_csr_ext sha512_acc_csr_rm;
        rand soc_ifc_reg_ext    soc_ifc_reg_rm;

        uvm_reg_map default_map; // Block map
        uvm_reg_map soc_ifc_APB_map; // Block map
        uvm_reg_map soc_ifc_AHB_map; // Block map

        soc_ifc_reg_cbs_intr_block_rf_ext_global_intr_en_r_base      soc_ifc_reg_intr_block_rf_ext_global_intr_en_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_error_internal_intr_r_base soc_ifc_reg_intr_block_rf_ext_error_internal_intr_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_error_intr_en_r_base       soc_ifc_reg_intr_block_rf_ext_error_intr_en_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_error_intr_trig_r_base     soc_ifc_reg_intr_block_rf_ext_error_intr_trig_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_notif_internal_intr_r_base soc_ifc_reg_intr_block_rf_ext_notif_internal_intr_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_notif_intr_en_r_base       soc_ifc_reg_intr_block_rf_ext_notif_intr_en_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_notif_intr_trig_r_base     soc_ifc_reg_intr_block_rf_ext_notif_intr_trig_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_internal                   soc_ifc_reg_intr_block_rf_ext_internal_cb;

        soc_ifc_reg_cbs_intr_block_rf_ext_global_intr_en_r_base      sha512_acc_csr_intr_block_rf_ext_global_intr_en_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_error_internal_intr_r_base sha512_acc_csr_intr_block_rf_ext_error_internal_intr_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_error_intr_en_r_base       sha512_acc_csr_intr_block_rf_ext_error_intr_en_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_error_intr_trig_r_base     sha512_acc_csr_intr_block_rf_ext_error_intr_trig_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_notif_internal_intr_r_base sha512_acc_csr_intr_block_rf_ext_notif_internal_intr_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_notif_intr_en_r_base       sha512_acc_csr_intr_block_rf_ext_notif_intr_en_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_notif_intr_trig_r_base     sha512_acc_csr_intr_block_rf_ext_notif_intr_trig_r_base_cb;
        soc_ifc_reg_cbs_intr_block_rf_ext_internal                   sha512_acc_csr_intr_block_rf_ext_internal_cb;


        soc_ifc_reg_cbs_mbox_csr_mbox_lock_lock          mbox_csr_mbox_lock_lock_cb;
        soc_ifc_reg_cbs_mbox_csr_mbox_cmd_command        mbox_csr_mbox_cmd_command_cb;
        soc_ifc_reg_cbs_mbox_csr_mbox_dlen_length        mbox_csr_mbox_dlen_length_cb;
        soc_ifc_reg_cbs_mbox_csr_mbox_datain_datain      mbox_csr_mbox_datain_datain_cb;
        soc_ifc_reg_cbs_mbox_csr_mbox_dataout_dataout    mbox_csr_mbox_dataout_dataout_cb;
        soc_ifc_reg_cbs_mbox_csr_mbox_status_status      mbox_csr_mbox_status_status_cb;
        soc_ifc_reg_cbs_mbox_csr_mbox_status_mbox_fsm_ps mbox_csr_mbox_status_mbox_fsm_ps_cb;
        soc_ifc_reg_cbs_mbox_csr_mbox_execute_execute    mbox_csr_mbox_execute_execute_cb;
        soc_ifc_reg_cbs_mbox_csr_mbox_unlock_unlock      mbox_csr_mbox_unlock_unlock_cb;

        soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_HW_ERROR_FATAL              soc_ifc_reg_CPTRA_HW_ERROR_FATAL_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_HW_ERROR_NON_FATAL          soc_ifc_reg_CPTRA_HW_ERROR_NON_FATAL_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_DATA_DATA              soc_ifc_reg_CPTRA_TRNG_DATA_DATA_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_PAUSER_LOCK_LOCK       soc_ifc_reg_CPTRA_TRNG_PAUSER_LOCK_LOCK_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR             soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_REQ        soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_REQ_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_WR_DONE    soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_WR_DONE_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_VALID_PAUSER_PAUSER    soc_ifc_reg_CPTRA_TRNG_VALID_PAUSER_PAUSER_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART soc_ifc_reg_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART soc_ifc_reg_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_cb;

        soc_ifc_reg_cbs_soc_ifc_reg_secret   soc_ifc_reg_secret_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_fuse     soc_ifc_reg_fuse_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_key      soc_ifc_reg_key_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_internal soc_ifc_reg_internal_cb;
        soc_ifc_reg_cbs_soc_ifc_reg_internal_fw_update_reset soc_ifc_reg_internal_fw_update_reset_cb;

        soc_ifc_reg_cbs_sha512_acc_csr_LOCK_LOCK       sha512_acc_csr_LOCK_LOCK_cb;
        soc_ifc_reg_cbs_sha512_acc_csr_EXECUTE_EXECUTE sha512_acc_csr_EXECUTE_EXECUTE_cb;

        soc_ifc_reg_cbs_sample sample_cb;

        uvm_reg_field cptra_fatal_flds[$];
        uvm_reg_field cptra_non_fatal_flds[$];
        uvm_reg_field error_en_flds[$];
        uvm_reg_field notif_en_flds[$];
        uvm_reg_field error_sts_flds[$];
        uvm_reg_field notif_sts_flds[$];
        uvm_reg_field error_trig_flds[$];
        uvm_reg_field notif_trig_flds[$];
        uvm_reg_field all_fields[$];
        uvm_reg       all_regs[$];

        uvm_queue #(soc_ifc_reg_delay_job) delay_jobs;

// pragma uvmf custom instantiate_registers_within_block end

      soc_ifc_AHB_map_coverage AHB_map_cg;
      soc_ifc_APB_map_coverage APB_map_cg;

      // Function: new
      // 
      function new(string name = "soc_ifc_reg_model_top");
         super.new(name, build_coverage(UVM_CVR_ALL));
      endfunction

      // Function: build
      // 
      virtual function void build();
      if(has_coverage(UVM_CVR_ADDR_MAP)) begin
         AHB_map_cg = soc_ifc_AHB_map_coverage::type_id::create("AHB_map_cg");
         APB_map_cg = soc_ifc_APB_map_coverage::type_id::create("APB_map_cg");
         AHB_map_cg.ra_cov.set_inst_name({this.get_full_name(),"_AHB_cg"});
         APB_map_cg.ra_cov.set_inst_name({this.get_full_name(),"_APB_cg"});
         void'(set_coverage(UVM_CVR_ADDR_MAP));
      end


// pragma uvmf custom construct_configure_build_registers_within_block begin
        delay_jobs = new("delay_jobs");
        uvm_config_db#(uvm_queue#(soc_ifc_reg_delay_job))::set(null, "soc_ifc_reg_model_top", "delay_jobs", delay_jobs);

        // inst all soc_ifc register blocks and memory model as single reg block
        /*mbox_mem_ahb_apb*/
        this.mbox_mem_rm = new("mbox_mem_rm", 18'h8000, 32, "RW", UVM_NO_COVERAGE);
        this.mbox_mem_rm.configure(this);

        /*mbox_csr_ahb_apb*/
        this.mbox_csr_rm = new("mbox_csr_rm");
        this.mbox_csr_rm.configure(this);
        this.mbox_csr_rm.build();

        /*sha512_acc_csr_ahb_apb*/
        this.sha512_acc_csr_rm = new("sha512_acc_csr_rm");
        this.sha512_acc_csr_rm.configure(this);
        this.sha512_acc_csr_rm.build();

        /*soc_ifc_reg_ahb_apb*/
        this.soc_ifc_reg_rm = new("soc_ifc_reg_rm");
        this.soc_ifc_reg_rm.configure(this);
        this.soc_ifc_reg_rm.build();

        soc_ifc_reg_intr_block_rf_ext_global_intr_en_r_base_cb      = soc_ifc_reg_cbs_intr_block_rf_ext_global_intr_en_r_base     ::type_id::create("soc_ifc_reg_intr_block_rf_ext_global_intr_en_r_base_cb"     );
        soc_ifc_reg_intr_block_rf_ext_error_internal_intr_r_base_cb = soc_ifc_reg_cbs_intr_block_rf_ext_error_internal_intr_r_base::type_id::create("soc_ifc_reg_intr_block_rf_ext_error_internal_intr_r_base_cb");
        soc_ifc_reg_intr_block_rf_ext_error_intr_en_r_base_cb       = soc_ifc_reg_cbs_intr_block_rf_ext_error_intr_en_r_base      ::type_id::create("soc_ifc_reg_intr_block_rf_ext_error_intr_en_r_base_cb"      );
        soc_ifc_reg_intr_block_rf_ext_error_intr_trig_r_base_cb     = soc_ifc_reg_cbs_intr_block_rf_ext_error_intr_trig_r_base    ::type_id::create("soc_ifc_reg_intr_block_rf_ext_error_intr_trig_r_base_cb"    );
        soc_ifc_reg_intr_block_rf_ext_notif_internal_intr_r_base_cb = soc_ifc_reg_cbs_intr_block_rf_ext_notif_internal_intr_r_base::type_id::create("soc_ifc_reg_intr_block_rf_ext_notif_internal_intr_r_base_cb");
        soc_ifc_reg_intr_block_rf_ext_notif_intr_en_r_base_cb       = soc_ifc_reg_cbs_intr_block_rf_ext_notif_intr_en_r_base      ::type_id::create("soc_ifc_reg_intr_block_rf_ext_notif_intr_en_r_base_cb"      );
        soc_ifc_reg_intr_block_rf_ext_notif_intr_trig_r_base_cb     = soc_ifc_reg_cbs_intr_block_rf_ext_notif_intr_trig_r_base    ::type_id::create("soc_ifc_reg_intr_block_rf_ext_notif_intr_trig_r_base_cb"    );
        soc_ifc_reg_intr_block_rf_ext_internal_cb                   = soc_ifc_reg_cbs_intr_block_rf_ext_internal                  ::type_id::create("soc_ifc_reg_intr_block_rf_ext_internal_cb"                  );

        sha512_acc_csr_intr_block_rf_ext_global_intr_en_r_base_cb      = soc_ifc_reg_cbs_intr_block_rf_ext_global_intr_en_r_base     ::type_id::create("sha512_acc_csr_intr_block_rf_ext_global_intr_en_r_base_cb"     );
        sha512_acc_csr_intr_block_rf_ext_error_internal_intr_r_base_cb = soc_ifc_reg_cbs_intr_block_rf_ext_error_internal_intr_r_base::type_id::create("sha512_acc_csr_intr_block_rf_ext_error_internal_intr_r_base_cb");
        sha512_acc_csr_intr_block_rf_ext_error_intr_en_r_base_cb       = soc_ifc_reg_cbs_intr_block_rf_ext_error_intr_en_r_base      ::type_id::create("sha512_acc_csr_intr_block_rf_ext_error_intr_en_r_base_cb"      );
        sha512_acc_csr_intr_block_rf_ext_error_intr_trig_r_base_cb     = soc_ifc_reg_cbs_intr_block_rf_ext_error_intr_trig_r_base    ::type_id::create("sha512_acc_csr_intr_block_rf_ext_error_intr_trig_r_base_cb"    );
        sha512_acc_csr_intr_block_rf_ext_notif_internal_intr_r_base_cb = soc_ifc_reg_cbs_intr_block_rf_ext_notif_internal_intr_r_base::type_id::create("sha512_acc_csr_intr_block_rf_ext_notif_internal_intr_r_base_cb");
        sha512_acc_csr_intr_block_rf_ext_notif_intr_en_r_base_cb       = soc_ifc_reg_cbs_intr_block_rf_ext_notif_intr_en_r_base      ::type_id::create("sha512_acc_csr_intr_block_rf_ext_notif_intr_en_r_base_cb"      );
        sha512_acc_csr_intr_block_rf_ext_notif_intr_trig_r_base_cb     = soc_ifc_reg_cbs_intr_block_rf_ext_notif_intr_trig_r_base    ::type_id::create("sha512_acc_csr_intr_block_rf_ext_notif_intr_trig_r_base_cb"    );
        sha512_acc_csr_intr_block_rf_ext_internal_cb                   = soc_ifc_reg_cbs_intr_block_rf_ext_internal                  ::type_id::create("sha512_acc_csr_intr_block_rf_ext_internal_cb"                  );

        mbox_csr_mbox_lock_lock_cb          = soc_ifc_reg_cbs_mbox_csr_mbox_lock_lock         ::type_id::create("mbox_csr_mbox_lock_lock_cb"         );
        mbox_csr_mbox_cmd_command_cb        = soc_ifc_reg_cbs_mbox_csr_mbox_cmd_command       ::type_id::create("mbox_csr_mbox_cmd_command_cb"       );
        mbox_csr_mbox_dlen_length_cb        = soc_ifc_reg_cbs_mbox_csr_mbox_dlen_length       ::type_id::create("mbox_csr_mbox_dlen_length_cb"       );
        mbox_csr_mbox_datain_datain_cb      = soc_ifc_reg_cbs_mbox_csr_mbox_datain_datain     ::type_id::create("mbox_csr_mbox_datain_datain_cb"     );
        mbox_csr_mbox_dataout_dataout_cb    = soc_ifc_reg_cbs_mbox_csr_mbox_dataout_dataout   ::type_id::create("mbox_csr_mbox_dataout_dataout_cb"   );
        mbox_csr_mbox_status_status_cb      = soc_ifc_reg_cbs_mbox_csr_mbox_status_status     ::type_id::create("mbox_csr_mbox_status_status_cb"     );
        mbox_csr_mbox_status_mbox_fsm_ps_cb = soc_ifc_reg_cbs_mbox_csr_mbox_status_mbox_fsm_ps::type_id::create("mbox_csr_mbox_status_mbox_fsm_ps_cb");
        mbox_csr_mbox_execute_execute_cb    = soc_ifc_reg_cbs_mbox_csr_mbox_execute_execute   ::type_id::create("mbox_csr_mbox_execute_execute_cb"   );
        mbox_csr_mbox_unlock_unlock_cb      = soc_ifc_reg_cbs_mbox_csr_mbox_unlock_unlock     ::type_id::create("mbox_csr_mbox_unlock_unlock_cb"     );

        soc_ifc_reg_CPTRA_HW_ERROR_FATAL_cb            = soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_HW_ERROR_FATAL          ::type_id::create("soc_ifc_reg_CPTRA_HW_ERROR_FATAL_cb"          );
        soc_ifc_reg_CPTRA_HW_ERROR_NON_FATAL_cb        = soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_HW_ERROR_NON_FATAL      ::type_id::create("soc_ifc_reg_CPTRA_HW_ERROR_NON_FATAL_cb"      );
        soc_ifc_reg_CPTRA_TRNG_DATA_DATA_cb            = soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_DATA_DATA          ::type_id::create("soc_ifc_reg_CPTRA_TRNG_DATA_DATA_cb"          );
        soc_ifc_reg_CPTRA_TRNG_PAUSER_LOCK_LOCK_cb     = soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_PAUSER_LOCK_LOCK   ::type_id::create("soc_ifc_reg_CPTRA_TRNG_PAUSER_LOCK_LOCK_cb"   );
        soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR_cb           = soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR         ::type_id::create("soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR_cb"         );
        soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_REQ_cb      = soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_REQ    ::type_id::create("soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_REQ_cb"    );
        soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_WR_DONE_cb  = soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_WR_DONE::type_id::create("soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_WR_DONE_cb");
        soc_ifc_reg_CPTRA_TRNG_VALID_PAUSER_PAUSER_cb  = soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_TRNG_VALID_PAUSER_PAUSER::type_id::create("soc_ifc_reg_CPTRA_TRNG_VALID_PAUSER_PAUSER_cb");
        soc_ifc_reg_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_cb = soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART::type_id::create("soc_ifc_reg_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_cb");
        soc_ifc_reg_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_cb = soc_ifc_reg_cbs_soc_ifc_reg_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART::type_id::create("soc_ifc_reg_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_cb");

        soc_ifc_reg_secret_cb   = soc_ifc_reg_cbs_soc_ifc_reg_secret  ::type_id::create("soc_ifc_reg_secret_cb");
        soc_ifc_reg_fuse_cb     = soc_ifc_reg_cbs_soc_ifc_reg_fuse    ::type_id::create("soc_ifc_reg_fuse_cb");
        soc_ifc_reg_key_cb      = soc_ifc_reg_cbs_soc_ifc_reg_key     ::type_id::create("soc_ifc_reg_key_cb");
        soc_ifc_reg_internal_cb = soc_ifc_reg_cbs_soc_ifc_reg_internal::type_id::create("soc_ifc_reg_internal_cb");
        soc_ifc_reg_internal_fw_update_reset_cb = soc_ifc_reg_cbs_soc_ifc_reg_internal_fw_update_reset::type_id::create("soc_ifc_reg_internal_fw_update_reset_cb");

        sha512_acc_csr_LOCK_LOCK_cb       = soc_ifc_reg_cbs_sha512_acc_csr_LOCK_LOCK::type_id::create("sha512_acc_csr_LOCK_LOCK_cb");
        sha512_acc_csr_EXECUTE_EXECUTE_cb = soc_ifc_reg_cbs_sha512_acc_csr_EXECUTE_EXECUTE::type_id::create("sha512_acc_csr_EXECUTE_EXECUTE_cb");

        sample_cb = soc_ifc_reg_cbs_sample::type_id::create("sample_cb");

        // Callbacks compute side-effects to other registers in the reg-model
        // in response to 'do_predict'.
        // 'do_predict' is invoked by the reg_predictor after receiving a transaction
        // from the soc_ifc_predictor.

        /* -- soc_ifc_reg interrupts -- */
        uvm_reg_field_cb::add(soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.error_en, soc_ifc_reg_intr_block_rf_ext_global_intr_en_r_base_cb     );
        uvm_reg_field_cb::add(soc_ifc_reg_rm.intr_block_rf_ext.global_intr_en_r.notif_en, soc_ifc_reg_intr_block_rf_ext_global_intr_en_r_base_cb     );
        this.soc_ifc_reg_rm.intr_block_rf_ext.error_intr_en_r      .get_fields(error_en_flds  );
        this.soc_ifc_reg_rm.intr_block_rf_ext.notif_intr_en_r      .get_fields(notif_en_flds  );
        this.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_r.get_fields(error_sts_flds );
        this.soc_ifc_reg_rm.intr_block_rf_ext.notif_internal_intr_r.get_fields(notif_sts_flds );
        this.soc_ifc_reg_rm.intr_block_rf_ext.error_intr_trig_r    .get_fields(error_trig_flds);
        this.soc_ifc_reg_rm.intr_block_rf_ext.notif_intr_trig_r    .get_fields(notif_trig_flds);
        foreach (error_en_flds  [ii]) uvm_reg_field_cb::add(error_en_flds  [ii], soc_ifc_reg_intr_block_rf_ext_error_intr_en_r_base_cb      );
        foreach (notif_en_flds  [ii]) uvm_reg_field_cb::add(notif_en_flds  [ii], soc_ifc_reg_intr_block_rf_ext_notif_intr_en_r_base_cb      );
        foreach (error_sts_flds [ii]) uvm_reg_field_cb::add(error_sts_flds [ii], soc_ifc_reg_intr_block_rf_ext_error_internal_intr_r_base_cb);
        foreach (notif_sts_flds [ii]) uvm_reg_field_cb::add(notif_sts_flds [ii], soc_ifc_reg_intr_block_rf_ext_notif_internal_intr_r_base_cb);
        foreach (error_trig_flds[ii]) uvm_reg_field_cb::add(error_trig_flds[ii], soc_ifc_reg_intr_block_rf_ext_error_intr_trig_r_base_cb    );
        foreach (notif_trig_flds[ii]) uvm_reg_field_cb::add(notif_trig_flds[ii], soc_ifc_reg_intr_block_rf_ext_notif_intr_trig_r_base_cb    );
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_count_r                 .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_inv_dev_intr_count_r                  .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_cmd_fail_intr_count_r                 .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_bad_fuse_intr_count_r                 .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_iccm_blocked_intr_count_r             .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_mbox_ecc_unc_intr_count_r             .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_wdt_timer1_timeout_intr_count_r       .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_wdt_timer2_timeout_intr_count_r       .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.notif_cmd_avail_intr_count_r                .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.notif_mbox_ecc_cor_intr_count_r             .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.notif_debug_locked_intr_count_r             .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.notif_scan_mode_intr_count_r                .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.notif_soc_req_lock_intr_count_r             .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.notif_gen_in_toggle_intr_count_r            .cnt, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_internal_intr_count_incr_r          .pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_inv_dev_intr_count_incr_r           .pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_cmd_fail_intr_count_incr_r          .pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_bad_fuse_intr_count_incr_r          .pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_iccm_blocked_intr_count_incr_r      .pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_mbox_ecc_unc_intr_count_incr_r      .pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_wdt_timer1_timeout_intr_count_incr_r.pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.error_wdt_timer2_timeout_intr_count_incr_r.pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.notif_cmd_avail_intr_count_incr_r         .pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.notif_mbox_ecc_cor_intr_count_incr_r      .pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.notif_debug_locked_intr_count_incr_r      .pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.notif_scan_mode_intr_count_incr_r         .pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.notif_soc_req_lock_intr_count_incr_r      .pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.soc_ifc_reg_rm.intr_block_rf_ext.notif_gen_in_toggle_intr_count_incr_r     .pulse, soc_ifc_reg_intr_block_rf_ext_internal_cb);

        /* -- sha512_acc_csr interrupts -- */
        uvm_reg_field_cb::add(sha512_acc_csr_rm.intr_block_rf_ext.global_intr_en_r.error_en, sha512_acc_csr_intr_block_rf_ext_global_intr_en_r_base_cb     );
        uvm_reg_field_cb::add(sha512_acc_csr_rm.intr_block_rf_ext.global_intr_en_r.notif_en, sha512_acc_csr_intr_block_rf_ext_global_intr_en_r_base_cb     );
        error_en_flds  .delete(); 
        notif_en_flds  .delete(); 
        error_sts_flds .delete(); 
        notif_sts_flds .delete(); 
        error_trig_flds.delete(); 
        notif_trig_flds.delete(); 
        this.sha512_acc_csr_rm.intr_block_rf_ext.error_intr_en_r      .get_fields(error_en_flds  );
        this.sha512_acc_csr_rm.intr_block_rf_ext.notif_intr_en_r      .get_fields(notif_en_flds  );
        this.sha512_acc_csr_rm.intr_block_rf_ext.error_internal_intr_r.get_fields(error_sts_flds );
        this.sha512_acc_csr_rm.intr_block_rf_ext.notif_internal_intr_r.get_fields(notif_sts_flds );
        this.sha512_acc_csr_rm.intr_block_rf_ext.error_intr_trig_r    .get_fields(error_trig_flds);
        this.sha512_acc_csr_rm.intr_block_rf_ext.notif_intr_trig_r    .get_fields(notif_trig_flds);
        foreach (error_en_flds  [ii]) uvm_reg_field_cb::add(error_en_flds  [ii], sha512_acc_csr_intr_block_rf_ext_error_intr_en_r_base_cb      );
        foreach (notif_en_flds  [ii]) uvm_reg_field_cb::add(notif_en_flds  [ii], sha512_acc_csr_intr_block_rf_ext_notif_intr_en_r_base_cb      );
        foreach (error_sts_flds [ii]) uvm_reg_field_cb::add(error_sts_flds [ii], sha512_acc_csr_intr_block_rf_ext_error_internal_intr_r_base_cb);
        foreach (notif_sts_flds [ii]) uvm_reg_field_cb::add(notif_sts_flds [ii], sha512_acc_csr_intr_block_rf_ext_notif_internal_intr_r_base_cb);
        foreach (error_trig_flds[ii]) uvm_reg_field_cb::add(error_trig_flds[ii], sha512_acc_csr_intr_block_rf_ext_error_intr_trig_r_base_cb    );
        foreach (notif_trig_flds[ii]) uvm_reg_field_cb::add(notif_trig_flds[ii], sha512_acc_csr_intr_block_rf_ext_notif_intr_trig_r_base_cb    );
        uvm_reg_field_cb::add(this.sha512_acc_csr_rm.intr_block_rf_ext.error0_intr_count_r                .cnt, sha512_acc_csr_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.sha512_acc_csr_rm.intr_block_rf_ext.error1_intr_count_r                .cnt, sha512_acc_csr_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.sha512_acc_csr_rm.intr_block_rf_ext.error2_intr_count_r                .cnt, sha512_acc_csr_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.sha512_acc_csr_rm.intr_block_rf_ext.error3_intr_count_r                .cnt, sha512_acc_csr_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.sha512_acc_csr_rm.intr_block_rf_ext.notif_cmd_done_intr_count_r        .cnt, sha512_acc_csr_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.sha512_acc_csr_rm.intr_block_rf_ext.error0_intr_count_incr_r         .pulse, sha512_acc_csr_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.sha512_acc_csr_rm.intr_block_rf_ext.error1_intr_count_incr_r         .pulse, sha512_acc_csr_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.sha512_acc_csr_rm.intr_block_rf_ext.error2_intr_count_incr_r         .pulse, sha512_acc_csr_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.sha512_acc_csr_rm.intr_block_rf_ext.error3_intr_count_incr_r         .pulse, sha512_acc_csr_intr_block_rf_ext_internal_cb);
        uvm_reg_field_cb::add(this.sha512_acc_csr_rm.intr_block_rf_ext.notif_cmd_done_intr_count_incr_r .pulse, sha512_acc_csr_intr_block_rf_ext_internal_cb);

        /* -- mbox_csr -- */
        uvm_reg_field_cb::add(mbox_csr_rm.mbox_lock   .lock       , mbox_csr_mbox_lock_lock_cb         );
        uvm_reg_field_cb::add(mbox_csr_rm.mbox_cmd    .command    , mbox_csr_mbox_cmd_command_cb       );
        uvm_reg_field_cb::add(mbox_csr_rm.mbox_dlen   .length     , mbox_csr_mbox_dlen_length_cb       );
        uvm_reg_field_cb::add(mbox_csr_rm.mbox_datain .datain     , mbox_csr_mbox_datain_datain_cb     );
        uvm_reg_field_cb::add(mbox_csr_rm.mbox_dataout.dataout    , mbox_csr_mbox_dataout_dataout_cb   );
        uvm_reg_field_cb::add(mbox_csr_rm.mbox_status .status     , mbox_csr_mbox_status_status_cb     );
        uvm_reg_field_cb::add(mbox_csr_rm.mbox_status .mbox_fsm_ps, mbox_csr_mbox_status_mbox_fsm_ps_cb);
        uvm_reg_field_cb::add(mbox_csr_rm.mbox_execute.execute    , mbox_csr_mbox_execute_execute_cb   );
        uvm_reg_field_cb::add(mbox_csr_rm.mbox_unlock .unlock     , mbox_csr_mbox_unlock_unlock_cb     );

        /* -- soc_ifc_reg -- */
        soc_ifc_reg_rm.CPTRA_HW_ERROR_FATAL    .get_fields(cptra_fatal_flds    );
        soc_ifc_reg_rm.CPTRA_HW_ERROR_NON_FATAL.get_fields(cptra_non_fatal_flds);
        foreach (cptra_fatal_flds    [ii]) if (cptra_fatal_flds    [ii].get_name() == "rsvd") cptra_fatal_flds    .delete(ii);
        foreach (cptra_non_fatal_flds[ii]) if (cptra_non_fatal_flds[ii].get_name() == "rsvd") cptra_non_fatal_flds.delete(ii);

        foreach (cptra_fatal_flds    [ii])           uvm_reg_field_cb::add(cptra_fatal_flds    [ii]               , soc_ifc_reg_CPTRA_HW_ERROR_FATAL_cb    );
        foreach (cptra_non_fatal_flds[ii])           uvm_reg_field_cb::add(cptra_non_fatal_flds[ii]               , soc_ifc_reg_CPTRA_HW_ERROR_NON_FATAL_cb);
        uvm_reg_field_cb::add(soc_ifc_reg_rm.CPTRA_BOOT_STATUS.status             , soc_ifc_reg_internal_cb                       );
        foreach (soc_ifc_reg_rm.CPTRA_TRNG_DATA[ii]) uvm_reg_field_cb::add(soc_ifc_reg_rm.CPTRA_TRNG_DATA[ii].DATA, soc_ifc_reg_CPTRA_TRNG_DATA_DATA_cb);
        uvm_reg_field_cb::add(soc_ifc_reg_rm.CPTRA_TRNG_PAUSER_LOCK  .LOCK        , soc_ifc_reg_CPTRA_TRNG_PAUSER_LOCK_LOCK_cb    );
        uvm_reg_field_cb::add(soc_ifc_reg_rm.CPTRA_TRNG_STATUS       .DATA_REQ    , soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_REQ_cb     );
        uvm_reg_field_cb::add(soc_ifc_reg_rm.CPTRA_TRNG_STATUS       .DATA_WR_DONE, soc_ifc_reg_CPTRA_TRNG_STATUS_DATA_WR_DONE_cb );
        uvm_reg_field_cb::add(soc_ifc_reg_rm.CPTRA_TRNG_VALID_PAUSER .PAUSER      , soc_ifc_reg_CPTRA_TRNG_VALID_PAUSER_PAUSER_cb );
        uvm_reg_field_cb::add(soc_ifc_reg_rm.CPTRA_TRNG_CTRL         .clear       , soc_ifc_reg_CPTRA_TRNG_CTRL_CLEAR_cb );
        uvm_reg_field_cb::add(soc_ifc_reg_rm.CPTRA_WDT_TIMER1_CTRL   .timer1_restart, soc_ifc_reg_CPTRA_WDT_TIMER1_CTRL_TIMER1_RESTART_cb );
        uvm_reg_field_cb::add(soc_ifc_reg_rm.CPTRA_WDT_TIMER2_CTRL   .timer2_restart, soc_ifc_reg_CPTRA_WDT_TIMER2_CTRL_TIMER2_RESTART_cb );

        foreach (soc_ifc_reg_rm.fuse_uds_seed[ii])             uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_uds_seed[ii].seed             , soc_ifc_reg_secret_cb);
        foreach (soc_ifc_reg_rm.fuse_field_entropy[ii])        uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_field_entropy[ii].seed        , soc_ifc_reg_secret_cb);
        foreach (soc_ifc_reg_rm.fuse_key_manifest_pk_hash[ii]) uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_key_manifest_pk_hash[ii].hash , soc_ifc_reg_fuse_cb);
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_key_manifest_pk_hash_mask.mask, soc_ifc_reg_fuse_cb);
        foreach (soc_ifc_reg_rm.fuse_owner_pk_hash[ii])        uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_owner_pk_hash[ii].hash        , soc_ifc_reg_fuse_cb);
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_fmc_key_manifest_svn.svn      , soc_ifc_reg_fuse_cb);
        foreach (soc_ifc_reg_rm.fuse_runtime_svn[ii])          uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_runtime_svn[ii].svn           , soc_ifc_reg_fuse_cb);
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_anti_rollback_disable.dis     , soc_ifc_reg_fuse_cb);
        foreach (soc_ifc_reg_rm.fuse_idevid_cert_attr[ii])     uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_idevid_cert_attr[ii].cert     , soc_ifc_reg_fuse_cb);
        foreach (soc_ifc_reg_rm.fuse_idevid_manuf_hsm_id[ii])  uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_idevid_manuf_hsm_id[ii].hsm_id, soc_ifc_reg_fuse_cb);
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_life_cycle.life_cycle         , soc_ifc_reg_fuse_cb);
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_lms_verify.lms_verify         , soc_ifc_reg_fuse_cb);
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_lms_revocation.lms_revocation , soc_ifc_reg_fuse_cb);
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.fuse_soc_stepping_id.soc_stepping_id, soc_ifc_reg_fuse_cb);
        foreach (soc_ifc_reg_rm.internal_obf_key[ii])          uvm_reg_field_cb::add(soc_ifc_reg_rm.internal_obf_key[ii].key           , soc_ifc_reg_key_cb);
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.internal_iccm_lock.lock            , soc_ifc_reg_internal_cb);
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.internal_fw_update_reset.core_rst  , soc_ifc_reg_internal_fw_update_reset_cb) ;
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.internal_rv_mtime_l.count_l        , soc_ifc_reg_internal_cb);
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.internal_rv_mtime_h.count_h        , soc_ifc_reg_internal_cb);
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.internal_rv_mtimecmp_l.compare_l   , soc_ifc_reg_internal_cb);
                                                               uvm_reg_field_cb::add(soc_ifc_reg_rm.internal_rv_mtimecmp_h.compare_h   , soc_ifc_reg_internal_cb);
        /* -- sha512_acc_csr -- */
        uvm_reg_field_cb::add(sha512_acc_csr_rm.LOCK.LOCK, sha512_acc_csr_LOCK_LOCK_cb);
        uvm_reg_field_cb::add(sha512_acc_csr_rm.EXECUTE.EXECUTE, sha512_acc_csr_EXECUTE_EXECUTE_cb);

        /* -- Coverage sampling callback for all registers */
        // Add this callback after all other callbacks so it runs AFTER the prediction is finalized
        get_registers(all_regs, UVM_HIER);
        foreach (all_regs[ii]) begin
            all_fields.delete();
            all_regs[ii].get_fields(all_fields);
            foreach (all_fields[jj]) begin
                uvm_reg_field_cb::add(all_fields[jj], sample_cb);
            end
        end

// pragma uvmf custom construct_configure_build_registers_within_block end
// pragma uvmf custom add_registers_to_block_map begin
        /* Top register model default map */
        // NOTE: Initialize here using add_submap to avoid UVM_WARNING inside uvm_reg_map
        //       but we don't ever use the "default_map" -- instead use AHB/APB maps to
        //       access registers
        this.default_map = create_map("soc_ifc_default_map", 0, 4, UVM_LITTLE_ENDIAN);
        this.default_map.add_mem(this.mbox_mem_rm, 0, "RW");
        this.default_map.add_submap(this.mbox_csr_rm.default_map, 'h2_0000);
        this.default_map.add_submap(this.sha512_acc_csr_rm.default_map, 'h2_1000);
        this.default_map.add_submap(this.soc_ifc_reg_rm.default_map, 'h3_0000);

        this.soc_ifc_APB_map = create_map("soc_ifc_APB_map", 0, 4, UVM_LITTLE_ENDIAN);
        this.soc_ifc_AHB_map = create_map("soc_ifc_AHB_map", 0, 4, UVM_LITTLE_ENDIAN);

      endfunction

      // Called after lock_model in soc_ifc_env_configuration
      virtual function void build_ext_maps();
        // Requires default_map.add_submap first to avoid UVM_WARNING about
        // is_intialized (due to look-up of get_offset in constituent regs)
        // Also requires block.is_locked() to be true
        this.mbox_csr_rm.build_ext_maps();
        this.sha512_acc_csr_rm.build_ext_maps();
        this.soc_ifc_reg_rm.build_ext_maps();

        /* Top register model APB map */
        this.soc_ifc_APB_map.add_mem(this.mbox_mem_rm, 0, "RW");
        this.soc_ifc_APB_map.add_submap(this.mbox_csr_rm.mbox_csr_APB_map, 'h2_0000);
        this.soc_ifc_APB_map.add_submap(this.sha512_acc_csr_rm.sha512_acc_csr_APB_map, 'h2_1000);
        this.soc_ifc_APB_map.add_submap(this.soc_ifc_reg_rm.soc_ifc_reg_APB_map, 'h3_0000);

        /* Top register model AHB map */
        this.soc_ifc_AHB_map.add_mem(this.mbox_mem_rm, 0, "RW");
        this.soc_ifc_AHB_map.add_submap(this.mbox_csr_rm.mbox_csr_AHB_map, 'h2_0000);
        this.soc_ifc_AHB_map.add_submap(this.sha512_acc_csr_rm.sha512_acc_csr_AHB_map, 'h2_1000);
        this.soc_ifc_AHB_map.add_submap(this.soc_ifc_reg_rm.soc_ifc_reg_AHB_map, 'h3_0000);

        void'(set_coverage(get_coverage() | UVM_CVR_REG_BITS | UVM_CVR_FIELD_VALS));
// pragma uvmf custom add_registers_to_block_map end


      endfunction

      // Function: sample
      //
      function void sample(uvm_reg_addr_t offset, bit is_read, uvm_reg_map  map);
         if(get_coverage(UVM_CVR_ADDR_MAP)) begin
            if(map.get_name() == "soc_ifc_AHB_map") begin
               AHB_map_cg.sample(offset, is_read);
            end
            if(map.get_name() == "soc_ifc_APB_map") begin
               APB_map_cg.sample(offset, is_read);
            end
         end
      endfunction: sample

   endclass

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

