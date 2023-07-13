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

`ifndef SOC_IFC_REG_COVERGROUPS
    `define SOC_IFC_REG_COVERGROUPS
    
    /*----------------------- SOC_IFC_REG__CPTRA_HW_ERROR_FATAL COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_HW_ERROR_FATAL_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_HW_ERROR_FATAL_fld_cg with function sample(
    input bit [1-1:0] iccm_ecc_unc,
    input bit [1-1:0] dccm_ecc_unc,
    input bit [1-1:0] nmi_pin
    );
        option.per_instance = 1;
        iccm_ecc_unc_cp : coverpoint iccm_ecc_unc;
        dccm_ecc_unc_cp : coverpoint dccm_ecc_unc;
        nmi_pin_cp : coverpoint nmi_pin;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_HW_ERROR_NON_FATAL COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_HW_ERROR_NON_FATAL_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_HW_ERROR_NON_FATAL_fld_cg with function sample(
    input bit [1-1:0] mbox_prot_no_lock,
    input bit [1-1:0] mbox_prot_ooo,
    input bit [1-1:0] mbox_ecc_unc
    );
        option.per_instance = 1;
        mbox_prot_no_lock_cp : coverpoint mbox_prot_no_lock;
        mbox_prot_ooo_cp : coverpoint mbox_prot_ooo;
        mbox_ecc_unc_cp : coverpoint mbox_ecc_unc;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_FW_ERROR_FATAL COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_FW_ERROR_FATAL_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_FW_ERROR_FATAL_fld_cg with function sample(
    input bit [32-1:0] error_code
    );
        option.per_instance = 1;
        error_code_cp : coverpoint error_code;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_FW_ERROR_NON_FATAL COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_FW_ERROR_NON_FATAL_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_FW_ERROR_NON_FATAL_fld_cg with function sample(
    input bit [32-1:0] error_code
    );
        option.per_instance = 1;
        error_code_cp : coverpoint error_code;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_HW_ERROR_ENC COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_HW_ERROR_ENC_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_HW_ERROR_ENC_fld_cg with function sample(
    input bit [32-1:0] error_code
    );
        option.per_instance = 1;
        error_code_cp : coverpoint error_code;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_FW_ERROR_ENC COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_FW_ERROR_ENC_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_FW_ERROR_ENC_fld_cg with function sample(
    input bit [32-1:0] error_code
    );
        option.per_instance = 1;
        error_code_cp : coverpoint error_code;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_FW_EXTENDED_ERROR_INFO COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_FW_EXTENDED_ERROR_INFO_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_FW_EXTENDED_ERROR_INFO_fld_cg with function sample(
    input bit [32-1:0] error_info
    );
        option.per_instance = 1;
        error_info_cp : coverpoint error_info;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_BOOT_STATUS COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_BOOT_STATUS_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_BOOT_STATUS_fld_cg with function sample(
    input bit [32-1:0] status
    );
        option.per_instance = 1;
        status_cp : coverpoint status;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_FLOW_STATUS COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_FLOW_STATUS_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_FLOW_STATUS_fld_cg with function sample(
    input bit [25-1:0] status,
    input bit [3-1:0] boot_fsm_ps,
    input bit [1-1:0] ready_for_fw,
    input bit [1-1:0] ready_for_runtime,
    input bit [1-1:0] ready_for_fuses,
    input bit [1-1:0] mailbox_flow_done
    );
        option.per_instance = 1;
        status_cp : coverpoint status;
        boot_fsm_ps_cp : coverpoint boot_fsm_ps;
        ready_for_fw_cp : coverpoint ready_for_fw;
        ready_for_runtime_cp : coverpoint ready_for_runtime;
        ready_for_fuses_cp : coverpoint ready_for_fuses;
        mailbox_flow_done_cp : coverpoint mailbox_flow_done;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_RESET_REASON COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_RESET_REASON_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_RESET_REASON_fld_cg with function sample(
    input bit [1-1:0] FW_UPD_RESET,
    input bit [1-1:0] WARM_RESET
    );
        option.per_instance = 1;
        FW_UPD_RESET_cp : coverpoint FW_UPD_RESET;
        WARM_RESET_cp : coverpoint WARM_RESET;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_SECURITY_STATE COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_SECURITY_STATE_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_SECURITY_STATE_fld_cg with function sample(
    input bit [2-1:0] device_lifecycle,
    input bit [1-1:0] debug_locked,
    input bit [1-1:0] scan_mode,
    input bit [28-1:0] rsvd
    );
        option.per_instance = 1;
        device_lifecycle_cp : coverpoint device_lifecycle;
        debug_locked_cp : coverpoint debug_locked;
        scan_mode_cp : coverpoint scan_mode;
        rsvd_cp : coverpoint rsvd;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_MBOX_VALID_PAUSER COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_MBOX_VALID_PAUSER_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_MBOX_VALID_PAUSER_fld_cg with function sample(
    input bit [32-1:0] PAUSER
    );
        option.per_instance = 1;
        PAUSER_cp : coverpoint PAUSER;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_MBOX_PAUSER_LOCK COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_MBOX_PAUSER_LOCK_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_MBOX_PAUSER_LOCK_fld_cg with function sample(
    input bit [1-1:0] LOCK
    );
        option.per_instance = 1;
        LOCK_cp : coverpoint LOCK;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_TRNG_VALID_PAUSER COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_TRNG_VALID_PAUSER_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_TRNG_VALID_PAUSER_fld_cg with function sample(
    input bit [32-1:0] PAUSER
    );
        option.per_instance = 1;
        PAUSER_cp : coverpoint PAUSER {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_TRNG_PAUSER_LOCK COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_TRNG_PAUSER_LOCK_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_TRNG_PAUSER_LOCK_fld_cg with function sample(
    input bit [1-1:0] LOCK
    );
        option.per_instance = 1;
        LOCK_cp : coverpoint LOCK;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_TRNG_DATA COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_TRNG_DATA_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_TRNG_DATA_fld_cg with function sample(
    input bit [32-1:0] DATA
    );
        option.per_instance = 1;
        DATA_cp : coverpoint DATA {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_TRNG_STATUS COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_TRNG_STATUS_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_TRNG_STATUS_fld_cg with function sample(
    input bit [1-1:0] DATA_REQ,
    input bit [1-1:0] DATA_WR_DONE
    );
        option.per_instance = 1;
        DATA_REQ_cp : coverpoint DATA_REQ;
        DATA_WR_DONE_cp : coverpoint DATA_WR_DONE;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_FUSE_WR_DONE COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_FUSE_WR_DONE_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_FUSE_WR_DONE_fld_cg with function sample(
    input bit [1-1:0] done
    );
        option.per_instance = 1;
        done_cp : coverpoint done;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_TIMER_CONFIG COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_TIMER_CONFIG_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_TIMER_CONFIG_fld_cg with function sample(
    input bit [32-1:0] clk_period
    );
        option.per_instance = 1;
        clk_period_cp : coverpoint clk_period;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_BOOTFSM_GO COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_BOOTFSM_GO_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_BOOTFSM_GO_fld_cg with function sample(
    input bit [1-1:0] GO
    );
        option.per_instance = 1;
        GO_cp : coverpoint GO;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_DBG_MANUF_SERVICE_REG COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_DBG_MANUF_SERVICE_REG_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_DBG_MANUF_SERVICE_REG_fld_cg with function sample(
    input bit [32-1:0] DATA
    );
        option.per_instance = 1;
        DATA_cp : coverpoint DATA {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_CLK_GATING_EN COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_CLK_GATING_EN_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_CLK_GATING_EN_fld_cg with function sample(
    input bit [1-1:0] clk_gating_en
    );
        option.per_instance = 1;
        clk_gating_en_cp : coverpoint clk_gating_en;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_GENERIC_INPUT_WIRES COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_GENERIC_INPUT_WIRES_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_GENERIC_INPUT_WIRES_fld_cg with function sample(
    input bit [32-1:0] generic_wires
    );
        option.per_instance = 1;
        generic_wires_cp : coverpoint generic_wires {
            bins byte_none = {64'h0000_0000_0000_0000};
            bins byte_0    = {[0:$]} with ($countones(item[ 7: 0] > 0));
            bins byte_1    = {[0:$]} with ($countones(item[15: 8] > 0));
            bins byte_2    = {[0:$]} with ($countones(item[23:16] > 0));
            bins byte_3    = {[0:$]} with ($countones(item[31:24] > 0));
        }

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_GENERIC_OUTPUT_WIRES COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_GENERIC_OUTPUT_WIRES_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_GENERIC_OUTPUT_WIRES_fld_cg with function sample(
    input bit [32-1:0] generic_wires
    );
        option.per_instance = 1;
        generic_wires_cp : coverpoint generic_wires {
            bins byte_none = {64'h0000_0000_0000_0000};
            bins byte_0    = {[0:$]} with ($countones(item[ 7: 0] > 0));
            bins byte_1    = {[0:$]} with ($countones(item[15: 8] > 0));
            bins byte_2    = {[0:$]} with ($countones(item[23:16] > 0));
            bins byte_3    = {[0:$]} with ($countones(item[31:24] > 0));
        }

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_HW_REV_ID COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_HW_REV_ID_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_HW_REV_ID_fld_cg with function sample(
    input bit [32-1:0] REV_ID
    );
        option.per_instance = 1;
        REV_ID_cp : coverpoint REV_ID; // FIXME

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_FW_REV_ID COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_FW_REV_ID_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_FW_REV_ID_fld_cg with function sample(
    input bit [32-1:0] REV_ID
    );
        option.per_instance = 1;
        REV_ID_cp : coverpoint REV_ID; // FIXME

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_HW_CONFIG COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_HW_CONFIG_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_HW_CONFIG_fld_cg with function sample(
    input bit [1-1:0] iTRNG_en,
    input bit [1-1:0] QSPI_en,
    input bit [1-1:0] I3C_en,
    input bit [1-1:0] UART_en
    );
        option.per_instance = 1;
        iTRNG_en_cp : coverpoint iTRNG_en;
        QSPI_en_cp : coverpoint QSPI_en;
        I3C_en_cp : coverpoint I3C_en;
        UART_en_cp : coverpoint UART_en;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_TIMER1_EN COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_WDT_TIMER1_EN_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_WDT_TIMER1_EN_fld_cg with function sample(
    input bit [1-1:0] timer1_en
    );
        option.per_instance = 1;
        timer1_en_cp : coverpoint timer1_en;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_TIMER1_CTRL COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_WDT_TIMER1_CTRL_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_WDT_TIMER1_CTRL_fld_cg with function sample(
    input bit [1-1:0] timer1_restart
    );
        option.per_instance = 1;
        timer1_restart_cp : coverpoint timer1_restart;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_TIMER1_TIMEOUT_PERIOD COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_fld_cg with function sample(
    input bit [32-1:0] timer1_timeout_period
    );
        option.per_instance = 1;
        timer1_timeout_period_cp : coverpoint timer1_timeout_period;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_TIMER2_EN COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_WDT_TIMER2_EN_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_WDT_TIMER2_EN_fld_cg with function sample(
    input bit [1-1:0] timer2_en
    );
        option.per_instance = 1;
        timer2_en_cp : coverpoint timer2_en;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_TIMER2_CTRL COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_WDT_TIMER2_CTRL_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_WDT_TIMER2_CTRL_fld_cg with function sample(
    input bit [1-1:0] timer2_restart
    );
        option.per_instance = 1;
        timer2_restart_cp : coverpoint timer2_restart;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_TIMER2_TIMEOUT_PERIOD COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_fld_cg with function sample(
    input bit [32-1:0] timer2_timeout_period
    );
        option.per_instance = 1;
        timer2_timeout_period_cp : coverpoint timer2_timeout_period;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_WDT_STATUS COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_WDT_STATUS_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_WDT_STATUS_fld_cg with function sample(
    input bit [1-1:0] t1_timeout,
    input bit [1-1:0] t2_timeout
    );
        option.per_instance = 1;
        t1_timeout_cp : coverpoint t1_timeout;
        t2_timeout_cp : coverpoint t2_timeout;

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_FUSE_VALID_PAUSER COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_FUSE_VALID_PAUSER_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_FUSE_VALID_PAUSER_fld_cg with function sample(
    input bit [32-1:0] PAUSER
    );
        option.per_instance = 1;
        PAUSER_cp : coverpoint PAUSER {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__CPTRA_FUSE_PAUSER_LOCK COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__CPTRA_FUSE_PAUSER_LOCK_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__CPTRA_FUSE_PAUSER_LOCK_fld_cg with function sample(
    input bit [1-1:0] LOCK
    );
        option.per_instance = 1;
        LOCK_cp : coverpoint LOCK;

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_UDS_SEED COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_uds_seed_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_uds_seed_fld_cg with function sample(
    input bit [32-1:0] seed
    );
        option.per_instance = 1;
        seed_cp : coverpoint seed {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_FIELD_ENTROPY COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_field_entropy_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_field_entropy_fld_cg with function sample(
    input bit [32-1:0] seed
    );
        option.per_instance = 1;
        seed_cp : coverpoint seed {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_KEY_MANIFEST_PK_HASH COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_key_manifest_pk_hash_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_key_manifest_pk_hash_fld_cg with function sample(
    input bit [32-1:0] hash
    );
        option.per_instance = 1;
        hash_cp : coverpoint hash {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_KEY_MANIFEST_PK_HASH_MASK COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_key_manifest_pk_hash_mask_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_key_manifest_pk_hash_mask_fld_cg with function sample(
    input bit [4-1:0] mask
    );
        option.per_instance = 1;
        mask_cp : coverpoint mask {
            bins zero_val = {4'h0};
            bins rand_val[4] = {[1:4'hE]};
            bins ones_val = {{4{1'b1}}};
            wildcard bins set = (0 => 4'h?);
            wildcard bins clr = (4'h? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_OWNER_PK_HASH COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_owner_pk_hash_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_owner_pk_hash_fld_cg with function sample(
    input bit [32-1:0] hash
    );
        option.per_instance = 1;
        hash_cp : coverpoint hash {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_FMC_KEY_MANIFEST_SVN COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_fmc_key_manifest_svn_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_fmc_key_manifest_svn_fld_cg with function sample(
    input bit [32-1:0] svn
    );
        option.per_instance = 1;
        svn_cp : coverpoint svn {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_RUNTIME_SVN COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_runtime_svn_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_runtime_svn_fld_cg with function sample(
    input bit [32-1:0] svn
    );
        option.per_instance = 1;
        svn_cp : coverpoint svn {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_ANTI_ROLLBACK_DISABLE COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_anti_rollback_disable_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_anti_rollback_disable_fld_cg with function sample(
    input bit [1-1:0] dis
    );
        option.per_instance = 1;
        dis_cp : coverpoint dis;

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_IDEVID_CERT_ATTR COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_idevid_cert_attr_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_idevid_cert_attr_fld_cg with function sample(
    input bit [32-1:0] cert
    );
        option.per_instance = 1;
        cert_cp : coverpoint cert {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_IDEVID_MANUF_HSM_ID COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_idevid_manuf_hsm_id_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_idevid_manuf_hsm_id_fld_cg with function sample(
    input bit [32-1:0] hsm_id
    );
        option.per_instance = 1;
        hsm_id_cp : coverpoint hsm_id {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_LIFE_CYCLE COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_life_cycle_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_life_cycle_fld_cg with function sample(
    input bit [2-1:0] life_cycle
    );
        option.per_instance = 1;
        life_cycle_cp : coverpoint life_cycle;

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_LMS_VERIFY COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_lms_verify_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_lms_verify_fld_cg with function sample(
    input bit [1-1:0] lms_verify
    );
        option.per_instance = 1;
        lms_verify_cp : coverpoint lms_verify;

    endgroup

    /*----------------------- SOC_IFC_REG__FUSE_LMS_REVOCATION COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__fuse_lms_revocation_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__fuse_lms_revocation_fld_cg with function sample(
    input bit [32-1:0] lms_revocation
    );
        option.per_instance = 1;
        lms_revocation_cp : coverpoint lms_revocation;

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_OBF_KEY COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_obf_key_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_obf_key_fld_cg with function sample(
    input bit [32-1:0] key
    );
        option.per_instance = 1;
        key_cp : coverpoint key {
            bins zero_val = {32'h0};
            bins rand_val[64] = {[1:32'hFFFF_FFFE]};
            bins ones_val = {{32{1'b1}}};
            wildcard bins set = (0 => 32'h????_????);
            wildcard bins clr = (32'h????_???? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_ICCM_LOCK COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_iccm_lock_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_iccm_lock_fld_cg with function sample(
    input bit [1-1:0] lock
    );
        option.per_instance = 1;
        lock_cp : coverpoint lock;

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_FW_UPDATE_RESET COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_fw_update_reset_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_fw_update_reset_fld_cg with function sample(
    input bit [1-1:0] core_rst
    );
        option.per_instance = 1;
        core_rst_cp : coverpoint core_rst;

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_fw_update_reset_wait_cycles_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_fw_update_reset_wait_cycles_fld_cg with function sample(
    input bit [8-1:0] wait_cycles
    );
        option.per_instance = 1;
        wait_cycles_cp : coverpoint wait_cycles {
            bins zero_val = {8'h0};
            bins one_val = {1};
            bins two_val = {2};
            bins three_val = {3};
            bins small_val = {[4:15]};
            bins rand_val[16] = {[16:8'hFE]};
            bins ones_val = {{8{1'b1}}};
            wildcard bins set = (0 => 8'h??);
            wildcard bins clr = (8'h?? => 0);
        }

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_NMI_VECTOR COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_nmi_vector_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_nmi_vector_fld_cg with function sample(
    input bit [32-1:0] vec
    );
        option.per_instance = 1;
        vec_cp : coverpoint vec {
            wildcard bins ROM [16] = {32'h0000????};
            wildcard bins ICCM0[16] = {32'h4000????};
            wildcard bins ICCM1[16] = {32'h4001????};
        }

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_HW_ERROR_FATAL_MASK COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_hw_error_fatal_mask_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_hw_error_fatal_mask_fld_cg with function sample(
    input bit [1-1:0] mask_iccm_ecc_unc,
    input bit [1-1:0] mask_dccm_ecc_unc,
    input bit [1-1:0] mask_nmi_pin
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        mask_iccm_ecc_unc_cp : coverpoint mask_iccm_ecc_unc;
        mask_dccm_ecc_unc_cp : coverpoint mask_dccm_ecc_unc;
        mask_nmi_pin_cp : coverpoint mask_nmi_pin;

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_HW_ERROR_NON_FATAL_MASK COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_hw_error_non_fatal_mask_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_hw_error_non_fatal_mask_fld_cg with function sample(
    input bit [1-1:0] mask_mbox_prot_no_lock,
    input bit [1-1:0] mask_mbox_prot_ooo,
    input bit [1-1:0] mask_mbox_ecc_unc
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        mask_mbox_prot_no_lock_cp : coverpoint mask_mbox_prot_no_lock;
        mask_mbox_prot_ooo_cp : coverpoint mask_mbox_prot_ooo;
        mask_mbox_ecc_unc_cp : coverpoint mask_mbox_ecc_unc;

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_FW_ERROR_FATAL_MASK COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_fw_error_fatal_mask_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_fw_error_fatal_mask_fld_cg with function sample(
    input bit [32-1:0] mask
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        mask_cp : coverpoint mask;

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_FW_ERROR_NON_FATAL_MASK COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_fw_error_non_fatal_mask_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_fw_error_non_fatal_mask_fld_cg with function sample(
    input bit [32-1:0] mask
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        mask_cp : coverpoint mask;

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_RV_MTIME_L COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_rv_mtime_l_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_rv_mtime_l_fld_cg with function sample(
    input bit [32-1:0] count_l
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        count_l_cp : coverpoint count_l;

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_RV_MTIME_H COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_rv_mtime_h_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_rv_mtime_h_fld_cg with function sample(
    input bit [32-1:0] count_h
    );
        option.per_instance = 1;
        option.auto_bin_max = 4; /* Will have to manually force mtime to this, since it won't be reached normally in random sims */
        count_h_cp : coverpoint count_h;

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_RV_MTIMECMP_L COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_rv_mtimecmp_l_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_rv_mtimecmp_l_fld_cg with function sample(
    input bit [32-1:0] compare_l
    );
        option.per_instance = 1;
        option.auto_bin_max = 4;
        compare_l_cp : coverpoint compare_l;

    endgroup

    /*----------------------- SOC_IFC_REG__INTERNAL_RV_MTIMECMP_H COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__internal_rv_mtimecmp_h_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__internal_rv_mtimecmp_h_fld_cg with function sample(
    input bit [32-1:0] compare_h
    );
        option.per_instance = 1;
        option.auto_bin_max = 4;
        compare_h_cp : coverpoint compare_h;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__GLOBAL_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__global_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__global_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] error_en,
    input bit [1-1:0] notif_en
    );
        option.per_instance = 1;
        error_en_cp : coverpoint error_en;
        notif_en_cp : coverpoint notif_en;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__ERROR_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__error_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__error_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] error_internal_en,
    input bit [1-1:0] error_inv_dev_en,
    input bit [1-1:0] error_cmd_fail_en,
    input bit [1-1:0] error_bad_fuse_en,
    input bit [1-1:0] error_iccm_blocked_en,
    input bit [1-1:0] error_mbox_ecc_unc_en,
    input bit [1-1:0] error_wdt_timer1_timeout_en,
    input bit [1-1:0] error_wdt_timer2_timeout_en
    );
        option.per_instance = 1;
        error_internal_en_cp : coverpoint error_internal_en;
        error_inv_dev_en_cp : coverpoint error_inv_dev_en;
        error_cmd_fail_en_cp : coverpoint error_cmd_fail_en;
        error_bad_fuse_en_cp : coverpoint error_bad_fuse_en;
        error_iccm_blocked_en_cp : coverpoint error_iccm_blocked_en;
        error_mbox_ecc_unc_en_cp : coverpoint error_mbox_ecc_unc_en;
        error_wdt_timer1_timeout_en_cp : coverpoint error_wdt_timer1_timeout_en;
        error_wdt_timer2_timeout_en_cp : coverpoint error_wdt_timer2_timeout_en;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__NOTIF_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__notif_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__notif_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_avail_en,
    input bit [1-1:0] notif_mbox_ecc_cor_en,
    input bit [1-1:0] notif_debug_locked_en,
    input bit [1-1:0] notif_scan_mode_en,
    input bit [1-1:0] notif_soc_req_lock_en,
    input bit [1-1:0] notif_gen_in_toggle_en
    );
        option.per_instance = 1;
        notif_cmd_avail_en_cp : coverpoint notif_cmd_avail_en;
        notif_mbox_ecc_cor_en_cp : coverpoint notif_mbox_ecc_cor_en;
        notif_debug_locked_en_cp : coverpoint notif_debug_locked_en;
        notif_scan_mode_en_cp : coverpoint notif_scan_mode_en;
        notif_soc_req_lock_en_cp : coverpoint notif_soc_req_lock_en;
        notif_gen_in_toggle_en_cp : coverpoint notif_gen_in_toggle_en;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_DD3DCF0A COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_E6399B4A COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__ERROR_INTR_T_ERROR_BAD_FUSE_STS_23F67582_ERROR_CMD_FAIL_STS_B85845F8_ERROR_ICCM_BLOCKED_STS_E81E6AD2_ERROR_INTERNAL_STS_CAAD62E2_ERROR_INV_DEV_STS_6693E7DB_ERROR_MBOX_ECC_UNC_STS_30BFF330_ERROR_WDT_TIMER1_TIMEOUT_STS_6AAA9655_ERROR_WDT_TIMER2_TIMEOUT_STS_CDA8789F COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__error_intr_t_error_bad_fuse_sts_23f67582_error_cmd_fail_sts_b85845f8_error_iccm_blocked_sts_e81e6ad2_error_internal_sts_caad62e2_error_inv_dev_sts_6693e7db_error_mbox_ecc_unc_sts_30bff330_error_wdt_timer1_timeout_sts_6aaa9655_error_wdt_timer2_timeout_sts_cda8789f_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__error_intr_t_error_bad_fuse_sts_23f67582_error_cmd_fail_sts_b85845f8_error_iccm_blocked_sts_e81e6ad2_error_internal_sts_caad62e2_error_inv_dev_sts_6693e7db_error_mbox_ecc_unc_sts_30bff330_error_wdt_timer1_timeout_sts_6aaa9655_error_wdt_timer2_timeout_sts_cda8789f_fld_cg with function sample(
    input bit [1-1:0] error_internal_sts,
    input bit [1-1:0] error_inv_dev_sts,
    input bit [1-1:0] error_cmd_fail_sts,
    input bit [1-1:0] error_bad_fuse_sts,
    input bit [1-1:0] error_iccm_blocked_sts,
    input bit [1-1:0] error_mbox_ecc_unc_sts,
    input bit [1-1:0] error_wdt_timer1_timeout_sts,
    input bit [1-1:0] error_wdt_timer2_timeout_sts
    );
        option.per_instance = 1;
        error_internal_sts_cp : coverpoint error_internal_sts;
        error_inv_dev_sts_cp : coverpoint error_inv_dev_sts;
        error_cmd_fail_sts_cp : coverpoint error_cmd_fail_sts;
        error_bad_fuse_sts_cp : coverpoint error_bad_fuse_sts;
        error_iccm_blocked_sts_cp : coverpoint error_iccm_blocked_sts;
        error_mbox_ecc_unc_sts_cp : coverpoint error_mbox_ecc_unc_sts;
        error_wdt_timer1_timeout_sts_cp : coverpoint error_wdt_timer1_timeout_sts;
        error_wdt_timer2_timeout_sts_cp : coverpoint error_wdt_timer2_timeout_sts;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__NOTIF_INTR_T_NOTIF_CMD_AVAIL_STS_1871606B_NOTIF_DEBUG_LOCKED_STS_5F024102_NOTIF_GEN_IN_TOGGLE_STS_59F84B64_NOTIF_MBOX_ECC_COR_STS_5C3D26BB_NOTIF_SCAN_MODE_STS_122F6367_NOTIF_SOC_REQ_LOCK_STS_DEDDDE70 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__notif_intr_t_notif_cmd_avail_sts_1871606b_notif_debug_locked_sts_5f024102_notif_gen_in_toggle_sts_59f84b64_notif_mbox_ecc_cor_sts_5c3d26bb_notif_scan_mode_sts_122f6367_notif_soc_req_lock_sts_deddde70_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__notif_intr_t_notif_cmd_avail_sts_1871606b_notif_debug_locked_sts_5f024102_notif_gen_in_toggle_sts_59f84b64_notif_mbox_ecc_cor_sts_5c3d26bb_notif_scan_mode_sts_122f6367_notif_soc_req_lock_sts_deddde70_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_avail_sts,
    input bit [1-1:0] notif_mbox_ecc_cor_sts,
    input bit [1-1:0] notif_debug_locked_sts,
    input bit [1-1:0] notif_scan_mode_sts,
    input bit [1-1:0] notif_soc_req_lock_sts,
    input bit [1-1:0] notif_gen_in_toggle_sts
    );
        option.per_instance = 1;
        notif_cmd_avail_sts_cp : coverpoint notif_cmd_avail_sts;
        notif_mbox_ecc_cor_sts_cp : coverpoint notif_mbox_ecc_cor_sts;
        notif_debug_locked_sts_cp : coverpoint notif_debug_locked_sts;
        notif_scan_mode_sts_cp : coverpoint notif_scan_mode_sts;
        notif_soc_req_lock_sts_cp : coverpoint notif_soc_req_lock_sts;
        notif_gen_in_toggle_sts_cp : coverpoint notif_gen_in_toggle_sts;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__ERROR_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__error_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__error_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] error_internal_trig,
    input bit [1-1:0] error_inv_dev_trig,
    input bit [1-1:0] error_cmd_fail_trig,
    input bit [1-1:0] error_bad_fuse_trig,
    input bit [1-1:0] error_iccm_blocked_trig,
    input bit [1-1:0] error_mbox_ecc_unc_trig,
    input bit [1-1:0] error_wdt_timer1_timeout_trig,
    input bit [1-1:0] error_wdt_timer2_timeout_trig
    );
        option.per_instance = 1;
        error_internal_trig_cp : coverpoint error_internal_trig;
        error_inv_dev_trig_cp : coverpoint error_inv_dev_trig;
        error_cmd_fail_trig_cp : coverpoint error_cmd_fail_trig;
        error_bad_fuse_trig_cp : coverpoint error_bad_fuse_trig;
        error_iccm_blocked_trig_cp : coverpoint error_iccm_blocked_trig;
        error_mbox_ecc_unc_trig_cp : coverpoint error_mbox_ecc_unc_trig;
        error_wdt_timer1_timeout_trig_cp : coverpoint error_wdt_timer1_timeout_trig;
        error_wdt_timer2_timeout_trig_cp : coverpoint error_wdt_timer2_timeout_trig;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__NOTIF_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__notif_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__notif_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_avail_trig,
    input bit [1-1:0] notif_mbox_ecc_cor_trig,
    input bit [1-1:0] notif_debug_locked_trig,
    input bit [1-1:0] notif_scan_mode_trig,
    input bit [1-1:0] notif_soc_req_lock_trig,
    input bit [1-1:0] notif_gen_in_toggle_trig
    );
        option.per_instance = 1;
        notif_cmd_avail_trig_cp : coverpoint notif_cmd_avail_trig;
        notif_mbox_ecc_cor_trig_cp : coverpoint notif_mbox_ecc_cor_trig;
        notif_debug_locked_trig_cp : coverpoint notif_debug_locked_trig;
        notif_scan_mode_trig_cp : coverpoint notif_scan_mode_trig;
        notif_soc_req_lock_trig_cp : coverpoint notif_soc_req_lock_trig;
        notif_gen_in_toggle_trig_cp : coverpoint notif_gen_in_toggle_trig;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_608F1141 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_608f1141_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_608f1141_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_916AB5DF COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_916ab5df_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_916ab5df_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_B2A56031 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_b2a56031_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_b2a56031_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_FB7D2433 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_fb7d2433_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_fb7d2433_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_25E76B6F COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_25e76b6f_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_25e76b6f_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_26B97E39 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_26b97e39_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_26b97e39_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_A2F61F82 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_a2f61f82_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_a2f61f82_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_D46457CD COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_d46457cd_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_d46457cd_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_A06F0954 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_a06f0954_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_a06f0954_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_00E49272 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_00e49272_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_00e49272_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_EE53DED8 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_ee53ded8_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_ee53ded8_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_FBF3C714 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_fbf3c714_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_fbf3c714_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_B9BDDABE COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_b9bddabe_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_b9bddabe_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_57528CC1 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_57528cc1_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_t_cnt_57528cc1_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        option.auto_bin_max = 64;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_15E6ED7E COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_F762EA9C COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_f762ea9c_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_f762ea9c_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_AA8718C6 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_aa8718c6_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_aa8718c6_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_26FA5955 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_26fa5955_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_26fa5955_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_3E43D258 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_3e43d258_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_3e43d258_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_9F1632FD COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_9f1632fd_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_9f1632fd_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_AA999FDC COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_aa999fdc_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_aa999fdc_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_404E12DB COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_404e12db_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_404e12db_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_90D52137 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_90d52137_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_90d52137_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_A6DB6FFF COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_a6db6fff_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_a6db6fff_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_51891FB1 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_51891fb1_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_51891fb1_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_F5D8AFE0 COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_f5d8afe0_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_f5d8afe0_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_246489BD COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_246489bd_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_246489bd_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- SOC_IFC_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_D6ED4D1E COVERGROUPS -----------------------*/
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_d6ed4d1e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup soc_ifc_reg__intr_block_t__intr_count_incr_t_pulse_d6ed4d1e_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

`endif
