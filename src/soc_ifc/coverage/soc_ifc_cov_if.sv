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



// -- What the section under 'SCRIPT_OUTPUT' output covers --
// 
// Covergroups. 
//   - One per register; array of wide registers are under a single covergroup. 
//
// Coverpoints:
//   - Bins for total addressible space per register (including all fields)
//   - Transition bins: An AXI or AHB Write followed by AXI or AHB Read within 1000 cycles
//   - Ignore bins: IDLE (no read/write activity), simultaneous RD and WR over AXI or AHB. 
//
// Not covered and TODO.   
//   - Bins for individual fields within a register for special behavior. 
//   - New covergroups likely needed for cross coverage of related registers.
//   - Registers that don't have storage allocated (CPTRA_SECURITY_STATE, CPTRA_HW_REV_ID, CPTRA_HW_CONFIG)
//   - Possibly reduce the number of unique covergroup definitions


`ifndef VERILATOR

interface soc_ifc_cov_if
    import soc_ifc_pkg::*;
    import mbox_pkg::*;
    import soc_ifc_reg_pkg::*;
    import axi_pkg::*;
    import axi_dma_reg_pkg::*;
    import kv_defines_pkg::*;
    #(
         parameter AXI_ADDR_WIDTH = 18
        ,parameter AXI_DATA_WIDTH = 32
        ,parameter AXI_ID_WIDTH   = 32
        ,parameter AXI_USER_WIDTH = 32
        ,parameter AHB_ADDR_WIDTH = 18
        ,parameter AHB_DATA_WIDTH = 32
        ,parameter AXIM_ADDR_WIDTH = 48
        ,parameter AXIM_DATA_WIDTH = 32
        ,parameter AXIM_ID_WIDTH   = 5
        ,parameter AXIM_USER_WIDTH = 32
    )
    (
    input logic clk,
    input logic clk_cg,
    input logic soc_ifc_clk_cg,
    input logic rdc_clk_cg,

    //SoC boot signals
    input logic cptra_pwrgood,
    input logic cptra_rst_b,

    input logic ready_for_fuses,
    input logic ready_for_mb_processing,
    input logic ready_for_runtime,

    input logic mailbox_data_avail,
    input logic mailbox_flow_done,

    input logic recovery_data_avail,
    input logic recovery_image_activated,

    input var security_state_t security_state,

    input logic  [1:0][31:0] generic_input_wires,
    input logic BootFSM_BrkPoint,
    input logic [1:0][31:0] generic_output_wires,

    //SoC AXI Interface
    axi_if.w_sub s_axi_w_if,
    axi_if.r_sub s_axi_r_if,

    //uC AHB Lite Interface
    input logic [AHB_ADDR_WIDTH-1:0]  haddr_i,
    input logic [AHB_DATA_WIDTH-1:0]  hwdata_i,
    input logic                       hsel_i,
    input logic                       hwrite_i,
    input logic                       hready_i,
    input logic [1:0]                 htrans_i,
    input logic [2:0]                 hsize_i,

    input logic                      hresp_o,
    input logic                      hreadyout_o,
    input logic [AHB_DATA_WIDTH-1:0] hrdata_o,

    // AXI Manager INF
    axi_if.w_mgr m_axi_w_if,
    axi_if.r_mgr m_axi_r_if,

    //SoC Interrupts
    input logic             cptra_error_fatal,
    input logic             cptra_error_non_fatal,
    input logic             trng_req,

    //uC Interrupts
    input wire              soc_ifc_error_intr,
    input wire              soc_ifc_notif_intr,
    input wire              sha_error_intr,
    input wire              sha_notif_intr,
    input wire              dma_error_intr,
    input wire              dma_notif_intr,
    input wire              timer_intr,

    //SRAM interface
    input cptra_mbox_sram_req_t  mbox_sram_req,
    input cptra_mbox_sram_resp_t mbox_sram_resp,

    // RV ECC Status Interface
    input rv_ecc_sts_t rv_ecc_sts,

    // Clear KeyVault secrets
    input logic debugUnlock_or_scan_mode_switch,

    //Obfuscated UDS and FE
    input logic clear_obf_secrets,
    input logic scan_mode,
    input logic [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key,
    input logic [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key_reg,
    input logic                                 cptra_obf_field_entropy_vld,
    input logic [`CLP_OBF_FE_DWORDS-1 :0][31:0] cptra_obf_field_entropy,
    input logic [`CLP_OBF_FE_DWORDS-1 :0][31:0] obf_field_entropy,
    input logic                                 cptra_obf_uds_seed_vld,
    input logic [`CLP_OBF_UDS_DWORDS-1:0][31:0] cptra_obf_uds_seed,
    input logic [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed,
    input logic [OCP_LOCK_HEK_NUM_DWORDS-1:0][31:0] obf_hek_seed,

    input logic aes_input_ready,
    input logic aes_output_valid,
    input logic aes_status_idle,
    input logic aes_req_dv,
    input logic aes_req_hold,
    input soc_ifc_req_t aes_req_data,
    input logic [SOC_IFC_DATA_W-1:0] aes_rdata,
    input logic aes_error,

    // kv interface
    input  kv_read_t    kv_read,
    input  kv_rd_resp_t kv_rd_resp,


    // Subsystem mode straps
    input logic [63:0] strap_ss_caliptra_base_addr,
    input logic [63:0] strap_ss_mci_base_addr,
    input logic [63:0] strap_ss_recovery_ifc_base_addr,
    input logic [63:0] strap_ss_external_staging_area_base_addr,
    input logic [63:0] strap_ss_otp_fc_base_addr,
    input logic [63:0] strap_ss_uds_seed_base_addr,
    input logic [63:0] strap_ss_key_release_base_addr,
    input logic [15:0] strap_ss_key_release_key_size,
    input logic [31:0] strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset,
    input logic [31:0] strap_ss_num_of_prod_debug_unlock_auth_pk_hashes,
    input logic [31:0] strap_ss_strap_generic_0,
    input logic [31:0] strap_ss_strap_generic_1,
    input logic [31:0] strap_ss_strap_generic_2,
    input logic [31:0] strap_ss_strap_generic_3,
    input logic [31:0] strap_ss_caliptra_dma_axi_user,
    input logic        ss_debug_intent,
    input logic        cptra_ss_debug_intent,

    // Subsystem mode debug outputs
    input logic        ss_dbg_manuf_enable,
    input logic [63:0] ss_soc_dbg_unlock_level,

    // Subsystem mode firmware execution control
    input logic [127:0] ss_generic_fw_exec_ctrl,

    // Subsystem mode OCP LOCK status
    input  logic         ss_ocp_lock_en,
    input  logic         ss_ocp_lock_in_progress,
    input  logic [15:0]  ss_key_release_key_size,

    // NMI Vector 
    input logic [31:0] nmi_vector,
    input logic nmi_intr,

    // ICCM Lock
    input logic iccm_lock,
    input logic iccm_axs_blocked,

    //soc ifc register HW inf
    input soc_ifc_reg__out_t soc_ifc_reg_hwif_out,

    //Other blocks reset
    input logic cptra_noncore_rst_b,
    //uC reset
    input logic cptra_uc_rst_b,
    //Clock gating
    input logic clk_gating_en,
    input logic rdc_clk_dis,
    input logic fw_update_rst_window,

    input logic crypto_error,

    input logic uc_req_dv,
    input soc_ifc_req_t uc_req,
    input logic soc_req_dv,
    input soc_ifc_req_t soc_req,
    input logic soc_ifc_reg_req_dv,
    input soc_ifc_req_t soc_ifc_reg_req_data

);

  `define AXI_DMA_TOP i_axi_dma
  `define AXI_DMA_CTRL `AXI_DMA_TOP.i_axi_dma_ctrl

  enum bit [3:0] {IDLE = '0, AHB_RD = 4'h8, AHB_WR = 4'h4,  AXI_RD = 4'h2, AXI_WR = 4'h1} bus_event_e;

  typedef enum logic [1:0] {
    DMA_IDLE,
    DMA_WAIT_DATA,
    DMA_DONE,
    DMA_ERROR
  } dma_ctrl_fsm_e;

  axi_dma_reg__ctrl__rd_route__rd_route_e_e dma_rd_route;
  axi_dma_reg__ctrl__wr_route__wr_route_e_e dma_wr_route;
  dma_ctrl_fsm_e dma_ctrl_fsm_ps;

  assign dma_rd_route = axi_dma_reg__ctrl__rd_route__rd_route_e_e'(`AXI_DMA_CTRL.hwif_out.ctrl.rd_route.value);
  assign dma_wr_route = axi_dma_reg__ctrl__wr_route__wr_route_e_e'(`AXI_DMA_CTRL.hwif_out.ctrl.wr_route.value);
  assign dma_ctrl_fsm_ps = dma_ctrl_fsm_e'(`AXI_DMA_CTRL.ctrl_fsm_ps);

  logic uc_rd, uc_wr, soc_rd, soc_wr;
  logic [63:0] generic_input_wires_flat;
  logic [63:0] generic_output_wires_flat;

  assign uc_rd = uc_req_dv & ~uc_req.write;
  assign uc_wr = uc_req_dv & uc_req.write;
  assign soc_rd = soc_req_dv & ~soc_req.write;
  assign soc_wr = soc_req_dv & soc_req.write;

  assign generic_input_wires_flat  = {generic_input_wires [1],generic_input_wires [0]};
  assign generic_output_wires_flat = {generic_output_wires[1],generic_output_wires[0]};

    covergroup soc_ifc_top_cov_grp @(posedge clk);
        //IO
        cptra_pwrgood_cp: coverpoint cptra_pwrgood;
        cptra_rst_b_cp: coverpoint cptra_rst_b;
        cptra_noncore_rst_b_cp: coverpoint cptra_noncore_rst_b;
        cptra_uc_rst_b_cp: coverpoint cptra_uc_rst_b;
        clk_gating_en_cp: coverpoint clk_gating_en;
        rdc_clk_dis_cp: coverpoint rdc_clk_dis;
        fw_update_rst_window_cp: coverpoint fw_update_rst_window;
        crypto_error_cp: coverpoint crypto_error;
        security_state_cp: coverpoint security_state;
        ready_for_fuses_cp: coverpoint ready_for_fuses;
        ready_for_mb_processing_cp: coverpoint ready_for_mb_processing;
        ready_for_runtime_cp: coverpoint ready_for_runtime;
        mailbox_data_avail_cp: coverpoint mailbox_data_avail;
        mailbox_flow_done_cp: coverpoint mailbox_flow_done;
        recovery_data_avail_cp: coverpoint recovery_data_avail;
        recovery_image_activated_cp: coverpoint recovery_image_activated;
        cptra_error_fatal_cp: coverpoint cptra_error_fatal;
        cptra_error_non_fatal_cp: coverpoint cptra_error_non_fatal;
        trng_req_cp: coverpoint trng_req;
        BootFSM_BrkPoint_cp: coverpoint BootFSM_BrkPoint;
        generic_input_wires_cp: coverpoint generic_input_wires_flat {
            bins byte0_active  = generic_input_wires_cp with (|(item & (64'hFF <<  0)));
            bins byte1_active  = generic_input_wires_cp with (|(item & (64'hFF <<  8)));
            bins byte2_active  = generic_input_wires_cp with (|(item & (64'hFF << 16)));
            bins byte3_active  = generic_input_wires_cp with (|(item & (64'hFF << 24)));
            bins byte4_active  = generic_input_wires_cp with (|(item & (64'hFF << 32)));
            bins byte5_active  = generic_input_wires_cp with (|(item & (64'hFF << 40)));
            bins byte6_active  = generic_input_wires_cp with (|(item & (64'hFF << 48)));
            bins byte7_active  = generic_input_wires_cp with (|(item & (64'hFF << 56)));
        }
        generic_output_wires_cp: coverpoint generic_output_wires_flat {
            bins byte0_active  = generic_output_wires_cp with (|(item & (64'hFF <<  0)));
            bins byte1_active  = generic_output_wires_cp with (|(item & (64'hFF <<  8)));
            bins byte2_active  = generic_output_wires_cp with (|(item & (64'hFF << 16)));
            bins byte3_active  = generic_output_wires_cp with (|(item & (64'hFF << 24)));
            bins byte4_active  = generic_output_wires_cp with (|(item & (64'hFF << 32)));
            bins byte5_active  = generic_output_wires_cp with (|(item & (64'hFF << 40)));
            bins byte6_active  = generic_output_wires_cp with (|(item & (64'hFF << 48)));
            bins byte7_active  = generic_output_wires_cp with (|(item & (64'hFF << 56)));
        }
        nmi_vector_cp: coverpoint nmi_vector;
        nmi_intr_cp: coverpoint nmi_intr;
        soc_ifc_error_intr_cp: coverpoint soc_ifc_error_intr;
        soc_ifc_notif_intr_cp: coverpoint soc_ifc_notif_intr;
        sha_error_intr_cp: coverpoint sha_error_intr;
        sha_notif_intr_cp: coverpoint sha_notif_intr;
        dma_error_intr_cp: coverpoint dma_error_intr;
        dma_notif_intr_cp: coverpoint dma_notif_intr;
        timer_intr_cp: coverpoint timer_intr;
        mbox_sram_req_cp: coverpoint mbox_sram_req;
        mbox_sram_resp_cp: coverpoint mbox_sram_resp;
        rv_ecc_sts_cp: coverpoint rv_ecc_sts;
        clear_obf_secrets_cp: coverpoint clear_obf_secrets;
        scan_mode_cp: coverpoint scan_mode;
        cptra_obf_key_reg_cp: coverpoint cptra_obf_key_reg;
        cptra_obf_field_entropy_vld_cp: coverpoint cptra_obf_field_entropy_vld;
        cptra_obf_field_entropy_cp: coverpoint cptra_obf_field_entropy;
        obf_field_entropy_cp: coverpoint obf_field_entropy;
        cptra_obf_uds_seed_vld_cp: coverpoint cptra_obf_uds_seed_vld;
        cptra_obf_uds_seed_cp: coverpoint cptra_obf_uds_seed;
        obf_uds_seed_cp: coverpoint obf_uds_seed;
        obf_hek_seed_cp: coverpoint obf_hek_seed;
        aes_input_ready_cp: coverpoint aes_input_ready;
        aes_output_valid_cp: coverpoint aes_output_valid;
        aes_status_idle_cp: coverpoint aes_status_idle;
        aes_req_dv_cp: coverpoint aes_req_dv;
        aes_req_hold_cp: coverpoint aes_req_hold;
        aes_req_data_cp: coverpoint aes_req_data;
        aes_rdata_cp: coverpoint aes_rdata;
        aes_error_cp: coverpoint aes_error;

        kv_read_read_entry_cp:   coverpoint kv_read.read_entry;
        kv_read_read_offset_cp:  coverpoint kv_read.read_offset;
        kv_rd_resp_error_cp:     coverpoint kv_rd_resp.error;
        kv_rd_resp_last_cp:      coverpoint kv_rd_resp.last;
        kv_rd_resp_read_data_cp: coverpoint kv_rd_resp.read_data;

        strap_ss_caliptra_base_addr_cp: coverpoint strap_ss_caliptra_base_addr;
        strap_ss_mci_base_addr_cp: coverpoint strap_ss_mci_base_addr;
        strap_ss_recovery_ifc_base_addr_cp: coverpoint strap_ss_recovery_ifc_base_addr;
        strap_ss_external_staging_area_base_addr_cp: coverpoint strap_ss_external_staging_area_base_addr;
        strap_ss_otp_fc_base_addr_cp: coverpoint strap_ss_otp_fc_base_addr;
        strap_ss_uds_seed_base_addr_cp: coverpoint strap_ss_uds_seed_base_addr;
        strap_ss_key_release_base_addr_cp: coverpoint strap_ss_key_release_base_addr;
        strap_ss_key_release_key_size_cp: coverpoint strap_ss_key_release_key_size;
        strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_cp: coverpoint strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset;
        strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_cp: coverpoint strap_ss_num_of_prod_debug_unlock_auth_pk_hashes;
        strap_ss_caliptra_dma_axi_user_cp: coverpoint strap_ss_caliptra_dma_axi_user;
        strap_ss_strap_generic_0_cp: coverpoint strap_ss_strap_generic_0;
        strap_ss_strap_generic_1_cp: coverpoint strap_ss_strap_generic_1;
        strap_ss_strap_generic_2_cp: coverpoint strap_ss_strap_generic_2;
        strap_ss_strap_generic_3_cp: coverpoint strap_ss_strap_generic_3;
        ss_debug_intent_cp: coverpoint ss_debug_intent;
        cptra_ss_debug_intent_cp: coverpoint cptra_ss_debug_intent;
        ss_dbg_manuf_enable_cp: coverpoint ss_dbg_manuf_enable;
        ss_soc_dbg_unlock_level_cp: coverpoint ss_soc_dbg_unlock_level {
            wildcard bins bit0   = {64'b???????????????????????????????????????????????????????????????1};
            wildcard bins bit1   = {64'b??????????????????????????????????????????????????????????????1?};
            wildcard bins bit2   = {64'b?????????????????????????????????????????????????????????????1??};
            wildcard bins bit3   = {64'b????????????????????????????????????????????????????????????1???};
            wildcard bins bit4   = {64'b???????????????????????????????????????????????????????????1????};
            wildcard bins bit5   = {64'b??????????????????????????????????????????????????????????1?????};
            wildcard bins bit6   = {64'b?????????????????????????????????????????????????????????1??????};
            wildcard bins bit7   = {64'b????????????????????????????????????????????????????????1???????};
            bins byte1_active  = ss_soc_dbg_unlock_level_cp with (|(item & (64'hFF       <<  8)));
            bins byte2_active  = ss_soc_dbg_unlock_level_cp with (|(item & (64'hFF       << 16)));
            bins byte3_active  = ss_soc_dbg_unlock_level_cp with (|(item & (64'hFF       << 24)));
            bins dword1_active = ss_soc_dbg_unlock_level_cp with (|(item & (64'hFFFFFFFF << 32)));
        }
        ss_generic_fw_exec_ctrl_cp: coverpoint ss_generic_fw_exec_ctrl {
            bins byte0_active  = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<   0)));
            bins byte1_active  = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<   8)));
            bins byte2_active  = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<  16)));
            bins byte3_active  = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<  24)));
            bins byte4_active  = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<  32)));
            bins byte5_active  = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<  40)));
            bins byte6_active  = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<  48)));
            bins byte7_active  = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<  56)));
            bins byte8_active  = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<  64)));
            bins byte9_active  = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<  72)));
            bins byte10_active = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<  80)));
            bins byte11_active = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<  88)));
            bins byte12_active = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF <<  96)));
            bins byte13_active = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF << 104)));
            bins byte14_active = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF << 112)));
            bins byte15_active = ss_generic_fw_exec_ctrl_cp with (|(item & (128'hFF << 120)));
        }
        ss_ocp_lock_en_cp: coverpoint ss_ocp_lock_en;
        ss_ocp_lock_in_progress_cp: coverpoint ss_ocp_lock_in_progress;
        ss_key_release_key_size_cp: coverpoint ss_key_release_key_size {
            bins zero = {0};
            bins lt40 = {[1:39]};
            bins eq40 = {40};
            bins gt40 = {[41:65535]};
            // RTL allows reg-writes to set non-aligned values, but this violates the documented requirements and produces undefined behavior.
            // NOTE: If hardware is updated to enforce alignment on reg-writes, this should be changed to illegal_bins
            bins not_aligned_to_4 = ss_key_release_key_size_cp with (item[1:0] != 2'b00);
        }
        iccm_lock_cp: coverpoint iccm_lock;
        iccm_axs_blocked_cp: coverpoint iccm_axs_blocked;

    endgroup

    logic valid_arb_cycle;
    assign valid_arb_cycle = i_soc_ifc_arb.uc_req_dv | i_soc_ifc_arb.soc_req_dv;

    covergroup soc_ifc_arb_cov_grp @(posedge clk iff (cptra_rst_b & valid_arb_cycle));
        req_collision_cp: coverpoint i_soc_ifc_arb.req_collision;
        soc_priority_cp: coverpoint i_soc_ifc_arb.soc_priority;
        soc_has_priority_cp: coverpoint i_soc_ifc_arb.soc_has_priority;
        uc_has_priority_cp: coverpoint i_soc_ifc_arb.uc_has_priority;
        valid_mbox_req_cp: coverpoint i_soc_ifc_arb.valid_mbox_req;
        soc_mbox_addr_cp: coverpoint i_soc_ifc_arb.soc_req_data.addr inside {[MBOX_REG_START_ADDR:MBOX_REG_END_ADDR]};

        soc_req_ip_cp: coverpoint i_soc_ifc_arb.soc_req_ip;
        uc_req_ip_cp: coverpoint i_soc_ifc_arb.uc_req_ip;

        uc_mbox_reg_req_cp: coverpoint i_soc_ifc_arb.uc_mbox_reg_req;
        uc_mbox_dir_req_cp: coverpoint i_soc_ifc_arb.uc_mbox_dir_req;
        soc_mbox_req_cp: coverpoint i_soc_ifc_arb.soc_mbox_req;

        uc_reg_req_cp: coverpoint i_soc_ifc_arb.uc_reg_req;
        soc_reg_req_cp: coverpoint i_soc_ifc_arb.soc_reg_req;

        uc_sha_req_cp: coverpoint i_soc_ifc_arb.uc_sha_req;
        soc_sha_req_cp: coverpoint i_soc_ifc_arb.soc_sha_req;

        uc_dma_req_cp: coverpoint i_soc_ifc_arb.uc_dma_req;
        soc_dma_req_cp: coverpoint i_soc_ifc_arb.soc_dma_req;

        //Cover soc req to mbox addr range with and without valid pauser.
        soc_mbox_reqXvalid_mbox_req: cross soc_mbox_addr_cp, valid_mbox_req_cp;
        //Collision crosses
        collisionXuc_prioXprio_flag: cross req_collision_cp, uc_has_priority_cp, soc_priority_cp;
        collisionXsoc_prioXprio_Flag: cross req_collision_cp, soc_has_priority_cp, soc_priority_cp;
    endgroup

    covergroup soc_ifc_boot_fsm_cov_grp @(posedge clk iff cptra_rst_b);
        //FSM
        boot_fsm_ps_cp: coverpoint i_soc_ifc_boot_fsm.boot_fsm_ps;
        arc_BOOT_IDLE_BOOT_FUSE_cp: coverpoint i_soc_ifc_boot_fsm.arc_BOOT_IDLE_BOOT_FUSE;
        arc_BOOT_FUSE_BOOT_DONE_cp: coverpoint i_soc_ifc_boot_fsm.arc_BOOT_FUSE_BOOT_DONE;
        arc_BOOT_FUSE_BOOT_WAIT_cp: coverpoint i_soc_ifc_boot_fsm.arc_BOOT_FUSE_BOOT_WAIT;
        //Not a real arc - tied off to zero
        //arc_BOOT_DONE_BOOT_IDLE_cp: coverpoint i_soc_ifc_boot_fsm.arc_BOOT_DONE_BOOT_IDLE;
        arc_BOOT_DONE_BOOT_FWRST_cp: coverpoint i_soc_ifc_boot_fsm.arc_BOOT_DONE_BOOT_FWRST;
        arc_BOOT_FWRST_BOOT_WAIT_cp: coverpoint i_soc_ifc_boot_fsm.arc_BOOT_FWRST_BOOT_WAIT;
        arc_BOOT_WAIT_BOOT_DONE_cp: coverpoint i_soc_ifc_boot_fsm.arc_BOOT_WAIT_BOOT_DONE;
        arc_IDLE_cp: coverpoint i_soc_ifc_boot_fsm.arc_IDLE & ($bits(boot_fsm_state_e)'(i_soc_ifc_boot_fsm.boot_fsm_ps) != BOOT_IDLE);
        fsm_iccm_unlock_cp: coverpoint i_soc_ifc_boot_fsm.fsm_iccm_unlock;


    endgroup

    sha_fsm_state_e sha_fsm_ps;
    assign sha_fsm_ps = sha_fsm_state_e'(i_sha512_acc_top.sha_fsm_ps);

    covergroup sha512_acc_cov_grp @(posedge clk iff cptra_rst_b);
        //FSM
        sha_fsm_ps_cp: coverpoint sha_fsm_ps;
        arc_SHA_IDLE_SHA_BLOCK_0_cp: coverpoint i_sha512_acc_top.arc_SHA_IDLE_SHA_BLOCK_0;
        arc_SHA_BLOCK_0_SHA_BLOCK_N_cp: coverpoint i_sha512_acc_top.arc_SHA_BLOCK_0_SHA_BLOCK_N;
        arc_SHA_BLOCK_0_SHA_PAD0_cp: coverpoint i_sha512_acc_top.arc_SHA_BLOCK_0_SHA_PAD0;
        arc_SHA_BLOCK_N_SHA_BLOCK_N_cp: coverpoint i_sha512_acc_top.arc_SHA_BLOCK_N_SHA_BLOCK_N;
        arc_SHA_BLOCK_N_SHA_PAD0_cp: coverpoint i_sha512_acc_top.arc_SHA_BLOCK_N_SHA_PAD0;
        arc_SHA_PAD0_SHA_PAD1_cp: coverpoint i_sha512_acc_top.arc_SHA_PAD0_SHA_PAD1;
        arc_SHA_PAD0_SHA_DONE_cp: coverpoint i_sha512_acc_top.arc_SHA_PAD0_SHA_DONE;
        arc_SHA_PAD1_SHA_DONE_cp: coverpoint i_sha512_acc_top.arc_SHA_PAD1_SHA_DONE;
        arc_IDLE_cp: coverpoint (i_sha512_acc_top.arc_IDLE & (sha_fsm_ps != SHA_IDLE));

        //controls
        extra_pad_block_required_cp: coverpoint i_sha512_acc_top.extra_pad_block_required;
        num_bytes_data_cp: coverpoint i_sha512_acc_top.num_bytes_data;
        mailbox_mode_cp: coverpoint i_sha512_acc_top.mailbox_mode;
        sha_mode_cp: coverpoint i_sha512_acc_top.sha_mode {
          option.comment = "SHA Mode Encoding";
          bins MODE_SHA_384 = {2'h2};
          bins MODE_SHA_512 = {2'h3};
        }

        //crosses
        mailbox_modeXextra_pad: cross mailbox_mode_cp, extra_pad_block_required_cp;
        mailbox_modeXnum_bytes_data: cross mailbox_mode_cp, num_bytes_data_cp;
        mailbox_modeXsha_mode_cpXsha_fsm_ps: cross mailbox_mode_cp, sha_mode_cp, sha_fsm_ps_cp;

    endgroup

    mbox_fsm_state_e mbox_fsm_ps;
    assign mbox_fsm_ps = mbox_fsm_state_e'(i_mbox.mbox_fsm_ps);

    covergroup mbox_cov_grp @(posedge clk iff cptra_rst_b);
        //FSM
        mbox_fsm_ps_cp: coverpoint mbox_fsm_ps;
        arc_FORCE_MBOX_UNLOCK_cp: coverpoint i_mbox.arc_FORCE_MBOX_UNLOCK;
        arc_MBOX_IDLE_MBOX_RDY_FOR_CMD_cp: coverpoint i_mbox.arc_MBOX_IDLE_MBOX_RDY_FOR_CMD;
        arc_MBOX_RDY_FOR_CMD_MBOX_RDY_FOR_DLEN_cp: coverpoint i_mbox.arc_MBOX_RDY_FOR_CMD_MBOX_RDY_FOR_DLEN;
        arc_MBOX_RDY_FOR_DLEN_MBOX_RDY_FOR_DATA_cp: coverpoint i_mbox.arc_MBOX_RDY_FOR_DLEN_MBOX_RDY_FOR_DATA;
        arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC_cp: coverpoint i_mbox.arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_UC;
        arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC_cp: coverpoint i_mbox.arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_SOC;
        arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_TAP_cp: coverpoint i_mbox.arc_MBOX_RDY_FOR_DATA_MBOX_EXECUTE_TAP;
        arc_MBOX_EXECUTE_UC_MBOX_IDLE_cp: coverpoint i_mbox.arc_MBOX_EXECUTE_UC_MBOX_IDLE;
        arc_MBOX_EXECUTE_SOC_MBOX_IDLE_cp: coverpoint i_mbox.arc_MBOX_EXECUTE_SOC_MBOX_IDLE;
        arc_MBOX_EXECUTE_TAP_MBOX_IDLE_cp: coverpoint i_mbox.arc_MBOX_EXECUTE_TAP_MBOX_IDLE;
        arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC_cp: coverpoint i_mbox.arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_SOC;
        arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_TAP_cp: coverpoint i_mbox.arc_MBOX_EXECUTE_UC_MBOX_EXECUTE_TAP;
        arc_MBOX_EXECUTE_SOC_MBOX_EXECUTE_UC_cp: coverpoint i_mbox.arc_MBOX_EXECUTE_SOC_MBOX_EXECUTE_UC;
        arc_MBOX_EXECUTE_TAP_MBOX_EXECUTE_UC_cp: coverpoint i_mbox.arc_MBOX_EXECUTE_TAP_MBOX_EXECUTE_UC;
        arc_MBOX_RDY_FOR_CMD_MBOX_ERROR_cp: coverpoint i_mbox.arc_MBOX_RDY_FOR_CMD_MBOX_ERROR;
        arc_MBOX_RDY_FOR_DLEN_MBOX_ERROR_cp: coverpoint i_mbox.arc_MBOX_RDY_FOR_DLEN_MBOX_ERROR;
        arc_MBOX_RDY_FOR_DATA_MBOX_ERROR_cp: coverpoint i_mbox.arc_MBOX_RDY_FOR_DATA_MBOX_ERROR;
        arc_MBOX_EXECUTE_UC_MBOX_ERROR_cp: coverpoint i_mbox.arc_MBOX_EXECUTE_UC_MBOX_ERROR;
        arc_MBOX_EXECUTE_SOC_MBOX_ERROR_cp: coverpoint i_mbox.arc_MBOX_EXECUTE_SOC_MBOX_ERROR;
        arc_MBOX_EXECUTE_TAP_MBOX_ERROR_cp: coverpoint i_mbox.arc_MBOX_EXECUTE_TAP_MBOX_ERROR;

        //controls
        soc_has_lock_cp: coverpoint i_mbox.soc_has_lock;
        uc_has_lock_cp: coverpoint i_mbox.uc_has_lock;
        tap_has_lock_cp: coverpoint i_mbox.tap_has_lock;
        mask_rdata_cp: coverpoint i_mbox.mask_rdata;
        dlen_in_dws_cp: coverpoint i_mbox.dlen_in_dws {
          bins zero = {0};
          bins one = {1};
          bins range[32] = {[2:CPTRA_MBOX_SIZE_DWORDS-2]};
          bins almost_full = {CPTRA_MBOX_SIZE_DWORDS-1};
          bins full = {CPTRA_MBOX_SIZE_DWORDS};}

        sram_single_ecc_error_cp: coverpoint i_mbox.sram_single_ecc_error;
        sram_double_ecc_error_cp: coverpoint i_mbox.sram_double_ecc_error;

        //req hold varieties
        req_hold0_cp: coverpoint (i_mbox.dir_req_dv_q & ~i_mbox.sha_sram_req_dv & ~i_mbox.req_data_write);
        req_hold1_cp: coverpoint (i_mbox.dir_req_dv & ~i_mbox.dir_req_rd_phase & i_mbox.sha_sram_req_dv);
        req_hold2_cp: coverpoint i_mbox.req_dv & (i_mbox.hwif_out.mbox_dataout.dataout.swacc & i_mbox.mbox_protocol_sram_rd_f);
        //sha_sram_hold_cp: coverpoint i_mbox.sha_sram_hold;

        //special scenarios - only care about bin of 1
        dlen_gt_mbox_size_cp: coverpoint i_mbox.hwif_out.mbox_dlen.length.value > CPTRA_MBOX_SIZE_BYTES {
            option.comment = "DLEN is programmed greater than mailbox size";
            bins one = {1};}
        req_wrptr_gt_dlen_cp: coverpoint (mbox_fsm_ps == MBOX_RDY_FOR_DATA) & (i_mbox.mbox_wrptr > i_mbox.dlen_in_dws) {
            option.comment = "Requester caused write pointer to increment past DLEN";
            bins one = {1};}
        resp_wrptr_gt_dlen_cp: coverpoint (mbox_fsm_ps inside {MBOX_EXECUTE_UC,MBOX_EXECUTE_SOC}) & (i_mbox.mbox_wrptr > i_mbox.dlen_in_dws) {
            option.comment = "Receiver caused write pointer to increment past DLEN";
            bins one = {1};}
        wrptr_rollover_cp: coverpoint i_mbox.inc_wrptr & ~i_mbox.wrptr_inc_valid {
            option.comment = "Write pointer tried to increment past mailbox size";
            bins one = {1};}
        rdptr_gt_dlen_cp: coverpoint i_mbox.inc_rdptr & ~(i_mbox.mbox_rdptr <= i_mbox.dlen_in_dws) {
            option.comment = "Read pointer tried to increment passed DLEN";
            bins one = {1};}
        rdptr_rollover_cp: coverpoint i_mbox.inc_rdptr & ~(i_mbox.mbox_rdptr < (CPTRA_MBOX_SIZE_DWORDS-1)) {
            option.comment = "Read pointer tried to increment passed mailbox size";
            bins one = {1};}

    endgroup

  covergroup axi_dma_cov_grp @(posedge clk iff cptra_rst_b);
    //DMA Accesses in progress
    AHBtoAXI_ip_cp: coverpoint (dma_ctrl_fsm_ps != DMA_IDLE) &
                               (dma_rd_route == axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE) &
                               (dma_wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO) {
                                  option.comment = "DMA Access: AHB FIFO data sent to AXI location";
                                  bins one = {1};}
    AXItoAHB_ip_cp: coverpoint (dma_ctrl_fsm_ps != DMA_IDLE) &
                               (dma_rd_route == axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO) &
                               (dma_wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE) {
                                  option.comment = "DMA Access: AXI read into AHB FIFO";
                                  bins one = {1};}
    AXItoAXI_ip_cp: coverpoint (dma_ctrl_fsm_ps != DMA_IDLE) &
                               (dma_rd_route == axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR) &
                               (dma_wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD) {
                                  option.comment = "DMA Access: AXI to AXI";
                                  bins one = {1};}
    MBOXtoAXI_ip_cp: coverpoint (dma_ctrl_fsm_ps != DMA_IDLE) &
                                (dma_rd_route == axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE) &
                                (dma_wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX) {
                                  option.comment = "DMA Access: MBOX data sent to AXI location";
                                  bins one = {1};}
    AXItoMBOX_ip_cp: coverpoint (dma_ctrl_fsm_ps != DMA_IDLE) &
                                (dma_rd_route == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX) &
                                (dma_wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE) {
                                  option.comment = "DMA Access: AXI read into MBOX";
                                  bins one = {1};}
    AXItoSHA_ip_cp: coverpoint (sha_fsm_ps != SHA_IDLE) & 
                               (i_sha512_acc_top.hwif_out.USER.USER.value == soc_ifc_reg_hwif_out.SS_CALIPTRA_DMA_AXI_USER.user.value) &
                               (dma_ctrl_fsm_ps != DMA_IDLE) &
                               (dma_rd_route == axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR) &
                               (dma_wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD) {
                                  option.comment = "DMA Access: AXI to SHA";
                                  bins one = {1};}

    //Other accesses to cross with
    MBOX_ip_cp: coverpoint (mbox_fsm_ps != MBOX_IDLE)  {
      option.comment = "Mailbox access in progress";
      bins one = {1};}
    TRNG_ip_cp: coverpoint (trng_req)  {
      option.comment = "TRNG access in progress";
      bins one = {1};}
    REG_ip_cp: coverpoint (soc_ifc_reg_req_dv)  {
      option.comment = "SOC Reg access in progress";
      bins one = {1};}

      AHBtoAXIxMailbox: cross AHBtoAXI_ip_cp, MBOX_ip_cp;
      AHBtoAXIxTRNG: cross AHBtoAXI_ip_cp, TRNG_ip_cp;
      AHBtoAXIxREG: cross AHBtoAXI_ip_cp, REG_ip_cp;
      MBOXtoAXIxMailbox: cross MBOXtoAXI_ip_cp, MBOX_ip_cp;
      MBOXtoAXIxTRNG: cross MBOXtoAXI_ip_cp, TRNG_ip_cp;
      MBOXtoAXIxREG: cross MBOXtoAXI_ip_cp, REG_ip_cp;
      AXItoAXIxMailbox: cross AXItoAXI_ip_cp, MBOX_ip_cp;
      AXItoAXIxTRNG: cross AXItoAXI_ip_cp, TRNG_ip_cp;
      AXItoAXIxREG: cross AXItoAXI_ip_cp, REG_ip_cp;
      AXItoAHBxMailbox: cross AXItoAHB_ip_cp, MBOX_ip_cp;
      AXItoAHBxTRNG: cross AXItoAHB_ip_cp, TRNG_ip_cp;
      AXItoAHBxREG: cross AXItoAHB_ip_cp, REG_ip_cp;
      AXItoMBOXxMailbox: cross AXItoMBOX_ip_cp, MBOX_ip_cp;
      AXItoMBOXxTRNG: cross AXItoMBOX_ip_cp, TRNG_ip_cp;
      AXItoMBOXxREG: cross AXItoMBOX_ip_cp, REG_ip_cp;
      AXItoSHAxMailbox: cross AXItoSHA_ip_cp, MBOX_ip_cp;
      AXItoSHAxTRNG: cross AXItoSHA_ip_cp, TRNG_ip_cp;
      AXItoSHAxREG: cross AXItoSHA_ip_cp, REG_ip_cp;
  endgroup

    soc_ifc_top_cov_grp soc_ifc_top_cov_grp1 = new();
    soc_ifc_arb_cov_grp soc_ifc_arb_cov_grp1 = new();
    soc_ifc_boot_fsm_cov_grp soc_ifc_boot_fsm_cov_grp1 = new();
    sha512_acc_cov_grp sha512_acc_cov_grp1 = new();
    mbox_cov_grp mbox_cov_grp1 = new();
    axi_dma_cov_grp axi_dma_cov_grp1 = new();

/*  -- Working Reference -- 
    for(genvar i = 0; i < 4; i++) begin : fuse_runtime_svn_blk
      covergroup soc_ifc_fuse_runtime_svn_cg @(posedge clk);
        option.comment =  {"fuse_runtime_svn", "_cp"};
        coverpoint i_soc_ifc_reg.field_storage.fuse_runtime_svn[i]; 
      endgroup
      soc_ifc_fuse_runtime_svn_cg fuse_runtime_svn_cg = new();
    end 
*/   




  // ------------------------------------------------------------------- 
  // begin SCRIPT_OUTPUT
  // ------------------------------------------------------------------- 


  // ------------------- COVERGROUP related signals & assigns -------------------

  logic          hit_CPTRA_HW_ERROR_FATAL;
  logic [3:0]    bus_CPTRA_HW_ERROR_FATAL;
  logic [31:0]   full_addr_CPTRA_HW_ERROR_FATAL = `CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL;

  logic          hit_CPTRA_HW_ERROR_NON_FATAL;
  logic [3:0]    bus_CPTRA_HW_ERROR_NON_FATAL;
  logic [31:0]   full_addr_CPTRA_HW_ERROR_NON_FATAL = `CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL;

  logic          hit_CPTRA_FW_ERROR_FATAL;
  logic [3:0]    bus_CPTRA_FW_ERROR_FATAL;
  logic [31:0]   full_addr_CPTRA_FW_ERROR_FATAL = `CLP_SOC_IFC_REG_CPTRA_FW_ERROR_FATAL;

  logic          hit_CPTRA_FW_ERROR_NON_FATAL;
  logic [3:0]    bus_CPTRA_FW_ERROR_NON_FATAL;
  logic [31:0]   full_addr_CPTRA_FW_ERROR_NON_FATAL = `CLP_SOC_IFC_REG_CPTRA_FW_ERROR_NON_FATAL;

  logic          hit_CPTRA_HW_ERROR_ENC;
  logic [3:0]    bus_CPTRA_HW_ERROR_ENC;
  logic [31:0]   full_addr_CPTRA_HW_ERROR_ENC = `CLP_SOC_IFC_REG_CPTRA_HW_ERROR_ENC;

  logic          hit_CPTRA_FW_ERROR_ENC;
  logic [3:0]    bus_CPTRA_FW_ERROR_ENC;
  logic [31:0]   full_addr_CPTRA_FW_ERROR_ENC = `CLP_SOC_IFC_REG_CPTRA_FW_ERROR_ENC;

  logic          hit_CPTRA_FW_EXTENDED_ERROR_INFO[0:7];
  logic [3:0]    bus_CPTRA_FW_EXTENDED_ERROR_INFO[0:7];
  logic [31:0]   full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[0:7];
  assign         full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[0] = `CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0;
  assign         full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[1] = `CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_1;
  assign         full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[2] = `CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_2;
  assign         full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[3] = `CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_3;
  assign         full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[4] = `CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_4;
  assign         full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[5] = `CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_5;
  assign         full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[6] = `CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_6;
  assign         full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[7] = `CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_7;

  logic          hit_CPTRA_BOOT_STATUS;
  logic [3:0]    bus_CPTRA_BOOT_STATUS;
  logic [31:0]   full_addr_CPTRA_BOOT_STATUS = `CLP_SOC_IFC_REG_CPTRA_BOOT_STATUS;

  logic          hit_CPTRA_FLOW_STATUS;
  logic [3:0]    bus_CPTRA_FLOW_STATUS;
  logic [31:0]   full_addr_CPTRA_FLOW_STATUS = `CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS;

  logic          hit_CPTRA_RESET_REASON;
  logic [3:0]    bus_CPTRA_RESET_REASON;
  logic [31:0]   full_addr_CPTRA_RESET_REASON = `CLP_SOC_IFC_REG_CPTRA_RESET_REASON;

  // logic          hit_CPTRA_SECURITY_STATE;
  // logic [3:0]    bus_CPTRA_SECURITY_STATE;
  // logic [31:0]   full_addr_CPTRA_SECURITY_STATE = `CLP_SOC_IFC_REG_CPTRA_SECURITY_STATE;

  logic          hit_CPTRA_MBOX_VALID_AXI_USER[0:4];
  logic [3:0]    bus_CPTRA_MBOX_VALID_AXI_USER[0:4];
  logic [31:0]   full_addr_CPTRA_MBOX_VALID_AXI_USER[0:4];
  assign         full_addr_CPTRA_MBOX_VALID_AXI_USER[0] = `CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0;
  assign         full_addr_CPTRA_MBOX_VALID_AXI_USER[1] = `CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_1;
  assign         full_addr_CPTRA_MBOX_VALID_AXI_USER[2] = `CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_2;
  assign         full_addr_CPTRA_MBOX_VALID_AXI_USER[3] = `CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_3;
  assign         full_addr_CPTRA_MBOX_VALID_AXI_USER[4] = `CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_4;

  logic          hit_CPTRA_MBOX_AXI_USER_LOCK[0:4];
  logic [3:0]    bus_CPTRA_MBOX_AXI_USER_LOCK[0:4];
  logic [31:0]   full_addr_CPTRA_MBOX_AXI_USER_LOCK[0:4];
  assign         full_addr_CPTRA_MBOX_AXI_USER_LOCK[0] = `CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0;
  assign         full_addr_CPTRA_MBOX_AXI_USER_LOCK[1] = `CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_1;
  assign         full_addr_CPTRA_MBOX_AXI_USER_LOCK[2] = `CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_2;
  assign         full_addr_CPTRA_MBOX_AXI_USER_LOCK[3] = `CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_3;
  assign         full_addr_CPTRA_MBOX_AXI_USER_LOCK[4] = `CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_4;

  logic          hit_CPTRA_TRNG_VALID_AXI_USER;
  logic [3:0]    bus_CPTRA_TRNG_VALID_AXI_USER;
  logic [31:0]   full_addr_CPTRA_TRNG_VALID_AXI_USER = `CLP_SOC_IFC_REG_CPTRA_TRNG_VALID_AXI_USER;

  logic          hit_CPTRA_TRNG_AXI_USER_LOCK;
  logic [3:0]    bus_CPTRA_TRNG_AXI_USER_LOCK;
  logic [31:0]   full_addr_CPTRA_TRNG_AXI_USER_LOCK = `CLP_SOC_IFC_REG_CPTRA_TRNG_AXI_USER_LOCK;

  logic          hit_CPTRA_TRNG_DATA[0:11];
  logic [3:0]    bus_CPTRA_TRNG_DATA[0:11];
  logic [31:0]   full_addr_CPTRA_TRNG_DATA[0:11];
  assign         full_addr_CPTRA_TRNG_DATA[0] = `CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_0;
  assign         full_addr_CPTRA_TRNG_DATA[1] = `CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_1;
  assign         full_addr_CPTRA_TRNG_DATA[2] = `CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_2;
  assign         full_addr_CPTRA_TRNG_DATA[3] = `CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_3;
  assign         full_addr_CPTRA_TRNG_DATA[4] = `CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_4;
  assign         full_addr_CPTRA_TRNG_DATA[5] = `CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_5;
  assign         full_addr_CPTRA_TRNG_DATA[6] = `CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_6;
  assign         full_addr_CPTRA_TRNG_DATA[7] = `CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_7;
  assign         full_addr_CPTRA_TRNG_DATA[8] = `CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_8;
  assign         full_addr_CPTRA_TRNG_DATA[9] = `CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_9;
  assign         full_addr_CPTRA_TRNG_DATA[10] = `CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_10;
  assign         full_addr_CPTRA_TRNG_DATA[11] = `CLP_SOC_IFC_REG_CPTRA_TRNG_DATA_11;

  logic          hit_CPTRA_TRNG_CTRL;
  logic [3:0]    bus_CPTRA_TRNG_CTRL;
  logic [31:0]   full_addr_CPTRA_TRNG_CTRL = `CLP_SOC_IFC_REG_CPTRA_TRNG_CTRL;

  logic          hit_CPTRA_TRNG_STATUS;
  logic [3:0]    bus_CPTRA_TRNG_STATUS;
  logic [31:0]   full_addr_CPTRA_TRNG_STATUS = `CLP_SOC_IFC_REG_CPTRA_TRNG_STATUS;

  logic          hit_CPTRA_FUSE_WR_DONE;
  logic [3:0]    bus_CPTRA_FUSE_WR_DONE;
  logic [31:0]   full_addr_CPTRA_FUSE_WR_DONE = `CLP_SOC_IFC_REG_CPTRA_FUSE_WR_DONE;

  logic          hit_CPTRA_TIMER_CONFIG;
  logic [3:0]    bus_CPTRA_TIMER_CONFIG;
  logic [31:0]   full_addr_CPTRA_TIMER_CONFIG = `CLP_SOC_IFC_REG_CPTRA_TIMER_CONFIG;

  logic          hit_CPTRA_BOOTFSM_GO;
  logic [3:0]    bus_CPTRA_BOOTFSM_GO;
  logic [31:0]   full_addr_CPTRA_BOOTFSM_GO = `CLP_SOC_IFC_REG_CPTRA_BOOTFSM_GO;

  logic          hit_CPTRA_DBG_MANUF_SERVICE_REG;
  logic [3:0]    bus_CPTRA_DBG_MANUF_SERVICE_REG;
  logic [31:0]   full_addr_CPTRA_DBG_MANUF_SERVICE_REG = `CLP_SOC_IFC_REG_CPTRA_DBG_MANUF_SERVICE_REG;

  logic          hit_CPTRA_CLK_GATING_EN;
  logic [3:0]    bus_CPTRA_CLK_GATING_EN;
  logic [31:0]   full_addr_CPTRA_CLK_GATING_EN = `CLP_SOC_IFC_REG_CPTRA_CLK_GATING_EN;

  logic          hit_CPTRA_GENERIC_INPUT_WIRES[0:1];
  logic [3:0]    bus_CPTRA_GENERIC_INPUT_WIRES[0:1];
  logic [31:0]   full_addr_CPTRA_GENERIC_INPUT_WIRES[0:1];
  assign         full_addr_CPTRA_GENERIC_INPUT_WIRES[0] = `CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0;
  assign         full_addr_CPTRA_GENERIC_INPUT_WIRES[1] = `CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_1;

  logic          hit_CPTRA_GENERIC_OUTPUT_WIRES[0:1];
  logic [3:0]    bus_CPTRA_GENERIC_OUTPUT_WIRES[0:1];
  logic [31:0]   full_addr_CPTRA_GENERIC_OUTPUT_WIRES[0:1];
  assign         full_addr_CPTRA_GENERIC_OUTPUT_WIRES[0] = `CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0;
  assign         full_addr_CPTRA_GENERIC_OUTPUT_WIRES[1] = `CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1;

  // logic          hit_CPTRA_HW_REV_ID;
  // logic [3:0]    bus_CPTRA_HW_REV_ID;
  // logic [31:0]   full_addr_CPTRA_HW_REV_ID = `CLP_SOC_IFC_REG_CPTRA_HW_REV_ID;

  logic          hit_CPTRA_FW_REV_ID[0:1];
  logic [3:0]    bus_CPTRA_FW_REV_ID[0:1];
  logic [31:0]   full_addr_CPTRA_FW_REV_ID[0:1];
  assign         full_addr_CPTRA_FW_REV_ID[0] = `CLP_SOC_IFC_REG_CPTRA_FW_REV_ID_0;
  assign         full_addr_CPTRA_FW_REV_ID[1] = `CLP_SOC_IFC_REG_CPTRA_FW_REV_ID_1;

  // logic          hit_CPTRA_HW_CONFIG;
  // logic [3:0]    bus_CPTRA_HW_CONFIG;
  // logic [31:0]   full_addr_CPTRA_HW_CONFIG = `CLP_SOC_IFC_REG_CPTRA_HW_CONFIG;

  logic          hit_CPTRA_WDT_TIMER1_EN;
  logic [3:0]    bus_CPTRA_WDT_TIMER1_EN;
  logic [31:0]   full_addr_CPTRA_WDT_TIMER1_EN = `CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_EN;

  logic          hit_CPTRA_WDT_TIMER1_CTRL;
  logic [3:0]    bus_CPTRA_WDT_TIMER1_CTRL;
  logic [31:0]   full_addr_CPTRA_WDT_TIMER1_CTRL = `CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_CTRL;

  logic          hit_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[0:1];
  logic [3:0]    bus_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[0:1];
  logic [31:0]   full_addr_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[0:1];
  assign         full_addr_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[0] = `CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_0;
  assign         full_addr_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[1] = `CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_1;

  logic          hit_CPTRA_WDT_TIMER2_EN;
  logic [3:0]    bus_CPTRA_WDT_TIMER2_EN;
  logic [31:0]   full_addr_CPTRA_WDT_TIMER2_EN = `CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_EN;

  logic          hit_CPTRA_WDT_TIMER2_CTRL;
  logic [3:0]    bus_CPTRA_WDT_TIMER2_CTRL;
  logic [31:0]   full_addr_CPTRA_WDT_TIMER2_CTRL = `CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_CTRL;

  logic          hit_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[0:1];
  logic [3:0]    bus_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[0:1];
  logic [31:0]   full_addr_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[0:1];
  assign         full_addr_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[0] = `CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_0;
  assign         full_addr_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[1] = `CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_1;

  logic          hit_CPTRA_WDT_STATUS;
  logic [3:0]    bus_CPTRA_WDT_STATUS;
  logic [31:0]   full_addr_CPTRA_WDT_STATUS = `CLP_SOC_IFC_REG_CPTRA_WDT_STATUS;

  logic          hit_CPTRA_FUSE_VALID_AXI_USER;
  logic [3:0]    bus_CPTRA_FUSE_VALID_AXI_USER;
  logic [31:0]   full_addr_CPTRA_FUSE_VALID_AXI_USER = `CLP_SOC_IFC_REG_CPTRA_FUSE_VALID_AXI_USER;

  logic          hit_CPTRA_FUSE_AXI_USER_LOCK;
  logic [3:0]    bus_CPTRA_FUSE_AXI_USER_LOCK;
  logic [31:0]   full_addr_CPTRA_FUSE_AXI_USER_LOCK = `CLP_SOC_IFC_REG_CPTRA_FUSE_AXI_USER_LOCK;

  logic          hit_CPTRA_WDT_CFG[0:1];
  logic [3:0]    bus_CPTRA_WDT_CFG[0:1];
  logic [31:0]   full_addr_CPTRA_WDT_CFG[0:1];
  assign         full_addr_CPTRA_WDT_CFG[0] = `CLP_SOC_IFC_REG_CPTRA_WDT_CFG_0;
  assign         full_addr_CPTRA_WDT_CFG[1] = `CLP_SOC_IFC_REG_CPTRA_WDT_CFG_1;

  logic          hit_CPTRA_iTRNG_ENTROPY_CONFIG_0;
  logic [3:0]    bus_CPTRA_iTRNG_ENTROPY_CONFIG_0;
  logic [31:0]   full_addr_CPTRA_iTRNG_ENTROPY_CONFIG_0 = `CLP_SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_0;

  logic          hit_CPTRA_iTRNG_ENTROPY_CONFIG_1;
  logic [3:0]    bus_CPTRA_iTRNG_ENTROPY_CONFIG_1;
  logic [31:0]   full_addr_CPTRA_iTRNG_ENTROPY_CONFIG_1 = `CLP_SOC_IFC_REG_CPTRA_ITRNG_ENTROPY_CONFIG_1;

  logic          hit_CPTRA_RSVD_REG[0:1];
  logic [3:0]    bus_CPTRA_RSVD_REG[0:1];
  logic [31:0]   full_addr_CPTRA_RSVD_REG[0:1];
  assign         full_addr_CPTRA_RSVD_REG[0] = `CLP_SOC_IFC_REG_CPTRA_RSVD_REG_0;
  assign         full_addr_CPTRA_RSVD_REG[1] = `CLP_SOC_IFC_REG_CPTRA_RSVD_REG_1;

  logic          hit_CPTRA_HW_CAPABILITIES;
  logic [3:0]    bus_CPTRA_HW_CAPABILITIES;
  logic [31:0]   full_addr_CPTRA_HW_CAPABILITIES = `CLP_SOC_IFC_REG_CPTRA_HW_CAPABILITIES;

  logic          hit_CPTRA_FW_CAPABILITIES;
  logic [3:0]    bus_CPTRA_FW_CAPABILITIES;
  logic [31:0]   full_addr_CPTRA_FW_CAPABILITIES = `CLP_SOC_IFC_REG_CPTRA_FW_CAPABILITIES;

  logic          hit_CPTRA_CAP_LOCK;
  logic [3:0]    bus_CPTRA_CAP_LOCK;
  logic [31:0]   full_addr_CPTRA_CAP_LOCK = `CLP_SOC_IFC_REG_CPTRA_CAP_LOCK;

  logic          hit_CPTRA_OWNER_PK_HASH[0:11];
  logic [3:0]    bus_CPTRA_OWNER_PK_HASH[0:11];
  logic [31:0]   full_addr_CPTRA_OWNER_PK_HASH[0:11];
  assign         full_addr_CPTRA_OWNER_PK_HASH[0] = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_0;
  assign         full_addr_CPTRA_OWNER_PK_HASH[1] = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_1;
  assign         full_addr_CPTRA_OWNER_PK_HASH[2] = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_2;
  assign         full_addr_CPTRA_OWNER_PK_HASH[3] = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_3;
  assign         full_addr_CPTRA_OWNER_PK_HASH[4] = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_4;
  assign         full_addr_CPTRA_OWNER_PK_HASH[5] = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_5;
  assign         full_addr_CPTRA_OWNER_PK_HASH[6] = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_6;
  assign         full_addr_CPTRA_OWNER_PK_HASH[7] = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_7;
  assign         full_addr_CPTRA_OWNER_PK_HASH[8] = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_8;
  assign         full_addr_CPTRA_OWNER_PK_HASH[9] = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_9;
  assign         full_addr_CPTRA_OWNER_PK_HASH[10] = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_10;
  assign         full_addr_CPTRA_OWNER_PK_HASH[11] = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_11;

  logic          hit_CPTRA_OWNER_PK_HASH_LOCK;
  logic [3:0]    bus_CPTRA_OWNER_PK_HASH_LOCK;
  logic [31:0]   full_addr_CPTRA_OWNER_PK_HASH_LOCK = `CLP_SOC_IFC_REG_CPTRA_OWNER_PK_HASH_LOCK;

  logic          hit_fuse_uds_seed[0:15];
  logic [3:0]    bus_fuse_uds_seed[0:15];
  logic [31:0]   full_addr_fuse_uds_seed[0:15];
  assign         full_addr_fuse_uds_seed[0] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_0;
  assign         full_addr_fuse_uds_seed[1] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_1;
  assign         full_addr_fuse_uds_seed[2] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_2;
  assign         full_addr_fuse_uds_seed[3] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_3;
  assign         full_addr_fuse_uds_seed[4] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_4;
  assign         full_addr_fuse_uds_seed[5] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_5;
  assign         full_addr_fuse_uds_seed[6] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_6;
  assign         full_addr_fuse_uds_seed[7] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_7;
  assign         full_addr_fuse_uds_seed[8] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_8;
  assign         full_addr_fuse_uds_seed[9] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_9;
  assign         full_addr_fuse_uds_seed[10] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_10;
  assign         full_addr_fuse_uds_seed[11] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_11;
  assign         full_addr_fuse_uds_seed[12] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_12;
  assign         full_addr_fuse_uds_seed[13] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_13;
  assign         full_addr_fuse_uds_seed[14] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_14;
  assign         full_addr_fuse_uds_seed[15] = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_15;

  logic          hit_fuse_field_entropy[0:7];
  logic [3:0]    bus_fuse_field_entropy[0:7];
  logic [31:0]   full_addr_fuse_field_entropy[0:7];
  assign         full_addr_fuse_field_entropy[0] = `CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_0;
  assign         full_addr_fuse_field_entropy[1] = `CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_1;
  assign         full_addr_fuse_field_entropy[2] = `CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_2;
  assign         full_addr_fuse_field_entropy[3] = `CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_3;
  assign         full_addr_fuse_field_entropy[4] = `CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_4;
  assign         full_addr_fuse_field_entropy[5] = `CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_5;
  assign         full_addr_fuse_field_entropy[6] = `CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_6;
  assign         full_addr_fuse_field_entropy[7] = `CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_7;

  logic          hit_fuse_vendor_pk_hash[0:11];
  logic [3:0]    bus_fuse_vendor_pk_hash[0:11];
  logic [31:0]   full_addr_fuse_vendor_pk_hash[0:11];
  assign         full_addr_fuse_vendor_pk_hash[0] = `CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_0;
  assign         full_addr_fuse_vendor_pk_hash[1] = `CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_1;
  assign         full_addr_fuse_vendor_pk_hash[2] = `CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_2;
  assign         full_addr_fuse_vendor_pk_hash[3] = `CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_3;
  assign         full_addr_fuse_vendor_pk_hash[4] = `CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_4;
  assign         full_addr_fuse_vendor_pk_hash[5] = `CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_5;
  assign         full_addr_fuse_vendor_pk_hash[6] = `CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_6;
  assign         full_addr_fuse_vendor_pk_hash[7] = `CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_7;
  assign         full_addr_fuse_vendor_pk_hash[8] = `CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_8;
  assign         full_addr_fuse_vendor_pk_hash[9] = `CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_9;
  assign         full_addr_fuse_vendor_pk_hash[10] = `CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_10;
  assign         full_addr_fuse_vendor_pk_hash[11] = `CLP_SOC_IFC_REG_FUSE_VENDOR_PK_HASH_11;

  logic          hit_fuse_ecc_revocation;
  logic [3:0]    bus_fuse_ecc_revocation;
  logic [31:0]   full_addr_fuse_ecc_revocation = `CLP_SOC_IFC_REG_FUSE_ECC_REVOCATION;

  logic          hit_fuse_fmc_key_manifest_svn;
  logic [3:0]    bus_fuse_fmc_key_manifest_svn;
  logic [31:0]   full_addr_fuse_fmc_key_manifest_svn = `CLP_SOC_IFC_REG_FUSE_FMC_KEY_MANIFEST_SVN;

  logic          hit_fuse_runtime_svn[0:3];
  logic [3:0]    bus_fuse_runtime_svn[0:3];
  logic [31:0]   full_addr_fuse_runtime_svn[0:3];
  assign         full_addr_fuse_runtime_svn[0] = `CLP_SOC_IFC_REG_FUSE_RUNTIME_SVN_0;
  assign         full_addr_fuse_runtime_svn[1] = `CLP_SOC_IFC_REG_FUSE_RUNTIME_SVN_1;
  assign         full_addr_fuse_runtime_svn[2] = `CLP_SOC_IFC_REG_FUSE_RUNTIME_SVN_2;
  assign         full_addr_fuse_runtime_svn[3] = `CLP_SOC_IFC_REG_FUSE_RUNTIME_SVN_3;

  logic          hit_fuse_anti_rollback_disable;
  logic [3:0]    bus_fuse_anti_rollback_disable;
  logic [31:0]   full_addr_fuse_anti_rollback_disable = `CLP_SOC_IFC_REG_FUSE_ANTI_ROLLBACK_DISABLE;

  logic          hit_fuse_idevid_cert_attr[0:23];
  logic [3:0]    bus_fuse_idevid_cert_attr[0:23];
  logic [31:0]   full_addr_fuse_idevid_cert_attr[0:23];
  assign         full_addr_fuse_idevid_cert_attr[0] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_0;
  assign         full_addr_fuse_idevid_cert_attr[1] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_1;
  assign         full_addr_fuse_idevid_cert_attr[2] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_2;
  assign         full_addr_fuse_idevid_cert_attr[3] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_3;
  assign         full_addr_fuse_idevid_cert_attr[4] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_4;
  assign         full_addr_fuse_idevid_cert_attr[5] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_5;
  assign         full_addr_fuse_idevid_cert_attr[6] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_6;
  assign         full_addr_fuse_idevid_cert_attr[7] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_7;
  assign         full_addr_fuse_idevid_cert_attr[8] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_8;
  assign         full_addr_fuse_idevid_cert_attr[9] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_9;
  assign         full_addr_fuse_idevid_cert_attr[10] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_10;
  assign         full_addr_fuse_idevid_cert_attr[11] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_11;
  assign         full_addr_fuse_idevid_cert_attr[12] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_12;
  assign         full_addr_fuse_idevid_cert_attr[13] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_13;
  assign         full_addr_fuse_idevid_cert_attr[14] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_14;
  assign         full_addr_fuse_idevid_cert_attr[15] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_15;
  assign         full_addr_fuse_idevid_cert_attr[16] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_16;
  assign         full_addr_fuse_idevid_cert_attr[17] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_17;
  assign         full_addr_fuse_idevid_cert_attr[18] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_18;
  assign         full_addr_fuse_idevid_cert_attr[19] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_19;
  assign         full_addr_fuse_idevid_cert_attr[20] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_20;
  assign         full_addr_fuse_idevid_cert_attr[21] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_21;
  assign         full_addr_fuse_idevid_cert_attr[22] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_22;
  assign         full_addr_fuse_idevid_cert_attr[23] = `CLP_SOC_IFC_REG_FUSE_IDEVID_CERT_ATTR_23;

  logic          hit_fuse_idevid_manuf_hsm_id[0:3];
  logic [3:0]    bus_fuse_idevid_manuf_hsm_id[0:3];
  logic [31:0]   full_addr_fuse_idevid_manuf_hsm_id[0:3];
  assign         full_addr_fuse_idevid_manuf_hsm_id[0] = `CLP_SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_0;
  assign         full_addr_fuse_idevid_manuf_hsm_id[1] = `CLP_SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_1;
  assign         full_addr_fuse_idevid_manuf_hsm_id[2] = `CLP_SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_2;
  assign         full_addr_fuse_idevid_manuf_hsm_id[3] = `CLP_SOC_IFC_REG_FUSE_IDEVID_MANUF_HSM_ID_3;

  logic          hit_fuse_lms_revocation;
  logic [3:0]    bus_fuse_lms_revocation;
  logic [31:0]   full_addr_fuse_lms_revocation = `CLP_SOC_IFC_REG_FUSE_LMS_REVOCATION;

  logic          hit_fuse_mldsa_revocation;
  logic [3:0]    bus_fuse_mldsa_revocation;
  logic [31:0]   full_addr_fuse_mldsa_revocation = `CLP_SOC_IFC_REG_FUSE_MLDSA_REVOCATION;

  logic          hit_fuse_soc_stepping_id;
  logic [3:0]    bus_fuse_soc_stepping_id;
  logic [31:0]   full_addr_fuse_soc_stepping_id = `CLP_SOC_IFC_REG_FUSE_SOC_STEPPING_ID;

  logic          hit_fuse_manuf_dbg_unlock_token[0:15];
  logic [3:0]    bus_fuse_manuf_dbg_unlock_token[0:15];
  logic [31:0]   full_addr_fuse_manuf_dbg_unlock_token[0:15];
  assign         full_addr_fuse_manuf_dbg_unlock_token[0] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0;
  assign         full_addr_fuse_manuf_dbg_unlock_token[1] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1;
  assign         full_addr_fuse_manuf_dbg_unlock_token[2] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2;
  assign         full_addr_fuse_manuf_dbg_unlock_token[3] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3;
  assign         full_addr_fuse_manuf_dbg_unlock_token[4] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_4;
  assign         full_addr_fuse_manuf_dbg_unlock_token[5] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_5;
  assign         full_addr_fuse_manuf_dbg_unlock_token[6] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_6;
  assign         full_addr_fuse_manuf_dbg_unlock_token[7] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_7;
  assign         full_addr_fuse_manuf_dbg_unlock_token[8] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_8;
  assign         full_addr_fuse_manuf_dbg_unlock_token[9] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_9;
  assign         full_addr_fuse_manuf_dbg_unlock_token[10] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_10;
  assign         full_addr_fuse_manuf_dbg_unlock_token[11] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_11;
  assign         full_addr_fuse_manuf_dbg_unlock_token[12] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_12;
  assign         full_addr_fuse_manuf_dbg_unlock_token[13] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_13;
  assign         full_addr_fuse_manuf_dbg_unlock_token[14] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_14;
  assign         full_addr_fuse_manuf_dbg_unlock_token[15] = `CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_15;

  logic          hit_fuse_pqc_key_type;
  logic [3:0]    bus_fuse_pqc_key_type;
  logic [31:0]   full_addr_fuse_pqc_key_type = `CLP_SOC_IFC_REG_FUSE_PQC_KEY_TYPE;

  logic          hit_fuse_soc_manifest_svn[0:3];
  logic [3:0]    bus_fuse_soc_manifest_svn[0:3];
  logic [31:0]   full_addr_fuse_soc_manifest_svn[0:3];
  assign         full_addr_fuse_soc_manifest_svn[0] = `CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_0;
  assign         full_addr_fuse_soc_manifest_svn[1] = `CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_1;
  assign         full_addr_fuse_soc_manifest_svn[2] = `CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_2;
  assign         full_addr_fuse_soc_manifest_svn[3] = `CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_SVN_3;

  logic          hit_fuse_soc_manifest_max_svn;
  logic [3:0]    bus_fuse_soc_manifest_max_svn;
  logic [31:0]   full_addr_fuse_soc_manifest_max_svn = `CLP_SOC_IFC_REG_FUSE_SOC_MANIFEST_MAX_SVN;

  logic          hit_fuse_hek_seed[0:7];
  logic [3:0]    bus_fuse_hek_seed[0:7];
  logic [31:0]   full_addr_fuse_hek_seed[0:7];
  assign         full_addr_fuse_hek_seed[0] = `CLP_SOC_IFC_REG_FUSE_HEK_SEED_0;
  assign         full_addr_fuse_hek_seed[1] = `CLP_SOC_IFC_REG_FUSE_HEK_SEED_1;
  assign         full_addr_fuse_hek_seed[2] = `CLP_SOC_IFC_REG_FUSE_HEK_SEED_2;
  assign         full_addr_fuse_hek_seed[3] = `CLP_SOC_IFC_REG_FUSE_HEK_SEED_3;
  assign         full_addr_fuse_hek_seed[4] = `CLP_SOC_IFC_REG_FUSE_HEK_SEED_4;
  assign         full_addr_fuse_hek_seed[5] = `CLP_SOC_IFC_REG_FUSE_HEK_SEED_5;
  assign         full_addr_fuse_hek_seed[6] = `CLP_SOC_IFC_REG_FUSE_HEK_SEED_6;
  assign         full_addr_fuse_hek_seed[7] = `CLP_SOC_IFC_REG_FUSE_HEK_SEED_7;

  logic          hit_SS_CALIPTRA_BASE_ADDR_L;
  logic [3:0]    bus_SS_CALIPTRA_BASE_ADDR_L;
  logic [31:0]   full_addr_SS_CALIPTRA_BASE_ADDR_L = `CLP_SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L;

  logic          hit_SS_CALIPTRA_BASE_ADDR_H;
  logic [3:0]    bus_SS_CALIPTRA_BASE_ADDR_H;
  logic [31:0]   full_addr_SS_CALIPTRA_BASE_ADDR_H = `CLP_SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_H;

  logic          hit_SS_MCI_BASE_ADDR_L;
  logic [3:0]    bus_SS_MCI_BASE_ADDR_L;
  logic [31:0]   full_addr_SS_MCI_BASE_ADDR_L = `CLP_SOC_IFC_REG_SS_MCI_BASE_ADDR_L;

  logic          hit_SS_MCI_BASE_ADDR_H;
  logic [3:0]    bus_SS_MCI_BASE_ADDR_H;
  logic [31:0]   full_addr_SS_MCI_BASE_ADDR_H = `CLP_SOC_IFC_REG_SS_MCI_BASE_ADDR_H;

  logic          hit_SS_RECOVERY_IFC_BASE_ADDR_L;
  logic [3:0]    bus_SS_RECOVERY_IFC_BASE_ADDR_L;
  logic [31:0]   full_addr_SS_RECOVERY_IFC_BASE_ADDR_L = `CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_L;

  logic          hit_SS_RECOVERY_IFC_BASE_ADDR_H;
  logic [3:0]    bus_SS_RECOVERY_IFC_BASE_ADDR_H;
  logic [31:0]   full_addr_SS_RECOVERY_IFC_BASE_ADDR_H = `CLP_SOC_IFC_REG_SS_RECOVERY_IFC_BASE_ADDR_H;

  logic          hit_SS_OTP_FC_BASE_ADDR_L;
  logic [3:0]    bus_SS_OTP_FC_BASE_ADDR_L;
  logic [31:0]   full_addr_SS_OTP_FC_BASE_ADDR_L = `CLP_SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_L;

  logic          hit_SS_OTP_FC_BASE_ADDR_H;
  logic [3:0]    bus_SS_OTP_FC_BASE_ADDR_H;
  logic [31:0]   full_addr_SS_OTP_FC_BASE_ADDR_H = `CLP_SOC_IFC_REG_SS_OTP_FC_BASE_ADDR_H;

  logic          hit_SS_UDS_SEED_BASE_ADDR_L;
  logic [3:0]    bus_SS_UDS_SEED_BASE_ADDR_L;
  logic [31:0]   full_addr_SS_UDS_SEED_BASE_ADDR_L = `CLP_SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_L;

  logic          hit_SS_UDS_SEED_BASE_ADDR_H;
  logic [3:0]    bus_SS_UDS_SEED_BASE_ADDR_H;
  logic [31:0]   full_addr_SS_UDS_SEED_BASE_ADDR_H = `CLP_SOC_IFC_REG_SS_UDS_SEED_BASE_ADDR_H;

  logic          hit_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET;
  logic [3:0]    bus_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET;
  logic [31:0]   full_addr_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET = `CLP_SOC_IFC_REG_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET;

  logic          hit_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES;
  logic [3:0]    bus_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES;
  logic [31:0]   full_addr_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES = `CLP_SOC_IFC_REG_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES;

  logic          hit_SS_DEBUG_INTENT;
  logic [3:0]    bus_SS_DEBUG_INTENT;
  logic [31:0]   full_addr_SS_DEBUG_INTENT = `CLP_SOC_IFC_REG_SS_DEBUG_INTENT;

  logic          hit_SS_CALIPTRA_DMA_AXI_USER;
  logic [3:0]    bus_SS_CALIPTRA_DMA_AXI_USER;
  logic [31:0]   full_addr_SS_CALIPTRA_DMA_AXI_USER = `CLP_SOC_IFC_REG_SS_CALIPTRA_DMA_AXI_USER;

  logic          hit_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L;
  logic [3:0]    bus_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L;
  logic [31:0]   full_addr_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L = `CLP_SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L;

  logic          hit_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H;
  logic [3:0]    bus_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H;
  logic [31:0]   full_addr_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H = `CLP_SOC_IFC_REG_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H;

  logic          hit_SS_KEY_RELEASE_BASE_ADDR_L;
  logic [3:0]    bus_SS_KEY_RELEASE_BASE_ADDR_L;
  logic [31:0]   full_addr_SS_KEY_RELEASE_BASE_ADDR_L = `CLP_SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_L;

  logic          hit_SS_KEY_RELEASE_BASE_ADDR_H;
  logic [3:0]    bus_SS_KEY_RELEASE_BASE_ADDR_H;
  logic [31:0]   full_addr_SS_KEY_RELEASE_BASE_ADDR_H = `CLP_SOC_IFC_REG_SS_KEY_RELEASE_BASE_ADDR_H;

  logic          hit_SS_KEY_RELEASE_SIZE;
  logic [3:0]    bus_SS_KEY_RELEASE_SIZE;
  logic [31:0]   full_addr_SS_KEY_RELEASE_SIZE = `CLP_SOC_IFC_REG_SS_KEY_RELEASE_SIZE;

  logic          hit_SS_OCP_LOCK_CTRL;
  logic [3:0]    bus_SS_OCP_LOCK_CTRL;
  logic [31:0]   full_addr_SS_OCP_LOCK_CTRL = `CLP_SOC_IFC_REG_SS_OCP_LOCK_CTRL;

  logic          hit_SS_STRAP_GENERIC[0:3];
  logic [3:0]    bus_SS_STRAP_GENERIC[0:3];
  logic [31:0]   full_addr_SS_STRAP_GENERIC[0:3];
  assign         full_addr_SS_STRAP_GENERIC[0] = `CLP_SOC_IFC_REG_SS_STRAP_GENERIC_0;
  assign         full_addr_SS_STRAP_GENERIC[1] = `CLP_SOC_IFC_REG_SS_STRAP_GENERIC_1;
  assign         full_addr_SS_STRAP_GENERIC[2] = `CLP_SOC_IFC_REG_SS_STRAP_GENERIC_2;
  assign         full_addr_SS_STRAP_GENERIC[3] = `CLP_SOC_IFC_REG_SS_STRAP_GENERIC_3;

  logic          hit_SS_DBG_SERVICE_REG_REQ;
  logic [3:0]    bus_SS_DBG_SERVICE_REG_REQ;
  logic [31:0]   full_addr_SS_DBG_SERVICE_REG_REQ = `CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_REQ;

  logic          hit_SS_DBG_SERVICE_REG_RSP;
  logic [3:0]    bus_SS_DBG_SERVICE_REG_RSP;
  logic [31:0]   full_addr_SS_DBG_SERVICE_REG_RSP = `CLP_SOC_IFC_REG_SS_DBG_SERVICE_REG_RSP;

  logic          hit_SS_SOC_DBG_UNLOCK_LEVEL[0:1];
  logic [3:0]    bus_SS_SOC_DBG_UNLOCK_LEVEL[0:1];
  logic [31:0]   full_addr_SS_SOC_DBG_UNLOCK_LEVEL[0:1];
  assign         full_addr_SS_SOC_DBG_UNLOCK_LEVEL[0] = `CLP_SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_0;
  assign         full_addr_SS_SOC_DBG_UNLOCK_LEVEL[1] = `CLP_SOC_IFC_REG_SS_SOC_DBG_UNLOCK_LEVEL_1;

  logic          hit_SS_GENERIC_FW_EXEC_CTRL[0:3];
  logic [3:0]    bus_SS_GENERIC_FW_EXEC_CTRL[0:3];
  logic [31:0]   full_addr_SS_GENERIC_FW_EXEC_CTRL[0:3];
  assign         full_addr_SS_GENERIC_FW_EXEC_CTRL[0] = `CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_0;
  assign         full_addr_SS_GENERIC_FW_EXEC_CTRL[1] = `CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_1;
  assign         full_addr_SS_GENERIC_FW_EXEC_CTRL[2] = `CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_2;
  assign         full_addr_SS_GENERIC_FW_EXEC_CTRL[3] = `CLP_SOC_IFC_REG_SS_GENERIC_FW_EXEC_CTRL_3;

  logic          hit_internal_obf_key[0:7];
  logic [3:0]    bus_internal_obf_key[0:7];
  logic [31:0]   full_addr_internal_obf_key[0:7];
  assign         full_addr_internal_obf_key[0] = `CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_0;
  assign         full_addr_internal_obf_key[1] = `CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_1;
  assign         full_addr_internal_obf_key[2] = `CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_2;
  assign         full_addr_internal_obf_key[3] = `CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_3;
  assign         full_addr_internal_obf_key[4] = `CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_4;
  assign         full_addr_internal_obf_key[5] = `CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_5;
  assign         full_addr_internal_obf_key[6] = `CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_6;
  assign         full_addr_internal_obf_key[7] = `CLP_SOC_IFC_REG_INTERNAL_OBF_KEY_7;

  logic          hit_internal_iccm_lock;
  logic [3:0]    bus_internal_iccm_lock;
  logic [31:0]   full_addr_internal_iccm_lock = `CLP_SOC_IFC_REG_INTERNAL_ICCM_LOCK;

  logic          hit_internal_fw_update_reset;
  logic [3:0]    bus_internal_fw_update_reset;
  logic [31:0]   full_addr_internal_fw_update_reset = `CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET;

  logic          hit_internal_fw_update_reset_wait_cycles;
  logic [3:0]    bus_internal_fw_update_reset_wait_cycles;
  logic [31:0]   full_addr_internal_fw_update_reset_wait_cycles = `CLP_SOC_IFC_REG_INTERNAL_FW_UPDATE_RESET_WAIT_CYCLES;

  logic          hit_internal_nmi_vector;
  logic [3:0]    bus_internal_nmi_vector;
  logic [31:0]   full_addr_internal_nmi_vector = `CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR;

  logic          hit_internal_hw_error_fatal_mask;
  logic [3:0]    bus_internal_hw_error_fatal_mask;
  logic [31:0]   full_addr_internal_hw_error_fatal_mask = `CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_FATAL_MASK;

  logic          hit_internal_hw_error_non_fatal_mask;
  logic [3:0]    bus_internal_hw_error_non_fatal_mask;
  logic [31:0]   full_addr_internal_hw_error_non_fatal_mask = `CLP_SOC_IFC_REG_INTERNAL_HW_ERROR_NON_FATAL_MASK;

  logic          hit_internal_fw_error_fatal_mask;
  logic [3:0]    bus_internal_fw_error_fatal_mask;
  logic [31:0]   full_addr_internal_fw_error_fatal_mask = `CLP_SOC_IFC_REG_INTERNAL_FW_ERROR_FATAL_MASK;

  logic          hit_internal_fw_error_non_fatal_mask;
  logic [3:0]    bus_internal_fw_error_non_fatal_mask;
  logic [31:0]   full_addr_internal_fw_error_non_fatal_mask = `CLP_SOC_IFC_REG_INTERNAL_FW_ERROR_NON_FATAL_MASK;

  logic          hit_internal_rv_mtime_l;
  logic [3:0]    bus_internal_rv_mtime_l;
  logic [31:0]   full_addr_internal_rv_mtime_l = `CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_L;

  logic          hit_internal_rv_mtime_h;
  logic [3:0]    bus_internal_rv_mtime_h;
  logic [31:0]   full_addr_internal_rv_mtime_h = `CLP_SOC_IFC_REG_INTERNAL_RV_MTIME_H;

  logic          hit_internal_rv_mtimecmp_l;
  logic [3:0]    bus_internal_rv_mtimecmp_l;
  logic [31:0]   full_addr_internal_rv_mtimecmp_l = `CLP_SOC_IFC_REG_INTERNAL_RV_MTIMECMP_L;

  logic          hit_internal_rv_mtimecmp_h;
  logic [3:0]    bus_internal_rv_mtimecmp_h;
  logic [31:0]   full_addr_internal_rv_mtimecmp_h = `CLP_SOC_IFC_REG_INTERNAL_RV_MTIMECMP_H;

  logic          hit_intr_brf_global_intr_en_r;
  logic [3:0]    bus_intr_brf_global_intr_en_r;
  logic [31:0]   full_addr_intr_brf_global_intr_en_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R;

  logic          hit_intr_brf_error_intr_en_r;
  logic [3:0]    bus_intr_brf_error_intr_en_r;
  logic [31:0]   full_addr_intr_brf_error_intr_en_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R;

  logic          hit_intr_brf_notif_intr_en_r;
  logic [3:0]    bus_intr_brf_notif_intr_en_r;
  logic [31:0]   full_addr_intr_brf_notif_intr_en_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R;

  logic          hit_intr_brf_error_global_intr_r;
  logic [3:0]    bus_intr_brf_error_global_intr_r;
  logic [31:0]   full_addr_intr_brf_error_global_intr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_GLOBAL_INTR_R;

  logic          hit_intr_brf_notif_global_intr_r;
  logic [3:0]    bus_intr_brf_notif_global_intr_r;
  logic [31:0]   full_addr_intr_brf_notif_global_intr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GLOBAL_INTR_R;

  logic          hit_intr_brf_error_internal_intr_r;
  logic [3:0]    bus_intr_brf_error_internal_intr_r;
  logic [31:0]   full_addr_intr_brf_error_internal_intr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R;

  logic          hit_intr_brf_notif_internal_intr_r;
  logic [3:0]    bus_intr_brf_notif_internal_intr_r;
  logic [31:0]   full_addr_intr_brf_notif_internal_intr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R;

  logic          hit_intr_brf_error_intr_trig_r;
  logic [3:0]    bus_intr_brf_error_intr_trig_r;
  logic [31:0]   full_addr_intr_brf_error_intr_trig_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_TRIG_R;

  logic          hit_intr_brf_notif_intr_trig_r;
  logic [3:0]    bus_intr_brf_notif_intr_trig_r;
  logic [31:0]   full_addr_intr_brf_notif_intr_trig_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTR_TRIG_R;

  logic          hit_intr_brf_error_internal_intr_count_r;
  logic [3:0]    bus_intr_brf_error_internal_intr_count_r;
  logic [31:0]   full_addr_intr_brf_error_internal_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_R;

  logic          hit_intr_brf_error_inv_dev_intr_count_r;
  logic [3:0]    bus_intr_brf_error_inv_dev_intr_count_r;
  logic [31:0]   full_addr_intr_brf_error_inv_dev_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_R;

  logic          hit_intr_brf_error_cmd_fail_intr_count_r;
  logic [3:0]    bus_intr_brf_error_cmd_fail_intr_count_r;
  logic [31:0]   full_addr_intr_brf_error_cmd_fail_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_R;

  logic          hit_intr_brf_error_bad_fuse_intr_count_r;
  logic [3:0]    bus_intr_brf_error_bad_fuse_intr_count_r;
  logic [31:0]   full_addr_intr_brf_error_bad_fuse_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_R;

  logic          hit_intr_brf_error_iccm_blocked_intr_count_r;
  logic [3:0]    bus_intr_brf_error_iccm_blocked_intr_count_r;
  logic [31:0]   full_addr_intr_brf_error_iccm_blocked_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_R;

  logic          hit_intr_brf_error_mbox_ecc_unc_intr_count_r;
  logic [3:0]    bus_intr_brf_error_mbox_ecc_unc_intr_count_r;
  logic [31:0]   full_addr_intr_brf_error_mbox_ecc_unc_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_R;

  logic          hit_intr_brf_error_wdt_timer1_timeout_intr_count_r;
  logic [3:0]    bus_intr_brf_error_wdt_timer1_timeout_intr_count_r;
  logic [31:0]   full_addr_intr_brf_error_wdt_timer1_timeout_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_R;

  logic          hit_intr_brf_error_wdt_timer2_timeout_intr_count_r;
  logic [3:0]    bus_intr_brf_error_wdt_timer2_timeout_intr_count_r;
  logic [31:0]   full_addr_intr_brf_error_wdt_timer2_timeout_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_R;

  logic          hit_intr_brf_notif_cmd_avail_intr_count_r;
  logic [3:0]    bus_intr_brf_notif_cmd_avail_intr_count_r;
  logic [31:0]   full_addr_intr_brf_notif_cmd_avail_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_R;

  logic          hit_intr_brf_notif_mbox_ecc_cor_intr_count_r;
  logic [3:0]    bus_intr_brf_notif_mbox_ecc_cor_intr_count_r;
  logic [31:0]   full_addr_intr_brf_notif_mbox_ecc_cor_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_R;

  logic          hit_intr_brf_notif_debug_locked_intr_count_r;
  logic [3:0]    bus_intr_brf_notif_debug_locked_intr_count_r;
  logic [31:0]   full_addr_intr_brf_notif_debug_locked_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_R;

  logic          hit_intr_brf_notif_scan_mode_intr_count_r;
  logic [3:0]    bus_intr_brf_notif_scan_mode_intr_count_r;
  logic [31:0]   full_addr_intr_brf_notif_scan_mode_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_R;

  logic          hit_intr_brf_notif_soc_req_lock_intr_count_r;
  logic [3:0]    bus_intr_brf_notif_soc_req_lock_intr_count_r;
  logic [31:0]   full_addr_intr_brf_notif_soc_req_lock_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_R;

  logic          hit_intr_brf_notif_gen_in_toggle_intr_count_r;
  logic [3:0]    bus_intr_brf_notif_gen_in_toggle_intr_count_r;
  logic [31:0]   full_addr_intr_brf_notif_gen_in_toggle_intr_count_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_R;

  logic          hit_intr_brf_error_internal_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_error_internal_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_error_internal_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_error_inv_dev_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_error_inv_dev_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_error_inv_dev_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INV_DEV_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_error_cmd_fail_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_error_cmd_fail_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_error_cmd_fail_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_CMD_FAIL_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_error_bad_fuse_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_error_bad_fuse_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_error_bad_fuse_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_BAD_FUSE_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_error_iccm_blocked_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_error_iccm_blocked_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_error_iccm_blocked_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_ICCM_BLOCKED_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_error_mbox_ecc_unc_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_error_mbox_ecc_unc_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_error_mbox_ecc_unc_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_MBOX_ECC_UNC_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_error_wdt_timer1_timeout_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_error_wdt_timer1_timeout_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_error_wdt_timer1_timeout_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER1_TIMEOUT_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_error_wdt_timer2_timeout_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_error_wdt_timer2_timeout_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_error_wdt_timer2_timeout_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_WDT_TIMER2_TIMEOUT_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_notif_cmd_avail_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_notif_cmd_avail_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_notif_cmd_avail_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_CMD_AVAIL_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_notif_mbox_ecc_cor_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_notif_mbox_ecc_cor_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_notif_mbox_ecc_cor_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_MBOX_ECC_COR_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_notif_debug_locked_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_notif_debug_locked_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_notif_debug_locked_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_DEBUG_LOCKED_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_notif_scan_mode_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_notif_scan_mode_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_notif_scan_mode_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SCAN_MODE_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_notif_soc_req_lock_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_notif_soc_req_lock_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_notif_soc_req_lock_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_SOC_REQ_LOCK_INTR_COUNT_INCR_R;

  logic          hit_intr_brf_notif_gen_in_toggle_intr_count_incr_r;
  logic [3:0]    bus_intr_brf_notif_gen_in_toggle_intr_count_incr_r;
  logic [31:0]   full_addr_intr_brf_notif_gen_in_toggle_intr_count_incr_r = `CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_GEN_IN_TOGGLE_INTR_COUNT_INCR_R;


  assign hit_CPTRA_HW_ERROR_FATAL = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_HW_ERROR_FATAL[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_HW_ERROR_FATAL = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_HW_ERROR_FATAL}};

  assign hit_CPTRA_HW_ERROR_NON_FATAL = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_HW_ERROR_NON_FATAL[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_HW_ERROR_NON_FATAL = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_HW_ERROR_NON_FATAL}};

  assign hit_CPTRA_FW_ERROR_FATAL = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_ERROR_FATAL[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_FW_ERROR_FATAL = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_ERROR_FATAL}};

  assign hit_CPTRA_FW_ERROR_NON_FATAL = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_ERROR_NON_FATAL[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_FW_ERROR_NON_FATAL = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_ERROR_NON_FATAL}};

  assign hit_CPTRA_HW_ERROR_ENC = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_HW_ERROR_ENC[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_HW_ERROR_ENC = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_HW_ERROR_ENC}};

  assign hit_CPTRA_FW_ERROR_ENC = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_ERROR_ENC[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_FW_ERROR_ENC = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_ERROR_ENC}};

  assign hit_CPTRA_FW_EXTENDED_ERROR_INFO[0] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[0][18-1:0]);
  assign bus_CPTRA_FW_EXTENDED_ERROR_INFO[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_EXTENDED_ERROR_INFO[0]}};

  assign hit_CPTRA_FW_EXTENDED_ERROR_INFO[1] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[1][18-1:0]);
  assign bus_CPTRA_FW_EXTENDED_ERROR_INFO[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_EXTENDED_ERROR_INFO[1]}};

  assign hit_CPTRA_FW_EXTENDED_ERROR_INFO[2] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[2][18-1:0]);
  assign bus_CPTRA_FW_EXTENDED_ERROR_INFO[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_EXTENDED_ERROR_INFO[2]}};

  assign hit_CPTRA_FW_EXTENDED_ERROR_INFO[3] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[3][18-1:0]);
  assign bus_CPTRA_FW_EXTENDED_ERROR_INFO[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_EXTENDED_ERROR_INFO[3]}};

  assign hit_CPTRA_FW_EXTENDED_ERROR_INFO[4] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[4][18-1:0]);
  assign bus_CPTRA_FW_EXTENDED_ERROR_INFO[4] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_EXTENDED_ERROR_INFO[4]}};

  assign hit_CPTRA_FW_EXTENDED_ERROR_INFO[5] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[5][18-1:0]);
  assign bus_CPTRA_FW_EXTENDED_ERROR_INFO[5] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_EXTENDED_ERROR_INFO[5]}};

  assign hit_CPTRA_FW_EXTENDED_ERROR_INFO[6] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[6][18-1:0]);
  assign bus_CPTRA_FW_EXTENDED_ERROR_INFO[6] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_EXTENDED_ERROR_INFO[6]}};

  assign hit_CPTRA_FW_EXTENDED_ERROR_INFO[7] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_EXTENDED_ERROR_INFO[7][18-1:0]);
  assign bus_CPTRA_FW_EXTENDED_ERROR_INFO[7] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_EXTENDED_ERROR_INFO[7]}};

  assign hit_CPTRA_BOOT_STATUS = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_BOOT_STATUS[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_BOOT_STATUS = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_BOOT_STATUS}};

  assign hit_CPTRA_FLOW_STATUS = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FLOW_STATUS[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_FLOW_STATUS = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FLOW_STATUS}};

  assign hit_CPTRA_RESET_REASON = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_RESET_REASON[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_RESET_REASON = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_RESET_REASON}};

  // assign hit_CPTRA_SECURITY_STATE = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_SECURITY_STATE[AXI_ADDR_WIDTH-1:0]);
  // assign bus_CPTRA_SECURITY_STATE = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_SECURITY_STATE}};

  assign hit_CPTRA_MBOX_VALID_AXI_USER[0] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_MBOX_VALID_AXI_USER[0][18-1:0]);
  assign bus_CPTRA_MBOX_VALID_AXI_USER[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_MBOX_VALID_AXI_USER[0]}};

  assign hit_CPTRA_MBOX_VALID_AXI_USER[1] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_MBOX_VALID_AXI_USER[1][18-1:0]);
  assign bus_CPTRA_MBOX_VALID_AXI_USER[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_MBOX_VALID_AXI_USER[1]}};

  assign hit_CPTRA_MBOX_VALID_AXI_USER[2] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_MBOX_VALID_AXI_USER[2][18-1:0]);
  assign bus_CPTRA_MBOX_VALID_AXI_USER[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_MBOX_VALID_AXI_USER[2]}};

  assign hit_CPTRA_MBOX_VALID_AXI_USER[3] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_MBOX_VALID_AXI_USER[3][18-1:0]);
  assign bus_CPTRA_MBOX_VALID_AXI_USER[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_MBOX_VALID_AXI_USER[3]}};

  assign hit_CPTRA_MBOX_VALID_AXI_USER[4] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_MBOX_VALID_AXI_USER[4][18-1:0]);
  assign bus_CPTRA_MBOX_VALID_AXI_USER[4] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_MBOX_VALID_AXI_USER[4]}};

  assign hit_CPTRA_MBOX_AXI_USER_LOCK[0] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_MBOX_AXI_USER_LOCK[0][18-1:0]);
  assign bus_CPTRA_MBOX_AXI_USER_LOCK[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_MBOX_AXI_USER_LOCK[0]}};

  assign hit_CPTRA_MBOX_AXI_USER_LOCK[1] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_MBOX_AXI_USER_LOCK[1][18-1:0]);
  assign bus_CPTRA_MBOX_AXI_USER_LOCK[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_MBOX_AXI_USER_LOCK[1]}};

  assign hit_CPTRA_MBOX_AXI_USER_LOCK[2] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_MBOX_AXI_USER_LOCK[2][18-1:0]);
  assign bus_CPTRA_MBOX_AXI_USER_LOCK[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_MBOX_AXI_USER_LOCK[2]}};

  assign hit_CPTRA_MBOX_AXI_USER_LOCK[3] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_MBOX_AXI_USER_LOCK[3][18-1:0]);
  assign bus_CPTRA_MBOX_AXI_USER_LOCK[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_MBOX_AXI_USER_LOCK[3]}};

  assign hit_CPTRA_MBOX_AXI_USER_LOCK[4] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_MBOX_AXI_USER_LOCK[4][18-1:0]);
  assign bus_CPTRA_MBOX_AXI_USER_LOCK[4] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_MBOX_AXI_USER_LOCK[4]}};

  assign hit_CPTRA_TRNG_VALID_AXI_USER = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_VALID_AXI_USER[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_TRNG_VALID_AXI_USER = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_VALID_AXI_USER}};

  assign hit_CPTRA_TRNG_AXI_USER_LOCK = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_AXI_USER_LOCK[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_TRNG_AXI_USER_LOCK = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_AXI_USER_LOCK}};

  assign hit_CPTRA_TRNG_DATA[0] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_DATA[0][18-1:0]);
  assign bus_CPTRA_TRNG_DATA[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_DATA[0]}};

  assign hit_CPTRA_TRNG_DATA[1] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_DATA[1][18-1:0]);
  assign bus_CPTRA_TRNG_DATA[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_DATA[1]}};

  assign hit_CPTRA_TRNG_DATA[2] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_DATA[2][18-1:0]);
  assign bus_CPTRA_TRNG_DATA[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_DATA[2]}};

  assign hit_CPTRA_TRNG_DATA[3] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_DATA[3][18-1:0]);
  assign bus_CPTRA_TRNG_DATA[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_DATA[3]}};

  assign hit_CPTRA_TRNG_DATA[4] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_DATA[4][18-1:0]);
  assign bus_CPTRA_TRNG_DATA[4] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_DATA[4]}};

  assign hit_CPTRA_TRNG_DATA[5] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_DATA[5][18-1:0]);
  assign bus_CPTRA_TRNG_DATA[5] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_DATA[5]}};

  assign hit_CPTRA_TRNG_DATA[6] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_DATA[6][18-1:0]);
  assign bus_CPTRA_TRNG_DATA[6] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_DATA[6]}};

  assign hit_CPTRA_TRNG_DATA[7] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_DATA[7][18-1:0]);
  assign bus_CPTRA_TRNG_DATA[7] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_DATA[7]}};

  assign hit_CPTRA_TRNG_DATA[8] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_DATA[8][18-1:0]);
  assign bus_CPTRA_TRNG_DATA[8] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_DATA[8]}};

  assign hit_CPTRA_TRNG_DATA[9] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_DATA[9][18-1:0]);
  assign bus_CPTRA_TRNG_DATA[9] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_DATA[9]}};

  assign hit_CPTRA_TRNG_DATA[10] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_DATA[10][18-1:0]);
  assign bus_CPTRA_TRNG_DATA[10] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_DATA[10]}};

  assign hit_CPTRA_TRNG_DATA[11] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_DATA[11][18-1:0]);
  assign bus_CPTRA_TRNG_DATA[11] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_DATA[11]}};

  assign hit_CPTRA_TRNG_CTRL = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_CTRL[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_TRNG_CTRL = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_CTRL}};

  assign hit_CPTRA_TRNG_STATUS = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TRNG_STATUS[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_TRNG_STATUS = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TRNG_STATUS}};

  assign hit_CPTRA_FUSE_WR_DONE = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FUSE_WR_DONE[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_FUSE_WR_DONE = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FUSE_WR_DONE}};

  assign hit_CPTRA_TIMER_CONFIG = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_TIMER_CONFIG[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_TIMER_CONFIG = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_TIMER_CONFIG}};

  assign hit_CPTRA_BOOTFSM_GO = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_BOOTFSM_GO[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_BOOTFSM_GO = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_BOOTFSM_GO}};

  assign hit_CPTRA_DBG_MANUF_SERVICE_REG = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_DBG_MANUF_SERVICE_REG[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_DBG_MANUF_SERVICE_REG = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_DBG_MANUF_SERVICE_REG}};

  assign hit_CPTRA_CLK_GATING_EN = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_CLK_GATING_EN[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_CLK_GATING_EN = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_CLK_GATING_EN}};

  assign hit_CPTRA_GENERIC_INPUT_WIRES[0] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_GENERIC_INPUT_WIRES[0][18-1:0]);
  assign bus_CPTRA_GENERIC_INPUT_WIRES[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_GENERIC_INPUT_WIRES[0]}};

  assign hit_CPTRA_GENERIC_INPUT_WIRES[1] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_GENERIC_INPUT_WIRES[1][18-1:0]);
  assign bus_CPTRA_GENERIC_INPUT_WIRES[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_GENERIC_INPUT_WIRES[1]}};

  assign hit_CPTRA_GENERIC_OUTPUT_WIRES[0] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_GENERIC_OUTPUT_WIRES[0][18-1:0]);
  assign bus_CPTRA_GENERIC_OUTPUT_WIRES[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_GENERIC_OUTPUT_WIRES[0]}};

  assign hit_CPTRA_GENERIC_OUTPUT_WIRES[1] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_GENERIC_OUTPUT_WIRES[1][18-1:0]);
  assign bus_CPTRA_GENERIC_OUTPUT_WIRES[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_GENERIC_OUTPUT_WIRES[1]}};

  // assign hit_CPTRA_HW_REV_ID = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_HW_REV_ID[AXI_ADDR_WIDTH-1:0]);
  // assign bus_CPTRA_HW_REV_ID = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_HW_REV_ID}};

  assign hit_CPTRA_FW_REV_ID[0] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_REV_ID[0][18-1:0]);
  assign bus_CPTRA_FW_REV_ID[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_REV_ID[0]}};

  assign hit_CPTRA_FW_REV_ID[1] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_REV_ID[1][18-1:0]);
  assign bus_CPTRA_FW_REV_ID[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_REV_ID[1]}};

  // assign hit_CPTRA_HW_CONFIG = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_HW_CONFIG[AXI_ADDR_WIDTH-1:0]);
  // assign bus_CPTRA_HW_CONFIG = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_HW_CONFIG}};

  assign hit_CPTRA_WDT_TIMER1_EN = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_WDT_TIMER1_EN[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_WDT_TIMER1_EN = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_WDT_TIMER1_EN}};

  assign hit_CPTRA_WDT_TIMER1_CTRL = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_WDT_TIMER1_CTRL[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_WDT_TIMER1_CTRL = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_WDT_TIMER1_CTRL}};

  assign hit_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[0] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[0][18-1:0]);
  assign bus_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[0]}};

  assign hit_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[1] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[1][18-1:0]);
  assign bus_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[1]}};

  assign hit_CPTRA_WDT_TIMER2_EN = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_WDT_TIMER2_EN[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_WDT_TIMER2_EN = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_WDT_TIMER2_EN}};

  assign hit_CPTRA_WDT_TIMER2_CTRL = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_WDT_TIMER2_CTRL[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_WDT_TIMER2_CTRL = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_WDT_TIMER2_CTRL}};

  assign hit_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[0] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[0][18-1:0]);
  assign bus_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[0]}};

  assign hit_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[1] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[1][18-1:0]);
  assign bus_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[1]}};

  assign hit_CPTRA_WDT_STATUS = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_WDT_STATUS[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_WDT_STATUS = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_WDT_STATUS}};

  assign hit_CPTRA_FUSE_VALID_AXI_USER = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FUSE_VALID_AXI_USER[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_FUSE_VALID_AXI_USER = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FUSE_VALID_AXI_USER}};

  assign hit_CPTRA_FUSE_AXI_USER_LOCK = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FUSE_AXI_USER_LOCK[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_FUSE_AXI_USER_LOCK = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FUSE_AXI_USER_LOCK}};

  assign hit_CPTRA_WDT_CFG[0] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_WDT_CFG[0][18-1:0]);
  assign bus_CPTRA_WDT_CFG[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_WDT_CFG[0]}};

  assign hit_CPTRA_WDT_CFG[1] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_WDT_CFG[1][18-1:0]);
  assign bus_CPTRA_WDT_CFG[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_WDT_CFG[1]}};

  assign hit_CPTRA_iTRNG_ENTROPY_CONFIG_0 = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_iTRNG_ENTROPY_CONFIG_0[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_iTRNG_ENTROPY_CONFIG_0 = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_iTRNG_ENTROPY_CONFIG_0}};

  assign hit_CPTRA_iTRNG_ENTROPY_CONFIG_1 = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_iTRNG_ENTROPY_CONFIG_1[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_iTRNG_ENTROPY_CONFIG_1 = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_iTRNG_ENTROPY_CONFIG_1}};

  assign hit_CPTRA_RSVD_REG[0] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_RSVD_REG[0][18-1:0]);
  assign bus_CPTRA_RSVD_REG[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_RSVD_REG[0]}};

  assign hit_CPTRA_RSVD_REG[1] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_RSVD_REG[1][18-1:0]);
  assign bus_CPTRA_RSVD_REG[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_RSVD_REG[1]}};

  assign hit_CPTRA_HW_CAPABILITIES = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_HW_CAPABILITIES[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_HW_CAPABILITIES = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_HW_CAPABILITIES}};

  assign hit_CPTRA_FW_CAPABILITIES = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_FW_CAPABILITIES[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_FW_CAPABILITIES = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_FW_CAPABILITIES}};

  assign hit_CPTRA_CAP_LOCK = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_CAP_LOCK[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_CAP_LOCK = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_CAP_LOCK}};

  assign hit_CPTRA_OWNER_PK_HASH[0] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH[0][18-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH[0]}};

  assign hit_CPTRA_OWNER_PK_HASH[1] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH[1][18-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH[1]}};

  assign hit_CPTRA_OWNER_PK_HASH[2] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH[2][18-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH[2]}};

  assign hit_CPTRA_OWNER_PK_HASH[3] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH[3][18-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH[3]}};

  assign hit_CPTRA_OWNER_PK_HASH[4] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH[4][18-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH[4] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH[4]}};

  assign hit_CPTRA_OWNER_PK_HASH[5] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH[5][18-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH[5] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH[5]}};

  assign hit_CPTRA_OWNER_PK_HASH[6] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH[6][18-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH[6] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH[6]}};

  assign hit_CPTRA_OWNER_PK_HASH[7] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH[7][18-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH[7] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH[7]}};

  assign hit_CPTRA_OWNER_PK_HASH[8] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH[8][18-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH[8] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH[8]}};

  assign hit_CPTRA_OWNER_PK_HASH[9] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH[9][18-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH[9] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH[9]}};

  assign hit_CPTRA_OWNER_PK_HASH[10] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH[10][18-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH[10] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH[10]}};

  assign hit_CPTRA_OWNER_PK_HASH[11] = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH[11][18-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH[11] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH[11]}};

  assign hit_CPTRA_OWNER_PK_HASH_LOCK = (soc_ifc_reg_req_data.addr == full_addr_CPTRA_OWNER_PK_HASH_LOCK[AXI_ADDR_WIDTH-1:0]);
  assign bus_CPTRA_OWNER_PK_HASH_LOCK = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_CPTRA_OWNER_PK_HASH_LOCK}};

  assign hit_fuse_uds_seed[0] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[0][18-1:0]);
  assign bus_fuse_uds_seed[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[0]}};

  assign hit_fuse_uds_seed[1] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[1][18-1:0]);
  assign bus_fuse_uds_seed[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[1]}};

  assign hit_fuse_uds_seed[2] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[2][18-1:0]);
  assign bus_fuse_uds_seed[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[2]}};

  assign hit_fuse_uds_seed[3] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[3][18-1:0]);
  assign bus_fuse_uds_seed[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[3]}};

  assign hit_fuse_uds_seed[4] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[4][18-1:0]);
  assign bus_fuse_uds_seed[4] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[4]}};

  assign hit_fuse_uds_seed[5] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[5][18-1:0]);
  assign bus_fuse_uds_seed[5] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[5]}};

  assign hit_fuse_uds_seed[6] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[6][18-1:0]);
  assign bus_fuse_uds_seed[6] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[6]}};

  assign hit_fuse_uds_seed[7] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[7][18-1:0]);
  assign bus_fuse_uds_seed[7] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[7]}};

  assign hit_fuse_uds_seed[8] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[8][18-1:0]);
  assign bus_fuse_uds_seed[8] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[8]}};

  assign hit_fuse_uds_seed[9] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[9][18-1:0]);
  assign bus_fuse_uds_seed[9] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[9]}};

  assign hit_fuse_uds_seed[10] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[10][18-1:0]);
  assign bus_fuse_uds_seed[10] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[10]}};

  assign hit_fuse_uds_seed[11] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[11][18-1:0]);
  assign bus_fuse_uds_seed[11] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[11]}};

  assign hit_fuse_uds_seed[12] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[12][18-1:0]);
  assign bus_fuse_uds_seed[12] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[12]}};

  assign hit_fuse_uds_seed[13] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[13][18-1:0]);
  assign bus_fuse_uds_seed[13] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[13]}};

  assign hit_fuse_uds_seed[14] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[14][18-1:0]);
  assign bus_fuse_uds_seed[14] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[14]}};

  assign hit_fuse_uds_seed[15] = (soc_ifc_reg_req_data.addr == full_addr_fuse_uds_seed[15][18-1:0]);
  assign bus_fuse_uds_seed[15] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_uds_seed[15]}};

  assign hit_fuse_field_entropy[0] = (soc_ifc_reg_req_data.addr == full_addr_fuse_field_entropy[0][18-1:0]);
  assign bus_fuse_field_entropy[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_field_entropy[0]}};

  assign hit_fuse_field_entropy[1] = (soc_ifc_reg_req_data.addr == full_addr_fuse_field_entropy[1][18-1:0]);
  assign bus_fuse_field_entropy[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_field_entropy[1]}};

  assign hit_fuse_field_entropy[2] = (soc_ifc_reg_req_data.addr == full_addr_fuse_field_entropy[2][18-1:0]);
  assign bus_fuse_field_entropy[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_field_entropy[2]}};

  assign hit_fuse_field_entropy[3] = (soc_ifc_reg_req_data.addr == full_addr_fuse_field_entropy[3][18-1:0]);
  assign bus_fuse_field_entropy[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_field_entropy[3]}};

  assign hit_fuse_field_entropy[4] = (soc_ifc_reg_req_data.addr == full_addr_fuse_field_entropy[4][18-1:0]);
  assign bus_fuse_field_entropy[4] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_field_entropy[4]}};

  assign hit_fuse_field_entropy[5] = (soc_ifc_reg_req_data.addr == full_addr_fuse_field_entropy[5][18-1:0]);
  assign bus_fuse_field_entropy[5] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_field_entropy[5]}};

  assign hit_fuse_field_entropy[6] = (soc_ifc_reg_req_data.addr == full_addr_fuse_field_entropy[6][18-1:0]);
  assign bus_fuse_field_entropy[6] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_field_entropy[6]}};

  assign hit_fuse_field_entropy[7] = (soc_ifc_reg_req_data.addr == full_addr_fuse_field_entropy[7][18-1:0]);
  assign bus_fuse_field_entropy[7] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_field_entropy[7]}};

  assign hit_fuse_vendor_pk_hash[0] = (soc_ifc_reg_req_data.addr == full_addr_fuse_vendor_pk_hash[0][18-1:0]);
  assign bus_fuse_vendor_pk_hash[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_vendor_pk_hash[0]}};

  assign hit_fuse_vendor_pk_hash[1] = (soc_ifc_reg_req_data.addr == full_addr_fuse_vendor_pk_hash[1][18-1:0]);
  assign bus_fuse_vendor_pk_hash[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_vendor_pk_hash[1]}};

  assign hit_fuse_vendor_pk_hash[2] = (soc_ifc_reg_req_data.addr == full_addr_fuse_vendor_pk_hash[2][18-1:0]);
  assign bus_fuse_vendor_pk_hash[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_vendor_pk_hash[2]}};

  assign hit_fuse_vendor_pk_hash[3] = (soc_ifc_reg_req_data.addr == full_addr_fuse_vendor_pk_hash[3][18-1:0]);
  assign bus_fuse_vendor_pk_hash[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_vendor_pk_hash[3]}};

  assign hit_fuse_vendor_pk_hash[4] = (soc_ifc_reg_req_data.addr == full_addr_fuse_vendor_pk_hash[4][18-1:0]);
  assign bus_fuse_vendor_pk_hash[4] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_vendor_pk_hash[4]}};

  assign hit_fuse_vendor_pk_hash[5] = (soc_ifc_reg_req_data.addr == full_addr_fuse_vendor_pk_hash[5][18-1:0]);
  assign bus_fuse_vendor_pk_hash[5] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_vendor_pk_hash[5]}};

  assign hit_fuse_vendor_pk_hash[6] = (soc_ifc_reg_req_data.addr == full_addr_fuse_vendor_pk_hash[6][18-1:0]);
  assign bus_fuse_vendor_pk_hash[6] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_vendor_pk_hash[6]}};

  assign hit_fuse_vendor_pk_hash[7] = (soc_ifc_reg_req_data.addr == full_addr_fuse_vendor_pk_hash[7][18-1:0]);
  assign bus_fuse_vendor_pk_hash[7] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_vendor_pk_hash[7]}};

  assign hit_fuse_vendor_pk_hash[8] = (soc_ifc_reg_req_data.addr == full_addr_fuse_vendor_pk_hash[8][18-1:0]);
  assign bus_fuse_vendor_pk_hash[8] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_vendor_pk_hash[8]}};

  assign hit_fuse_vendor_pk_hash[9] = (soc_ifc_reg_req_data.addr == full_addr_fuse_vendor_pk_hash[9][18-1:0]);
  assign bus_fuse_vendor_pk_hash[9] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_vendor_pk_hash[9]}};

  assign hit_fuse_vendor_pk_hash[10] = (soc_ifc_reg_req_data.addr == full_addr_fuse_vendor_pk_hash[10][18-1:0]);
  assign bus_fuse_vendor_pk_hash[10] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_vendor_pk_hash[10]}};

  assign hit_fuse_vendor_pk_hash[11] = (soc_ifc_reg_req_data.addr == full_addr_fuse_vendor_pk_hash[11][18-1:0]);
  assign bus_fuse_vendor_pk_hash[11] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_vendor_pk_hash[11]}};

  assign hit_fuse_ecc_revocation = (soc_ifc_reg_req_data.addr == full_addr_fuse_ecc_revocation[AXI_ADDR_WIDTH-1:0]);
  assign bus_fuse_ecc_revocation = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_ecc_revocation}};

  assign hit_fuse_fmc_key_manifest_svn = (soc_ifc_reg_req_data.addr == full_addr_fuse_fmc_key_manifest_svn[AXI_ADDR_WIDTH-1:0]);
  assign bus_fuse_fmc_key_manifest_svn = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_fmc_key_manifest_svn}};

  assign hit_fuse_runtime_svn[0] = (soc_ifc_reg_req_data.addr == full_addr_fuse_runtime_svn[0][18-1:0]);
  assign bus_fuse_runtime_svn[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_runtime_svn[0]}};

  assign hit_fuse_runtime_svn[1] = (soc_ifc_reg_req_data.addr == full_addr_fuse_runtime_svn[1][18-1:0]);
  assign bus_fuse_runtime_svn[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_runtime_svn[1]}};

  assign hit_fuse_runtime_svn[2] = (soc_ifc_reg_req_data.addr == full_addr_fuse_runtime_svn[2][18-1:0]);
  assign bus_fuse_runtime_svn[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_runtime_svn[2]}};

  assign hit_fuse_runtime_svn[3] = (soc_ifc_reg_req_data.addr == full_addr_fuse_runtime_svn[3][18-1:0]);
  assign bus_fuse_runtime_svn[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_runtime_svn[3]}};

  assign hit_fuse_anti_rollback_disable = (soc_ifc_reg_req_data.addr == full_addr_fuse_anti_rollback_disable[AXI_ADDR_WIDTH-1:0]);
  assign bus_fuse_anti_rollback_disable = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_anti_rollback_disable}};

  assign hit_fuse_idevid_cert_attr[0] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[0][18-1:0]);
  assign bus_fuse_idevid_cert_attr[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[0]}};

  assign hit_fuse_idevid_cert_attr[1] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[1][18-1:0]);
  assign bus_fuse_idevid_cert_attr[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[1]}};

  assign hit_fuse_idevid_cert_attr[2] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[2][18-1:0]);
  assign bus_fuse_idevid_cert_attr[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[2]}};

  assign hit_fuse_idevid_cert_attr[3] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[3][18-1:0]);
  assign bus_fuse_idevid_cert_attr[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[3]}};

  assign hit_fuse_idevid_cert_attr[4] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[4][18-1:0]);
  assign bus_fuse_idevid_cert_attr[4] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[4]}};

  assign hit_fuse_idevid_cert_attr[5] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[5][18-1:0]);
  assign bus_fuse_idevid_cert_attr[5] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[5]}};

  assign hit_fuse_idevid_cert_attr[6] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[6][18-1:0]);
  assign bus_fuse_idevid_cert_attr[6] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[6]}};

  assign hit_fuse_idevid_cert_attr[7] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[7][18-1:0]);
  assign bus_fuse_idevid_cert_attr[7] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[7]}};

  assign hit_fuse_idevid_cert_attr[8] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[8][18-1:0]);
  assign bus_fuse_idevid_cert_attr[8] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[8]}};

  assign hit_fuse_idevid_cert_attr[9] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[9][18-1:0]);
  assign bus_fuse_idevid_cert_attr[9] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[9]}};

  assign hit_fuse_idevid_cert_attr[10] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[10][18-1:0]);
  assign bus_fuse_idevid_cert_attr[10] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[10]}};

  assign hit_fuse_idevid_cert_attr[11] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[11][18-1:0]);
  assign bus_fuse_idevid_cert_attr[11] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[11]}};

  assign hit_fuse_idevid_cert_attr[12] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[12][18-1:0]);
  assign bus_fuse_idevid_cert_attr[12] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[12]}};

  assign hit_fuse_idevid_cert_attr[13] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[13][18-1:0]);
  assign bus_fuse_idevid_cert_attr[13] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[13]}};

  assign hit_fuse_idevid_cert_attr[14] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[14][18-1:0]);
  assign bus_fuse_idevid_cert_attr[14] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[14]}};

  assign hit_fuse_idevid_cert_attr[15] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[15][18-1:0]);
  assign bus_fuse_idevid_cert_attr[15] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[15]}};

  assign hit_fuse_idevid_cert_attr[16] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[16][18-1:0]);
  assign bus_fuse_idevid_cert_attr[16] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[16]}};

  assign hit_fuse_idevid_cert_attr[17] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[17][18-1:0]);
  assign bus_fuse_idevid_cert_attr[17] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[17]}};

  assign hit_fuse_idevid_cert_attr[18] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[18][18-1:0]);
  assign bus_fuse_idevid_cert_attr[18] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[18]}};

  assign hit_fuse_idevid_cert_attr[19] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[19][18-1:0]);
  assign bus_fuse_idevid_cert_attr[19] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[19]}};

  assign hit_fuse_idevid_cert_attr[20] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[20][18-1:0]);
  assign bus_fuse_idevid_cert_attr[20] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[20]}};

  assign hit_fuse_idevid_cert_attr[21] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[21][18-1:0]);
  assign bus_fuse_idevid_cert_attr[21] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[21]}};

  assign hit_fuse_idevid_cert_attr[22] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[22][18-1:0]);
  assign bus_fuse_idevid_cert_attr[22] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[22]}};

  assign hit_fuse_idevid_cert_attr[23] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_cert_attr[23][18-1:0]);
  assign bus_fuse_idevid_cert_attr[23] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_cert_attr[23]}};

  assign hit_fuse_idevid_manuf_hsm_id[0] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_manuf_hsm_id[0][18-1:0]);
  assign bus_fuse_idevid_manuf_hsm_id[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_manuf_hsm_id[0]}};

  assign hit_fuse_idevid_manuf_hsm_id[1] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_manuf_hsm_id[1][18-1:0]);
  assign bus_fuse_idevid_manuf_hsm_id[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_manuf_hsm_id[1]}};

  assign hit_fuse_idevid_manuf_hsm_id[2] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_manuf_hsm_id[2][18-1:0]);
  assign bus_fuse_idevid_manuf_hsm_id[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_manuf_hsm_id[2]}};

  assign hit_fuse_idevid_manuf_hsm_id[3] = (soc_ifc_reg_req_data.addr == full_addr_fuse_idevid_manuf_hsm_id[3][18-1:0]);
  assign bus_fuse_idevid_manuf_hsm_id[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_idevid_manuf_hsm_id[3]}};

  assign hit_fuse_lms_revocation = (soc_ifc_reg_req_data.addr == full_addr_fuse_lms_revocation[AXI_ADDR_WIDTH-1:0]);
  assign bus_fuse_lms_revocation = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_lms_revocation}};

  assign hit_fuse_mldsa_revocation = (soc_ifc_reg_req_data.addr == full_addr_fuse_mldsa_revocation[AXI_ADDR_WIDTH-1:0]);
  assign bus_fuse_mldsa_revocation = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_mldsa_revocation}};

  assign hit_fuse_soc_stepping_id = (soc_ifc_reg_req_data.addr == full_addr_fuse_soc_stepping_id[AXI_ADDR_WIDTH-1:0]);
  assign bus_fuse_soc_stepping_id = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_soc_stepping_id}};

  assign hit_fuse_manuf_dbg_unlock_token[0] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[0][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[0]}};

  assign hit_fuse_manuf_dbg_unlock_token[1] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[1][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[1]}};

  assign hit_fuse_manuf_dbg_unlock_token[2] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[2][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[2]}};

  assign hit_fuse_manuf_dbg_unlock_token[3] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[3][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[3]}};

  assign hit_fuse_manuf_dbg_unlock_token[4] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[4][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[4] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[4]}};

  assign hit_fuse_manuf_dbg_unlock_token[5] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[5][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[5] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[5]}};

  assign hit_fuse_manuf_dbg_unlock_token[6] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[6][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[6] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[6]}};

  assign hit_fuse_manuf_dbg_unlock_token[7] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[7][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[7] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[7]}};

  assign hit_fuse_manuf_dbg_unlock_token[8] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[8][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[8] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[8]}};

  assign hit_fuse_manuf_dbg_unlock_token[9] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[9][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[9] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[9]}};

  assign hit_fuse_manuf_dbg_unlock_token[10] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[10][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[10] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[10]}};

  assign hit_fuse_manuf_dbg_unlock_token[11] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[11][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[11] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[11]}};

  assign hit_fuse_manuf_dbg_unlock_token[12] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[12][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[12] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[12]}};

  assign hit_fuse_manuf_dbg_unlock_token[13] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[13][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[13] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[13]}};

  assign hit_fuse_manuf_dbg_unlock_token[14] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[14][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[14] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[14]}};

  assign hit_fuse_manuf_dbg_unlock_token[15] = (soc_ifc_reg_req_data.addr == full_addr_fuse_manuf_dbg_unlock_token[15][18-1:0]);
  assign bus_fuse_manuf_dbg_unlock_token[15] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_manuf_dbg_unlock_token[15]}};

  assign hit_fuse_pqc_key_type = (soc_ifc_reg_req_data.addr == full_addr_fuse_pqc_key_type[AXI_ADDR_WIDTH-1:0]);
  assign bus_fuse_pqc_key_type = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_pqc_key_type}};

  assign hit_fuse_soc_manifest_svn[0] = (soc_ifc_reg_req_data.addr == full_addr_fuse_soc_manifest_svn[0][18-1:0]);
  assign bus_fuse_soc_manifest_svn[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_soc_manifest_svn[0]}};

  assign hit_fuse_soc_manifest_svn[1] = (soc_ifc_reg_req_data.addr == full_addr_fuse_soc_manifest_svn[1][18-1:0]);
  assign bus_fuse_soc_manifest_svn[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_soc_manifest_svn[1]}};

  assign hit_fuse_soc_manifest_svn[2] = (soc_ifc_reg_req_data.addr == full_addr_fuse_soc_manifest_svn[2][18-1:0]);
  assign bus_fuse_soc_manifest_svn[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_soc_manifest_svn[2]}};

  assign hit_fuse_soc_manifest_svn[3] = (soc_ifc_reg_req_data.addr == full_addr_fuse_soc_manifest_svn[3][18-1:0]);
  assign bus_fuse_soc_manifest_svn[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_soc_manifest_svn[3]}};

  assign hit_fuse_soc_manifest_max_svn = (soc_ifc_reg_req_data.addr == full_addr_fuse_soc_manifest_max_svn[AXI_ADDR_WIDTH-1:0]);
  assign bus_fuse_soc_manifest_max_svn = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_soc_manifest_max_svn}};

  assign hit_fuse_hek_seed[0] = (soc_ifc_reg_req_data.addr == full_addr_fuse_hek_seed[0][18-1:0]);
  assign bus_fuse_hek_seed[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_hek_seed[0]}};

  assign hit_fuse_hek_seed[1] = (soc_ifc_reg_req_data.addr == full_addr_fuse_hek_seed[1][18-1:0]);
  assign bus_fuse_hek_seed[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_hek_seed[1]}};

  assign hit_fuse_hek_seed[2] = (soc_ifc_reg_req_data.addr == full_addr_fuse_hek_seed[2][18-1:0]);
  assign bus_fuse_hek_seed[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_hek_seed[2]}};

  assign hit_fuse_hek_seed[3] = (soc_ifc_reg_req_data.addr == full_addr_fuse_hek_seed[3][18-1:0]);
  assign bus_fuse_hek_seed[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_hek_seed[3]}};

  assign hit_fuse_hek_seed[4] = (soc_ifc_reg_req_data.addr == full_addr_fuse_hek_seed[4][18-1:0]);
  assign bus_fuse_hek_seed[4] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_hek_seed[4]}};

  assign hit_fuse_hek_seed[5] = (soc_ifc_reg_req_data.addr == full_addr_fuse_hek_seed[5][18-1:0]);
  assign bus_fuse_hek_seed[5] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_hek_seed[5]}};

  assign hit_fuse_hek_seed[6] = (soc_ifc_reg_req_data.addr == full_addr_fuse_hek_seed[6][18-1:0]);
  assign bus_fuse_hek_seed[6] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_hek_seed[6]}};

  assign hit_fuse_hek_seed[7] = (soc_ifc_reg_req_data.addr == full_addr_fuse_hek_seed[7][18-1:0]);
  assign bus_fuse_hek_seed[7] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_fuse_hek_seed[7]}};

  assign hit_SS_CALIPTRA_BASE_ADDR_L = (soc_ifc_reg_req_data.addr == full_addr_SS_CALIPTRA_BASE_ADDR_L[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_CALIPTRA_BASE_ADDR_L = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_CALIPTRA_BASE_ADDR_L}};

  assign hit_SS_CALIPTRA_BASE_ADDR_H = (soc_ifc_reg_req_data.addr == full_addr_SS_CALIPTRA_BASE_ADDR_H[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_CALIPTRA_BASE_ADDR_H = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_CALIPTRA_BASE_ADDR_H}};

  assign hit_SS_MCI_BASE_ADDR_L = (soc_ifc_reg_req_data.addr == full_addr_SS_MCI_BASE_ADDR_L[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_MCI_BASE_ADDR_L = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_MCI_BASE_ADDR_L}};

  assign hit_SS_MCI_BASE_ADDR_H = (soc_ifc_reg_req_data.addr == full_addr_SS_MCI_BASE_ADDR_H[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_MCI_BASE_ADDR_H = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_MCI_BASE_ADDR_H}};

  assign hit_SS_RECOVERY_IFC_BASE_ADDR_L = (soc_ifc_reg_req_data.addr == full_addr_SS_RECOVERY_IFC_BASE_ADDR_L[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_RECOVERY_IFC_BASE_ADDR_L = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_RECOVERY_IFC_BASE_ADDR_L}};

  assign hit_SS_RECOVERY_IFC_BASE_ADDR_H = (soc_ifc_reg_req_data.addr == full_addr_SS_RECOVERY_IFC_BASE_ADDR_H[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_RECOVERY_IFC_BASE_ADDR_H = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_RECOVERY_IFC_BASE_ADDR_H}};

  assign hit_SS_OTP_FC_BASE_ADDR_L = (soc_ifc_reg_req_data.addr == full_addr_SS_OTP_FC_BASE_ADDR_L[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_OTP_FC_BASE_ADDR_L = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_OTP_FC_BASE_ADDR_L}};

  assign hit_SS_OTP_FC_BASE_ADDR_H = (soc_ifc_reg_req_data.addr == full_addr_SS_OTP_FC_BASE_ADDR_H[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_OTP_FC_BASE_ADDR_H = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_OTP_FC_BASE_ADDR_H}};

  assign hit_SS_UDS_SEED_BASE_ADDR_L = (soc_ifc_reg_req_data.addr == full_addr_SS_UDS_SEED_BASE_ADDR_L[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_UDS_SEED_BASE_ADDR_L = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_UDS_SEED_BASE_ADDR_L}};

  assign hit_SS_UDS_SEED_BASE_ADDR_H = (soc_ifc_reg_req_data.addr == full_addr_SS_UDS_SEED_BASE_ADDR_H[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_UDS_SEED_BASE_ADDR_H = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_UDS_SEED_BASE_ADDR_H}};

  assign hit_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET = (soc_ifc_reg_req_data.addr == full_addr_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET}};

  assign hit_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES = (soc_ifc_reg_req_data.addr == full_addr_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES}};

  assign hit_SS_DEBUG_INTENT = (soc_ifc_reg_req_data.addr == full_addr_SS_DEBUG_INTENT[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_DEBUG_INTENT = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_DEBUG_INTENT}};

  assign hit_SS_CALIPTRA_DMA_AXI_USER = (soc_ifc_reg_req_data.addr == full_addr_SS_CALIPTRA_DMA_AXI_USER[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_CALIPTRA_DMA_AXI_USER = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_CALIPTRA_DMA_AXI_USER}};

  assign hit_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L = (soc_ifc_reg_req_data.addr == full_addr_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L}};

  assign hit_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H = (soc_ifc_reg_req_data.addr == full_addr_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H}};

  assign hit_SS_KEY_RELEASE_BASE_ADDR_L = (soc_ifc_reg_req_data.addr == full_addr_SS_KEY_RELEASE_BASE_ADDR_L[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_KEY_RELEASE_BASE_ADDR_L = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_KEY_RELEASE_BASE_ADDR_L}};

  assign hit_SS_KEY_RELEASE_BASE_ADDR_H = (soc_ifc_reg_req_data.addr == full_addr_SS_KEY_RELEASE_BASE_ADDR_H[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_KEY_RELEASE_BASE_ADDR_H = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_KEY_RELEASE_BASE_ADDR_H}};

  assign hit_SS_KEY_RELEASE_SIZE = (soc_ifc_reg_req_data.addr == full_addr_SS_KEY_RELEASE_SIZE[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_KEY_RELEASE_SIZE = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_KEY_RELEASE_SIZE}};

  assign hit_SS_OCP_LOCK_CTRL = (soc_ifc_reg_req_data.addr == full_addr_SS_OCP_LOCK_CTRL[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_OCP_LOCK_CTRL = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_OCP_LOCK_CTRL}};

  assign hit_SS_STRAP_GENERIC[0] = (soc_ifc_reg_req_data.addr == full_addr_SS_STRAP_GENERIC[0][18-1:0]);
  assign bus_SS_STRAP_GENERIC[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_STRAP_GENERIC[0]}};

  assign hit_SS_STRAP_GENERIC[1] = (soc_ifc_reg_req_data.addr == full_addr_SS_STRAP_GENERIC[1][18-1:0]);
  assign bus_SS_STRAP_GENERIC[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_STRAP_GENERIC[1]}};

  assign hit_SS_STRAP_GENERIC[2] = (soc_ifc_reg_req_data.addr == full_addr_SS_STRAP_GENERIC[2][18-1:0]);
  assign bus_SS_STRAP_GENERIC[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_STRAP_GENERIC[2]}};

  assign hit_SS_STRAP_GENERIC[3] = (soc_ifc_reg_req_data.addr == full_addr_SS_STRAP_GENERIC[3][18-1:0]);
  assign bus_SS_STRAP_GENERIC[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_STRAP_GENERIC[3]}};

  assign hit_SS_DBG_SERVICE_REG_REQ = (soc_ifc_reg_req_data.addr == full_addr_SS_DBG_SERVICE_REG_REQ[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_DBG_SERVICE_REG_REQ = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_DBG_SERVICE_REG_REQ}};

  assign hit_SS_DBG_SERVICE_REG_RSP = (soc_ifc_reg_req_data.addr == full_addr_SS_DBG_SERVICE_REG_RSP[AXI_ADDR_WIDTH-1:0]);
  assign bus_SS_DBG_SERVICE_REG_RSP = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_DBG_SERVICE_REG_RSP}};

  assign hit_SS_SOC_DBG_UNLOCK_LEVEL[0] = (soc_ifc_reg_req_data.addr == full_addr_SS_SOC_DBG_UNLOCK_LEVEL[0][18-1:0]);
  assign bus_SS_SOC_DBG_UNLOCK_LEVEL[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_SOC_DBG_UNLOCK_LEVEL[0]}};

  assign hit_SS_SOC_DBG_UNLOCK_LEVEL[1] = (soc_ifc_reg_req_data.addr == full_addr_SS_SOC_DBG_UNLOCK_LEVEL[1][18-1:0]);
  assign bus_SS_SOC_DBG_UNLOCK_LEVEL[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_SOC_DBG_UNLOCK_LEVEL[1]}};

  assign hit_SS_GENERIC_FW_EXEC_CTRL[0] = (soc_ifc_reg_req_data.addr == full_addr_SS_GENERIC_FW_EXEC_CTRL[0][18-1:0]);
  assign bus_SS_GENERIC_FW_EXEC_CTRL[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_GENERIC_FW_EXEC_CTRL[0]}};

  assign hit_SS_GENERIC_FW_EXEC_CTRL[1] = (soc_ifc_reg_req_data.addr == full_addr_SS_GENERIC_FW_EXEC_CTRL[1][18-1:0]);
  assign bus_SS_GENERIC_FW_EXEC_CTRL[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_GENERIC_FW_EXEC_CTRL[1]}};

  assign hit_SS_GENERIC_FW_EXEC_CTRL[2] = (soc_ifc_reg_req_data.addr == full_addr_SS_GENERIC_FW_EXEC_CTRL[2][18-1:0]);
  assign bus_SS_GENERIC_FW_EXEC_CTRL[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_GENERIC_FW_EXEC_CTRL[2]}};

  assign hit_SS_GENERIC_FW_EXEC_CTRL[3] = (soc_ifc_reg_req_data.addr == full_addr_SS_GENERIC_FW_EXEC_CTRL[3][18-1:0]);
  assign bus_SS_GENERIC_FW_EXEC_CTRL[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_SS_GENERIC_FW_EXEC_CTRL[3]}};

  assign hit_internal_obf_key[0] = (soc_ifc_reg_req_data.addr == full_addr_internal_obf_key[0][18-1:0]);
  assign bus_internal_obf_key[0] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_obf_key[0]}};

  assign hit_internal_obf_key[1] = (soc_ifc_reg_req_data.addr == full_addr_internal_obf_key[1][18-1:0]);
  assign bus_internal_obf_key[1] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_obf_key[1]}};

  assign hit_internal_obf_key[2] = (soc_ifc_reg_req_data.addr == full_addr_internal_obf_key[2][18-1:0]);
  assign bus_internal_obf_key[2] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_obf_key[2]}};

  assign hit_internal_obf_key[3] = (soc_ifc_reg_req_data.addr == full_addr_internal_obf_key[3][18-1:0]);
  assign bus_internal_obf_key[3] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_obf_key[3]}};

  assign hit_internal_obf_key[4] = (soc_ifc_reg_req_data.addr == full_addr_internal_obf_key[4][18-1:0]);
  assign bus_internal_obf_key[4] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_obf_key[4]}};

  assign hit_internal_obf_key[5] = (soc_ifc_reg_req_data.addr == full_addr_internal_obf_key[5][18-1:0]);
  assign bus_internal_obf_key[5] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_obf_key[5]}};

  assign hit_internal_obf_key[6] = (soc_ifc_reg_req_data.addr == full_addr_internal_obf_key[6][18-1:0]);
  assign bus_internal_obf_key[6] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_obf_key[6]}};

  assign hit_internal_obf_key[7] = (soc_ifc_reg_req_data.addr == full_addr_internal_obf_key[7][18-1:0]);
  assign bus_internal_obf_key[7] = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_obf_key[7]}};

  assign hit_internal_iccm_lock = (soc_ifc_reg_req_data.addr == full_addr_internal_iccm_lock[AXI_ADDR_WIDTH-1:0]);
  assign bus_internal_iccm_lock = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_iccm_lock}};

  assign hit_internal_fw_update_reset = (soc_ifc_reg_req_data.addr == full_addr_internal_fw_update_reset[AXI_ADDR_WIDTH-1:0]);
  assign bus_internal_fw_update_reset = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_fw_update_reset}};

  assign hit_internal_fw_update_reset_wait_cycles = (soc_ifc_reg_req_data.addr == full_addr_internal_fw_update_reset_wait_cycles[AXI_ADDR_WIDTH-1:0]);
  assign bus_internal_fw_update_reset_wait_cycles = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_fw_update_reset_wait_cycles}};

  assign hit_internal_nmi_vector = (soc_ifc_reg_req_data.addr == full_addr_internal_nmi_vector[AXI_ADDR_WIDTH-1:0]);
  assign bus_internal_nmi_vector = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_nmi_vector}};

  assign hit_internal_hw_error_fatal_mask = (soc_ifc_reg_req_data.addr == full_addr_internal_hw_error_fatal_mask[AXI_ADDR_WIDTH-1:0]);
  assign bus_internal_hw_error_fatal_mask = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_hw_error_fatal_mask}};

  assign hit_internal_hw_error_non_fatal_mask = (soc_ifc_reg_req_data.addr == full_addr_internal_hw_error_non_fatal_mask[AXI_ADDR_WIDTH-1:0]);
  assign bus_internal_hw_error_non_fatal_mask = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_hw_error_non_fatal_mask}};

  assign hit_internal_fw_error_fatal_mask = (soc_ifc_reg_req_data.addr == full_addr_internal_fw_error_fatal_mask[AXI_ADDR_WIDTH-1:0]);
  assign bus_internal_fw_error_fatal_mask = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_fw_error_fatal_mask}};

  assign hit_internal_fw_error_non_fatal_mask = (soc_ifc_reg_req_data.addr == full_addr_internal_fw_error_non_fatal_mask[AXI_ADDR_WIDTH-1:0]);
  assign bus_internal_fw_error_non_fatal_mask = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_fw_error_non_fatal_mask}};

  assign hit_internal_rv_mtime_l = (soc_ifc_reg_req_data.addr == full_addr_internal_rv_mtime_l[AXI_ADDR_WIDTH-1:0]);
  assign bus_internal_rv_mtime_l = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_rv_mtime_l}};

  assign hit_internal_rv_mtime_h = (soc_ifc_reg_req_data.addr == full_addr_internal_rv_mtime_h[AXI_ADDR_WIDTH-1:0]);
  assign bus_internal_rv_mtime_h = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_rv_mtime_h}};

  assign hit_internal_rv_mtimecmp_l = (soc_ifc_reg_req_data.addr == full_addr_internal_rv_mtimecmp_l[AXI_ADDR_WIDTH-1:0]);
  assign bus_internal_rv_mtimecmp_l = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_rv_mtimecmp_l}};

  assign hit_internal_rv_mtimecmp_h = (soc_ifc_reg_req_data.addr == full_addr_internal_rv_mtimecmp_h[AXI_ADDR_WIDTH-1:0]);
  assign bus_internal_rv_mtimecmp_h = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_internal_rv_mtimecmp_h}};

  assign hit_intr_brf_global_intr_en_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_global_intr_en_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_global_intr_en_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_global_intr_en_r}};

  assign hit_intr_brf_error_intr_en_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_intr_en_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_intr_en_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_intr_en_r}};

  assign hit_intr_brf_notif_intr_en_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_intr_en_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_intr_en_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_intr_en_r}};

  assign hit_intr_brf_error_global_intr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_global_intr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_global_intr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_global_intr_r}};

  assign hit_intr_brf_notif_global_intr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_global_intr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_global_intr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_global_intr_r}};

  assign hit_intr_brf_error_internal_intr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_internal_intr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_internal_intr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_internal_intr_r}};

  assign hit_intr_brf_notif_internal_intr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_internal_intr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_internal_intr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_internal_intr_r}};

  assign hit_intr_brf_error_intr_trig_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_intr_trig_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_intr_trig_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_intr_trig_r}};

  assign hit_intr_brf_notif_intr_trig_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_intr_trig_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_intr_trig_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_intr_trig_r}};

  assign hit_intr_brf_error_internal_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_internal_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_internal_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_internal_intr_count_r}};

  assign hit_intr_brf_error_inv_dev_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_inv_dev_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_inv_dev_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_inv_dev_intr_count_r}};

  assign hit_intr_brf_error_cmd_fail_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_cmd_fail_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_cmd_fail_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_cmd_fail_intr_count_r}};

  assign hit_intr_brf_error_bad_fuse_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_bad_fuse_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_bad_fuse_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_bad_fuse_intr_count_r}};

  assign hit_intr_brf_error_iccm_blocked_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_iccm_blocked_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_iccm_blocked_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_iccm_blocked_intr_count_r}};

  assign hit_intr_brf_error_mbox_ecc_unc_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_mbox_ecc_unc_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_mbox_ecc_unc_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_mbox_ecc_unc_intr_count_r}};

  assign hit_intr_brf_error_wdt_timer1_timeout_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_wdt_timer1_timeout_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_wdt_timer1_timeout_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_wdt_timer1_timeout_intr_count_r}};

  assign hit_intr_brf_error_wdt_timer2_timeout_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_wdt_timer2_timeout_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_wdt_timer2_timeout_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_wdt_timer2_timeout_intr_count_r}};

  assign hit_intr_brf_notif_cmd_avail_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_cmd_avail_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_cmd_avail_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_cmd_avail_intr_count_r}};

  assign hit_intr_brf_notif_mbox_ecc_cor_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_mbox_ecc_cor_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_mbox_ecc_cor_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_mbox_ecc_cor_intr_count_r}};

  assign hit_intr_brf_notif_debug_locked_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_debug_locked_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_debug_locked_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_debug_locked_intr_count_r}};

  assign hit_intr_brf_notif_scan_mode_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_scan_mode_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_scan_mode_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_scan_mode_intr_count_r}};

  assign hit_intr_brf_notif_soc_req_lock_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_soc_req_lock_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_soc_req_lock_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_soc_req_lock_intr_count_r}};

  assign hit_intr_brf_notif_gen_in_toggle_intr_count_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_gen_in_toggle_intr_count_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_gen_in_toggle_intr_count_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_gen_in_toggle_intr_count_r}};

  assign hit_intr_brf_error_internal_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_internal_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_internal_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_internal_intr_count_incr_r}};

  assign hit_intr_brf_error_inv_dev_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_inv_dev_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_inv_dev_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_inv_dev_intr_count_incr_r}};

  assign hit_intr_brf_error_cmd_fail_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_cmd_fail_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_cmd_fail_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_cmd_fail_intr_count_incr_r}};

  assign hit_intr_brf_error_bad_fuse_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_bad_fuse_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_bad_fuse_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_bad_fuse_intr_count_incr_r}};

  assign hit_intr_brf_error_iccm_blocked_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_iccm_blocked_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_iccm_blocked_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_iccm_blocked_intr_count_incr_r}};

  assign hit_intr_brf_error_mbox_ecc_unc_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_mbox_ecc_unc_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_mbox_ecc_unc_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_mbox_ecc_unc_intr_count_incr_r}};

  assign hit_intr_brf_error_wdt_timer1_timeout_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_wdt_timer1_timeout_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_wdt_timer1_timeout_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_wdt_timer1_timeout_intr_count_incr_r}};

  assign hit_intr_brf_error_wdt_timer2_timeout_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_error_wdt_timer2_timeout_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_error_wdt_timer2_timeout_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_error_wdt_timer2_timeout_intr_count_incr_r}};

  assign hit_intr_brf_notif_cmd_avail_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_cmd_avail_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_cmd_avail_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_cmd_avail_intr_count_incr_r}};

  assign hit_intr_brf_notif_mbox_ecc_cor_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_mbox_ecc_cor_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_mbox_ecc_cor_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_mbox_ecc_cor_intr_count_incr_r}};

  assign hit_intr_brf_notif_debug_locked_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_debug_locked_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_debug_locked_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_debug_locked_intr_count_incr_r}};

  assign hit_intr_brf_notif_scan_mode_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_scan_mode_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_scan_mode_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_scan_mode_intr_count_incr_r}};

  assign hit_intr_brf_notif_soc_req_lock_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_soc_req_lock_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_soc_req_lock_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_soc_req_lock_intr_count_incr_r}};

  assign hit_intr_brf_notif_gen_in_toggle_intr_count_incr_r = (soc_ifc_reg_req_data.addr == full_addr_intr_brf_notif_gen_in_toggle_intr_count_incr_r[AXI_ADDR_WIDTH-1:0]);
  assign bus_intr_brf_notif_gen_in_toggle_intr_count_incr_r = {uc_rd, uc_wr, soc_rd, soc_wr} & {4{hit_intr_brf_notif_gen_in_toggle_intr_count_incr_r}};

  // ----------------------- COVERGROUP CPTRA_HW_ERROR_FATAL -----------------------
  covergroup soc_ifc_CPTRA_HW_ERROR_FATAL_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_HW_ERROR_FATAL_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_HW_ERROR_FATAL;
    bus_CPTRA_HW_ERROR_FATAL_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_HW_ERROR_NON_FATAL -----------------------
  covergroup soc_ifc_CPTRA_HW_ERROR_NON_FATAL_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_HW_ERROR_NON_FATAL_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_HW_ERROR_NON_FATAL;
    bus_CPTRA_HW_ERROR_NON_FATAL_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_FW_ERROR_FATAL -----------------------
  covergroup soc_ifc_CPTRA_FW_ERROR_FATAL_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_FW_ERROR_FATAL_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_ERROR_FATAL;
    bus_CPTRA_FW_ERROR_FATAL_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_FW_ERROR_NON_FATAL -----------------------
  covergroup soc_ifc_CPTRA_FW_ERROR_NON_FATAL_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_FW_ERROR_NON_FATAL_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_ERROR_NON_FATAL;
    bus_CPTRA_FW_ERROR_NON_FATAL_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_HW_ERROR_ENC -----------------------
  covergroup soc_ifc_CPTRA_HW_ERROR_ENC_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_HW_ERROR_ENC_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_HW_ERROR_ENC;
    bus_CPTRA_HW_ERROR_ENC_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_FW_ERROR_ENC -----------------------
  covergroup soc_ifc_CPTRA_FW_ERROR_ENC_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_FW_ERROR_ENC_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_ERROR_ENC;
    bus_CPTRA_FW_ERROR_ENC_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_FW_EXTENDED_ERROR_INFO [0:7] -----------------------
  covergroup soc_ifc_CPTRA_FW_EXTENDED_ERROR_INFO_cg (ref logic [3:0] bus_event[0:7]) @(posedge clk);
    CPTRA_FW_EXTENDED_ERROR_INFO0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_EXTENDED_ERROR_INFO[0];
    bus_CPTRA_FW_EXTENDED_ERROR_INFO0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_FW_EXTENDED_ERROR_INFO1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_EXTENDED_ERROR_INFO[1];
    bus_CPTRA_FW_EXTENDED_ERROR_INFO1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_FW_EXTENDED_ERROR_INFO2_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_EXTENDED_ERROR_INFO[2];
    bus_CPTRA_FW_EXTENDED_ERROR_INFO2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_FW_EXTENDED_ERROR_INFO3_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_EXTENDED_ERROR_INFO[3];
    bus_CPTRA_FW_EXTENDED_ERROR_INFO3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_FW_EXTENDED_ERROR_INFO4_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_EXTENDED_ERROR_INFO[4];
    bus_CPTRA_FW_EXTENDED_ERROR_INFO4_cp : coverpoint bus_event[4] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_FW_EXTENDED_ERROR_INFO5_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_EXTENDED_ERROR_INFO[5];
    bus_CPTRA_FW_EXTENDED_ERROR_INFO5_cp : coverpoint bus_event[5] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_FW_EXTENDED_ERROR_INFO6_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_EXTENDED_ERROR_INFO[6];
    bus_CPTRA_FW_EXTENDED_ERROR_INFO6_cp : coverpoint bus_event[6] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_FW_EXTENDED_ERROR_INFO7_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_EXTENDED_ERROR_INFO[7];
    bus_CPTRA_FW_EXTENDED_ERROR_INFO7_cp : coverpoint bus_event[7] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_BOOT_STATUS -----------------------
  covergroup soc_ifc_CPTRA_BOOT_STATUS_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_BOOT_STATUS_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_BOOT_STATUS;
    bus_CPTRA_BOOT_STATUS_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_FLOW_STATUS -----------------------
  covergroup soc_ifc_CPTRA_FLOW_STATUS_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_FLOW_STATUS_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FLOW_STATUS;
    bus_CPTRA_FLOW_STATUS_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_RESET_REASON -----------------------
  covergroup soc_ifc_CPTRA_RESET_REASON_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_RESET_REASON_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_RESET_REASON;
    bus_CPTRA_RESET_REASON_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // // ----------------------- COVERGROUP CPTRA_SECURITY_STATE -----------------------
  // covergroup soc_ifc_CPTRA_SECURITY_STATE_cg (ref logic [3:0] bus_event) @(posedge clk);
    // CPTRA_SECURITY_STATE_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_SECURITY_STATE;
    // bus_CPTRA_SECURITY_STATE_cp : coverpoint bus_event {
      // bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      // ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
  //   }
  // endgroup

  // ----------------------- COVERGROUP CPTRA_MBOX_VALID_AXI_USER [0:4] -----------------------
  covergroup soc_ifc_CPTRA_MBOX_VALID_AXI_USER_cg (ref logic [3:0] bus_event[0:4]) @(posedge clk);
    CPTRA_MBOX_VALID_AXI_USER0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_MBOX_VALID_AXI_USER[0];
    bus_CPTRA_MBOX_VALID_AXI_USER0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_MBOX_VALID_AXI_USER1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_MBOX_VALID_AXI_USER[1];
    bus_CPTRA_MBOX_VALID_AXI_USER1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_MBOX_VALID_AXI_USER2_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_MBOX_VALID_AXI_USER[2];
    bus_CPTRA_MBOX_VALID_AXI_USER2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_MBOX_VALID_AXI_USER3_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_MBOX_VALID_AXI_USER[3];
    bus_CPTRA_MBOX_VALID_AXI_USER3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_MBOX_VALID_AXI_USER4_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_MBOX_VALID_AXI_USER[4];
    bus_CPTRA_MBOX_VALID_AXI_USER4_cp : coverpoint bus_event[4] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_MBOX_AXI_USER_LOCK [0:4] -----------------------
  covergroup soc_ifc_CPTRA_MBOX_AXI_USER_LOCK_cg (ref logic [3:0] bus_event[0:4]) @(posedge clk);
    CPTRA_MBOX_AXI_USER_LOCK0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_MBOX_AXI_USER_LOCK[0];
    bus_CPTRA_MBOX_AXI_USER_LOCK0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_MBOX_AXI_USER_LOCK1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_MBOX_AXI_USER_LOCK[1];
    bus_CPTRA_MBOX_AXI_USER_LOCK1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_MBOX_AXI_USER_LOCK2_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_MBOX_AXI_USER_LOCK[2];
    bus_CPTRA_MBOX_AXI_USER_LOCK2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_MBOX_AXI_USER_LOCK3_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_MBOX_AXI_USER_LOCK[3];
    bus_CPTRA_MBOX_AXI_USER_LOCK3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_MBOX_AXI_USER_LOCK4_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_MBOX_AXI_USER_LOCK[4];
    bus_CPTRA_MBOX_AXI_USER_LOCK4_cp : coverpoint bus_event[4] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_TRNG_VALID_AXI_USER -----------------------
  covergroup soc_ifc_CPTRA_TRNG_VALID_AXI_USER_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_TRNG_VALID_AXI_USER_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_VALID_AXI_USER;
    bus_CPTRA_TRNG_VALID_AXI_USER_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_TRNG_AXI_USER_LOCK -----------------------
  covergroup soc_ifc_CPTRA_TRNG_AXI_USER_LOCK_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_TRNG_AXI_USER_LOCK_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_AXI_USER_LOCK;
    bus_CPTRA_TRNG_AXI_USER_LOCK_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_TRNG_DATA [0:11] -----------------------
  covergroup soc_ifc_CPTRA_TRNG_DATA_cg (ref logic [3:0] bus_event[0:11]) @(posedge clk);
    CPTRA_TRNG_DATA0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_DATA[0];
    bus_CPTRA_TRNG_DATA0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_TRNG_DATA1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_DATA[1];
    bus_CPTRA_TRNG_DATA1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_TRNG_DATA2_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_DATA[2];
    bus_CPTRA_TRNG_DATA2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_TRNG_DATA3_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_DATA[3];
    bus_CPTRA_TRNG_DATA3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_TRNG_DATA4_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_DATA[4];
    bus_CPTRA_TRNG_DATA4_cp : coverpoint bus_event[4] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_TRNG_DATA5_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_DATA[5];
    bus_CPTRA_TRNG_DATA5_cp : coverpoint bus_event[5] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_TRNG_DATA6_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_DATA[6];
    bus_CPTRA_TRNG_DATA6_cp : coverpoint bus_event[6] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_TRNG_DATA7_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_DATA[7];
    bus_CPTRA_TRNG_DATA7_cp : coverpoint bus_event[7] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_TRNG_DATA8_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_DATA[8];
    bus_CPTRA_TRNG_DATA8_cp : coverpoint bus_event[8] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_TRNG_DATA9_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_DATA[9];
    bus_CPTRA_TRNG_DATA9_cp : coverpoint bus_event[9] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_TRNG_DATA10_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_DATA[10];
    bus_CPTRA_TRNG_DATA10_cp : coverpoint bus_event[10] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_TRNG_DATA11_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_DATA[11];
    bus_CPTRA_TRNG_DATA11_cp : coverpoint bus_event[11] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_TRNG_CTRL -----------------------
  covergroup soc_ifc_CPTRA_TRNG_CTRL_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_TRNG_CTRL_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_CTRL;
    bus_CPTRA_TRNG_CTRL_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_TRNG_STATUS -----------------------
  covergroup soc_ifc_CPTRA_TRNG_STATUS_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_TRNG_STATUS_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TRNG_STATUS;
    bus_CPTRA_TRNG_STATUS_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_FUSE_WR_DONE -----------------------
  covergroup soc_ifc_CPTRA_FUSE_WR_DONE_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_FUSE_WR_DONE_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FUSE_WR_DONE;
    bus_CPTRA_FUSE_WR_DONE_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_TIMER_CONFIG -----------------------
  covergroup soc_ifc_CPTRA_TIMER_CONFIG_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_TIMER_CONFIG_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_TIMER_CONFIG;
    bus_CPTRA_TIMER_CONFIG_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_BOOTFSM_GO -----------------------
  covergroup soc_ifc_CPTRA_BOOTFSM_GO_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_BOOTFSM_GO_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_BOOTFSM_GO;
    bus_CPTRA_BOOTFSM_GO_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_DBG_MANUF_SERVICE_REG -----------------------
  covergroup soc_ifc_CPTRA_DBG_MANUF_SERVICE_REG_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_DBG_MANUF_SERVICE_REG_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_DBG_MANUF_SERVICE_REG;
    bus_CPTRA_DBG_MANUF_SERVICE_REG_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_CLK_GATING_EN -----------------------
  covergroup soc_ifc_CPTRA_CLK_GATING_EN_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_CLK_GATING_EN_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_CLK_GATING_EN;
    bus_CPTRA_CLK_GATING_EN_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_GENERIC_INPUT_WIRES [0:1] -----------------------
  covergroup soc_ifc_CPTRA_GENERIC_INPUT_WIRES_cg (ref logic [3:0] bus_event[0:1]) @(posedge clk);
    CPTRA_GENERIC_INPUT_WIRES0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_GENERIC_INPUT_WIRES[0];
    bus_CPTRA_GENERIC_INPUT_WIRES0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_GENERIC_INPUT_WIRES1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_GENERIC_INPUT_WIRES[1];
    bus_CPTRA_GENERIC_INPUT_WIRES1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_GENERIC_OUTPUT_WIRES [0:1] -----------------------
  covergroup soc_ifc_CPTRA_GENERIC_OUTPUT_WIRES_cg (ref logic [3:0] bus_event[0:1]) @(posedge clk);
    CPTRA_GENERIC_OUTPUT_WIRES0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_GENERIC_OUTPUT_WIRES[0];
    bus_CPTRA_GENERIC_OUTPUT_WIRES0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_GENERIC_OUTPUT_WIRES1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_GENERIC_OUTPUT_WIRES[1];
    bus_CPTRA_GENERIC_OUTPUT_WIRES1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // // ----------------------- COVERGROUP CPTRA_HW_REV_ID -----------------------
  // covergroup soc_ifc_CPTRA_HW_REV_ID_cg (ref logic [3:0] bus_event) @(posedge clk);
    // CPTRA_HW_REV_ID_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_HW_REV_ID;
    // bus_CPTRA_HW_REV_ID_cp : coverpoint bus_event {
      // bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      // ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
  //   }
  // endgroup

  // ----------------------- COVERGROUP CPTRA_FW_REV_ID [0:1] -----------------------
  covergroup soc_ifc_CPTRA_FW_REV_ID_cg (ref logic [3:0] bus_event[0:1]) @(posedge clk);
    CPTRA_FW_REV_ID0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_REV_ID[0];
    bus_CPTRA_FW_REV_ID0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_FW_REV_ID1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_REV_ID[1];
    bus_CPTRA_FW_REV_ID1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // // ----------------------- COVERGROUP CPTRA_HW_CONFIG -----------------------
  // covergroup soc_ifc_CPTRA_HW_CONFIG_cg (ref logic [3:0] bus_event) @(posedge clk);
    // CPTRA_HW_CONFIG_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_HW_CONFIG;
    // bus_CPTRA_HW_CONFIG_cp : coverpoint bus_event {
      // bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      // ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
  //   }
  // endgroup

  // ----------------------- COVERGROUP CPTRA_WDT_TIMER1_EN -----------------------
  covergroup soc_ifc_CPTRA_WDT_TIMER1_EN_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_WDT_TIMER1_EN_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_WDT_TIMER1_EN;
    bus_CPTRA_WDT_TIMER1_EN_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_WDT_TIMER1_CTRL -----------------------
  covergroup soc_ifc_CPTRA_WDT_TIMER1_CTRL_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_WDT_TIMER1_CTRL_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_WDT_TIMER1_CTRL;
    bus_CPTRA_WDT_TIMER1_CTRL_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_WDT_TIMER1_TIMEOUT_PERIOD [0:1] -----------------------
  covergroup soc_ifc_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_cg (ref logic [3:0] bus_event[0:1]) @(posedge clk);
    CPTRA_WDT_TIMER1_TIMEOUT_PERIOD0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[0];
    bus_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_WDT_TIMER1_TIMEOUT_PERIOD1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[1];
    bus_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_WDT_TIMER2_EN -----------------------
  covergroup soc_ifc_CPTRA_WDT_TIMER2_EN_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_WDT_TIMER2_EN_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_WDT_TIMER2_EN;
    bus_CPTRA_WDT_TIMER2_EN_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_WDT_TIMER2_CTRL -----------------------
  covergroup soc_ifc_CPTRA_WDT_TIMER2_CTRL_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_WDT_TIMER2_CTRL_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_WDT_TIMER2_CTRL;
    bus_CPTRA_WDT_TIMER2_CTRL_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_WDT_TIMER2_TIMEOUT_PERIOD [0:1] -----------------------
  covergroup soc_ifc_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_cg (ref logic [3:0] bus_event[0:1]) @(posedge clk);
    CPTRA_WDT_TIMER2_TIMEOUT_PERIOD0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[0];
    bus_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_WDT_TIMER2_TIMEOUT_PERIOD1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[1];
    bus_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_WDT_STATUS -----------------------
  covergroup soc_ifc_CPTRA_WDT_STATUS_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_WDT_STATUS_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_WDT_STATUS;
    bus_CPTRA_WDT_STATUS_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_FUSE_VALID_AXI_USER -----------------------
  covergroup soc_ifc_CPTRA_FUSE_VALID_AXI_USER_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_FUSE_VALID_AXI_USER_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FUSE_VALID_AXI_USER;
    bus_CPTRA_FUSE_VALID_AXI_USER_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_FUSE_AXI_USER_LOCK -----------------------
  covergroup soc_ifc_CPTRA_FUSE_AXI_USER_LOCK_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_FUSE_AXI_USER_LOCK_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FUSE_AXI_USER_LOCK;
    bus_CPTRA_FUSE_AXI_USER_LOCK_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_WDT_CFG [0:1] -----------------------
  covergroup soc_ifc_CPTRA_WDT_CFG_cg (ref logic [3:0] bus_event[0:1]) @(posedge clk);
    CPTRA_WDT_CFG0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_WDT_CFG[0];
    bus_CPTRA_WDT_CFG0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_WDT_CFG1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_WDT_CFG[1];
    bus_CPTRA_WDT_CFG1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_iTRNG_ENTROPY_CONFIG_0 -----------------------
  covergroup soc_ifc_CPTRA_iTRNG_ENTROPY_CONFIG_0_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_iTRNG_ENTROPY_CONFIG_0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_iTRNG_ENTROPY_CONFIG_0;
    bus_CPTRA_iTRNG_ENTROPY_CONFIG_0_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_iTRNG_ENTROPY_CONFIG_1 -----------------------
  covergroup soc_ifc_CPTRA_iTRNG_ENTROPY_CONFIG_1_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_iTRNG_ENTROPY_CONFIG_1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_iTRNG_ENTROPY_CONFIG_1;
    bus_CPTRA_iTRNG_ENTROPY_CONFIG_1_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_RSVD_REG [0:1] -----------------------
  covergroup soc_ifc_CPTRA_RSVD_REG_cg (ref logic [3:0] bus_event[0:1]) @(posedge clk);
    CPTRA_RSVD_REG0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_RSVD_REG[0];
    bus_CPTRA_RSVD_REG0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_RSVD_REG1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_RSVD_REG[1];
    bus_CPTRA_RSVD_REG1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_HW_CAPABILITIES -----------------------
  covergroup soc_ifc_CPTRA_HW_CAPABILITIES_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_HW_CAPABILITIES_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_HW_CAPABILITIES;
    bus_CPTRA_HW_CAPABILITIES_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_FW_CAPABILITIES -----------------------
  covergroup soc_ifc_CPTRA_FW_CAPABILITIES_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_FW_CAPABILITIES_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_FW_CAPABILITIES;
    bus_CPTRA_FW_CAPABILITIES_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_CAP_LOCK -----------------------
  covergroup soc_ifc_CPTRA_CAP_LOCK_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_CAP_LOCK_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_CAP_LOCK;
    bus_CPTRA_CAP_LOCK_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_OWNER_PK_HASH [0:11] -----------------------
  covergroup soc_ifc_CPTRA_OWNER_PK_HASH_cg (ref logic [3:0] bus_event[0:11]) @(posedge clk);
    CPTRA_OWNER_PK_HASH0_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH[0];
    bus_CPTRA_OWNER_PK_HASH0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_OWNER_PK_HASH1_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH[1];
    bus_CPTRA_OWNER_PK_HASH1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_OWNER_PK_HASH2_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH[2];
    bus_CPTRA_OWNER_PK_HASH2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_OWNER_PK_HASH3_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH[3];
    bus_CPTRA_OWNER_PK_HASH3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_OWNER_PK_HASH4_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH[4];
    bus_CPTRA_OWNER_PK_HASH4_cp : coverpoint bus_event[4] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_OWNER_PK_HASH5_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH[5];
    bus_CPTRA_OWNER_PK_HASH5_cp : coverpoint bus_event[5] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_OWNER_PK_HASH6_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH[6];
    bus_CPTRA_OWNER_PK_HASH6_cp : coverpoint bus_event[6] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_OWNER_PK_HASH7_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH[7];
    bus_CPTRA_OWNER_PK_HASH7_cp : coverpoint bus_event[7] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_OWNER_PK_HASH8_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH[8];
    bus_CPTRA_OWNER_PK_HASH8_cp : coverpoint bus_event[8] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_OWNER_PK_HASH9_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH[9];
    bus_CPTRA_OWNER_PK_HASH9_cp : coverpoint bus_event[9] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_OWNER_PK_HASH10_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH[10];
    bus_CPTRA_OWNER_PK_HASH10_cp : coverpoint bus_event[10] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    CPTRA_OWNER_PK_HASH11_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH[11];
    bus_CPTRA_OWNER_PK_HASH11_cp : coverpoint bus_event[11] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP CPTRA_OWNER_PK_HASH_LOCK -----------------------
  covergroup soc_ifc_CPTRA_OWNER_PK_HASH_LOCK_cg (ref logic [3:0] bus_event) @(posedge clk);
    CPTRA_OWNER_PK_HASH_LOCK_cp : coverpoint i_soc_ifc_reg.field_storage.CPTRA_OWNER_PK_HASH_LOCK;
    bus_CPTRA_OWNER_PK_HASH_LOCK_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_uds_seed [0:15] -----------------------
  covergroup soc_ifc_fuse_uds_seed_cg (ref logic [3:0] bus_event[0:15]) @(posedge clk);
    fuse_uds_seed0_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[0];
    bus_fuse_uds_seed0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed1_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[1];
    bus_fuse_uds_seed1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed2_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[2];
    bus_fuse_uds_seed2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed3_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[3];
    bus_fuse_uds_seed3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed4_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[4];
    bus_fuse_uds_seed4_cp : coverpoint bus_event[4] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed5_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[5];
    bus_fuse_uds_seed5_cp : coverpoint bus_event[5] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed6_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[6];
    bus_fuse_uds_seed6_cp : coverpoint bus_event[6] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed7_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[7];
    bus_fuse_uds_seed7_cp : coverpoint bus_event[7] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed8_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[8];
    bus_fuse_uds_seed8_cp : coverpoint bus_event[8] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed9_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[9];
    bus_fuse_uds_seed9_cp : coverpoint bus_event[9] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed10_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[10];
    bus_fuse_uds_seed10_cp : coverpoint bus_event[10] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed11_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[11];
    bus_fuse_uds_seed11_cp : coverpoint bus_event[11] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed12_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[12];
    bus_fuse_uds_seed12_cp : coverpoint bus_event[12] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed13_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[13];
    bus_fuse_uds_seed13_cp : coverpoint bus_event[13] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed14_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[14];
    bus_fuse_uds_seed14_cp : coverpoint bus_event[14] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_uds_seed15_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_uds_seed[15];
    bus_fuse_uds_seed15_cp : coverpoint bus_event[15] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_field_entropy [0:7] -----------------------
  covergroup soc_ifc_fuse_field_entropy_cg (ref logic [3:0] bus_event[0:7]) @(posedge clk);
    fuse_field_entropy0_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_field_entropy[0];
    bus_fuse_field_entropy0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_field_entropy1_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_field_entropy[1];
    bus_fuse_field_entropy1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_field_entropy2_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_field_entropy[2];
    bus_fuse_field_entropy2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_field_entropy3_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_field_entropy[3];
    bus_fuse_field_entropy3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_field_entropy4_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_field_entropy[4];
    bus_fuse_field_entropy4_cp : coverpoint bus_event[4] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_field_entropy5_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_field_entropy[5];
    bus_fuse_field_entropy5_cp : coverpoint bus_event[5] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_field_entropy6_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_field_entropy[6];
    bus_fuse_field_entropy6_cp : coverpoint bus_event[6] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_field_entropy7_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_field_entropy[7];
    bus_fuse_field_entropy7_cp : coverpoint bus_event[7] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_vendor_pk_hash [0:11] -----------------------
  covergroup soc_ifc_fuse_vendor_pk_hash_cg (ref logic [3:0] bus_event[0:11]) @(posedge clk);
    fuse_vendor_pk_hash0_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_vendor_pk_hash[0];
    bus_fuse_vendor_pk_hash0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_vendor_pk_hash1_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_vendor_pk_hash[1];
    bus_fuse_vendor_pk_hash1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_vendor_pk_hash2_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_vendor_pk_hash[2];
    bus_fuse_vendor_pk_hash2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_vendor_pk_hash3_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_vendor_pk_hash[3];
    bus_fuse_vendor_pk_hash3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_vendor_pk_hash4_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_vendor_pk_hash[4];
    bus_fuse_vendor_pk_hash4_cp : coverpoint bus_event[4] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_vendor_pk_hash5_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_vendor_pk_hash[5];
    bus_fuse_vendor_pk_hash5_cp : coverpoint bus_event[5] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_vendor_pk_hash6_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_vendor_pk_hash[6];
    bus_fuse_vendor_pk_hash6_cp : coverpoint bus_event[6] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_vendor_pk_hash7_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_vendor_pk_hash[7];
    bus_fuse_vendor_pk_hash7_cp : coverpoint bus_event[7] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_vendor_pk_hash8_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_vendor_pk_hash[8];
    bus_fuse_vendor_pk_hash8_cp : coverpoint bus_event[8] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_vendor_pk_hash9_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_vendor_pk_hash[9];
    bus_fuse_vendor_pk_hash9_cp : coverpoint bus_event[9] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_vendor_pk_hash10_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_vendor_pk_hash[10];
    bus_fuse_vendor_pk_hash10_cp : coverpoint bus_event[10] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_vendor_pk_hash11_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_vendor_pk_hash[11];
    bus_fuse_vendor_pk_hash11_cp : coverpoint bus_event[11] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_ecc_revocation -----------------------
  covergroup soc_ifc_fuse_ecc_revocation_cg (ref logic [3:0] bus_event) @(posedge clk);
    fuse_ecc_revocation_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_ecc_revocation;
    bus_fuse_ecc_revocation_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_fmc_key_manifest_svn -----------------------
  covergroup soc_ifc_fuse_fmc_key_manifest_svn_cg (ref logic [3:0] bus_event) @(posedge clk);
    fuse_fmc_key_manifest_svn_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_fmc_key_manifest_svn;
    bus_fuse_fmc_key_manifest_svn_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_runtime_svn [0:3] -----------------------
  covergroup soc_ifc_fuse_runtime_svn_cg (ref logic [3:0] bus_event[0:3]) @(posedge clk);
    fuse_runtime_svn0_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_runtime_svn[0];
    bus_fuse_runtime_svn0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_runtime_svn1_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_runtime_svn[1];
    bus_fuse_runtime_svn1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_runtime_svn2_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_runtime_svn[2];
    bus_fuse_runtime_svn2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_runtime_svn3_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_runtime_svn[3];
    bus_fuse_runtime_svn3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_anti_rollback_disable -----------------------
  covergroup soc_ifc_fuse_anti_rollback_disable_cg (ref logic [3:0] bus_event) @(posedge clk);
    fuse_anti_rollback_disable_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_anti_rollback_disable;
    bus_fuse_anti_rollback_disable_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_idevid_cert_attr [0:23] -----------------------
  covergroup soc_ifc_fuse_idevid_cert_attr_cg (ref logic [3:0] bus_event[0:23]) @(posedge clk);
    fuse_idevid_cert_attr0_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[0];
    bus_fuse_idevid_cert_attr0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr1_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[1];
    bus_fuse_idevid_cert_attr1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr2_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[2];
    bus_fuse_idevid_cert_attr2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr3_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[3];
    bus_fuse_idevid_cert_attr3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr4_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[4];
    bus_fuse_idevid_cert_attr4_cp : coverpoint bus_event[4] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr5_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[5];
    bus_fuse_idevid_cert_attr5_cp : coverpoint bus_event[5] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr6_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[6];
    bus_fuse_idevid_cert_attr6_cp : coverpoint bus_event[6] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr7_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[7];
    bus_fuse_idevid_cert_attr7_cp : coverpoint bus_event[7] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr8_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[8];
    bus_fuse_idevid_cert_attr8_cp : coverpoint bus_event[8] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr9_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[9];
    bus_fuse_idevid_cert_attr9_cp : coverpoint bus_event[9] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr10_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[10];
    bus_fuse_idevid_cert_attr10_cp : coverpoint bus_event[10] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr11_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[11];
    bus_fuse_idevid_cert_attr11_cp : coverpoint bus_event[11] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr12_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[12];
    bus_fuse_idevid_cert_attr12_cp : coverpoint bus_event[12] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr13_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[13];
    bus_fuse_idevid_cert_attr13_cp : coverpoint bus_event[13] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr14_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[14];
    bus_fuse_idevid_cert_attr14_cp : coverpoint bus_event[14] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr15_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[15];
    bus_fuse_idevid_cert_attr15_cp : coverpoint bus_event[15] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr16_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[16];
    bus_fuse_idevid_cert_attr16_cp : coverpoint bus_event[16] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr17_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[17];
    bus_fuse_idevid_cert_attr17_cp : coverpoint bus_event[17] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr18_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[18];
    bus_fuse_idevid_cert_attr18_cp : coverpoint bus_event[18] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr19_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[19];
    bus_fuse_idevid_cert_attr19_cp : coverpoint bus_event[19] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr20_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[20];
    bus_fuse_idevid_cert_attr20_cp : coverpoint bus_event[20] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr21_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[21];
    bus_fuse_idevid_cert_attr21_cp : coverpoint bus_event[21] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr22_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[22];
    bus_fuse_idevid_cert_attr22_cp : coverpoint bus_event[22] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_cert_attr23_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_cert_attr[23];
    bus_fuse_idevid_cert_attr23_cp : coverpoint bus_event[23] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_idevid_manuf_hsm_id [0:3] -----------------------
  covergroup soc_ifc_fuse_idevid_manuf_hsm_id_cg (ref logic [3:0] bus_event[0:3]) @(posedge clk);
    fuse_idevid_manuf_hsm_id0_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_manuf_hsm_id[0];
    bus_fuse_idevid_manuf_hsm_id0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_manuf_hsm_id1_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_manuf_hsm_id[1];
    bus_fuse_idevid_manuf_hsm_id1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_manuf_hsm_id2_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_manuf_hsm_id[2];
    bus_fuse_idevid_manuf_hsm_id2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_idevid_manuf_hsm_id3_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_idevid_manuf_hsm_id[3];
    bus_fuse_idevid_manuf_hsm_id3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_lms_revocation -----------------------
  covergroup soc_ifc_fuse_lms_revocation_cg (ref logic [3:0] bus_event) @(posedge clk);
    fuse_lms_revocation_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_lms_revocation;
    bus_fuse_lms_revocation_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_mldsa_revocation -----------------------
  covergroup soc_ifc_fuse_mldsa_revocation_cg (ref logic [3:0] bus_event) @(posedge clk);
    fuse_mldsa_revocation_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_mldsa_revocation;
    bus_fuse_mldsa_revocation_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_soc_stepping_id -----------------------
  covergroup soc_ifc_fuse_soc_stepping_id_cg (ref logic [3:0] bus_event) @(posedge clk);
    fuse_soc_stepping_id_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_soc_stepping_id;
    bus_fuse_soc_stepping_id_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_manuf_dbg_unlock_token [0:15] -----------------------
  covergroup soc_ifc_fuse_manuf_dbg_unlock_token_cg (ref logic [3:0] bus_event[0:15]) @(posedge clk);
    fuse_manuf_dbg_unlock_token0_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[0];
    bus_fuse_manuf_dbg_unlock_token0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token1_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[1];
    bus_fuse_manuf_dbg_unlock_token1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token2_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[2];
    bus_fuse_manuf_dbg_unlock_token2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token3_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[3];
    bus_fuse_manuf_dbg_unlock_token3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token4_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[4];
    bus_fuse_manuf_dbg_unlock_token4_cp : coverpoint bus_event[4] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token5_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[5];
    bus_fuse_manuf_dbg_unlock_token5_cp : coverpoint bus_event[5] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token6_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[6];
    bus_fuse_manuf_dbg_unlock_token6_cp : coverpoint bus_event[6] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token7_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[7];
    bus_fuse_manuf_dbg_unlock_token7_cp : coverpoint bus_event[7] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token8_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[8];
    bus_fuse_manuf_dbg_unlock_token8_cp : coverpoint bus_event[8] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token9_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[9];
    bus_fuse_manuf_dbg_unlock_token9_cp : coverpoint bus_event[9] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token10_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[10];
    bus_fuse_manuf_dbg_unlock_token10_cp : coverpoint bus_event[10] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token11_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[11];
    bus_fuse_manuf_dbg_unlock_token11_cp : coverpoint bus_event[11] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token12_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[12];
    bus_fuse_manuf_dbg_unlock_token12_cp : coverpoint bus_event[12] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token13_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[13];
    bus_fuse_manuf_dbg_unlock_token13_cp : coverpoint bus_event[13] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token14_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[14];
    bus_fuse_manuf_dbg_unlock_token14_cp : coverpoint bus_event[14] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_manuf_dbg_unlock_token15_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_manuf_dbg_unlock_token[15];
    bus_fuse_manuf_dbg_unlock_token15_cp : coverpoint bus_event[15] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_pqc_key_type -----------------------
  covergroup soc_ifc_fuse_pqc_key_type_cg (ref logic [3:0] bus_event) @(posedge clk);
    fuse_pqc_key_type_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_pqc_key_type;
    bus_fuse_pqc_key_type_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_soc_manifest_svn [0:3] -----------------------
  covergroup soc_ifc_fuse_soc_manifest_svn_cg (ref logic [3:0] bus_event[0:3]) @(posedge clk);
    fuse_soc_manifest_svn0_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_soc_manifest_svn[0];
    bus_fuse_soc_manifest_svn0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_soc_manifest_svn1_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_soc_manifest_svn[1];
    bus_fuse_soc_manifest_svn1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_soc_manifest_svn2_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_soc_manifest_svn[2];
    bus_fuse_soc_manifest_svn2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_soc_manifest_svn3_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_soc_manifest_svn[3];
    bus_fuse_soc_manifest_svn3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_soc_manifest_max_svn -----------------------
  covergroup soc_ifc_fuse_soc_manifest_max_svn_cg (ref logic [3:0] bus_event) @(posedge clk);
    fuse_soc_manifest_max_svn_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_soc_manifest_max_svn;
    bus_fuse_soc_manifest_max_svn_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP fuse_hek_seed [0:7] -----------------------
  covergroup soc_ifc_fuse_hek_seed_cg (ref logic [3:0] bus_event[0:7]) @(posedge clk);
    fuse_hek_seed0_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_hek_seed[0];
    bus_fuse_hek_seed0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_hek_seed1_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_hek_seed[1];
    bus_fuse_hek_seed1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_hek_seed2_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_hek_seed[2];
    bus_fuse_hek_seed2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_hek_seed3_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_hek_seed[3];
    bus_fuse_hek_seed3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_hek_seed4_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_hek_seed[4];
    bus_fuse_hek_seed4_cp : coverpoint bus_event[4] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_hek_seed5_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_hek_seed[5];
    bus_fuse_hek_seed5_cp : coverpoint bus_event[5] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_hek_seed6_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_hek_seed[6];
    bus_fuse_hek_seed6_cp : coverpoint bus_event[6] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    fuse_hek_seed7_cp : coverpoint i_soc_ifc_reg.field_storage.fuse_hek_seed[7];
    bus_fuse_hek_seed7_cp : coverpoint bus_event[7] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_CALIPTRA_BASE_ADDR_L -----------------------
  covergroup soc_ifc_SS_CALIPTRA_BASE_ADDR_L_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_CALIPTRA_BASE_ADDR_L_cp : coverpoint i_soc_ifc_reg.field_storage.SS_CALIPTRA_BASE_ADDR_L;
    bus_SS_CALIPTRA_BASE_ADDR_L_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_CALIPTRA_BASE_ADDR_H -----------------------
  covergroup soc_ifc_SS_CALIPTRA_BASE_ADDR_H_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_CALIPTRA_BASE_ADDR_H_cp : coverpoint i_soc_ifc_reg.field_storage.SS_CALIPTRA_BASE_ADDR_H;
    bus_SS_CALIPTRA_BASE_ADDR_H_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_MCI_BASE_ADDR_L -----------------------
  covergroup soc_ifc_SS_MCI_BASE_ADDR_L_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_MCI_BASE_ADDR_L_cp : coverpoint i_soc_ifc_reg.field_storage.SS_MCI_BASE_ADDR_L;
    bus_SS_MCI_BASE_ADDR_L_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_MCI_BASE_ADDR_H -----------------------
  covergroup soc_ifc_SS_MCI_BASE_ADDR_H_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_MCI_BASE_ADDR_H_cp : coverpoint i_soc_ifc_reg.field_storage.SS_MCI_BASE_ADDR_H;
    bus_SS_MCI_BASE_ADDR_H_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_RECOVERY_IFC_BASE_ADDR_L -----------------------
  covergroup soc_ifc_SS_RECOVERY_IFC_BASE_ADDR_L_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_RECOVERY_IFC_BASE_ADDR_L_cp : coverpoint i_soc_ifc_reg.field_storage.SS_RECOVERY_IFC_BASE_ADDR_L;
    bus_SS_RECOVERY_IFC_BASE_ADDR_L_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_RECOVERY_IFC_BASE_ADDR_H -----------------------
  covergroup soc_ifc_SS_RECOVERY_IFC_BASE_ADDR_H_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_RECOVERY_IFC_BASE_ADDR_H_cp : coverpoint i_soc_ifc_reg.field_storage.SS_RECOVERY_IFC_BASE_ADDR_H;
    bus_SS_RECOVERY_IFC_BASE_ADDR_H_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_OTP_FC_BASE_ADDR_L -----------------------
  covergroup soc_ifc_SS_OTP_FC_BASE_ADDR_L_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_OTP_FC_BASE_ADDR_L_cp : coverpoint i_soc_ifc_reg.field_storage.SS_OTP_FC_BASE_ADDR_L;
    bus_SS_OTP_FC_BASE_ADDR_L_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_OTP_FC_BASE_ADDR_H -----------------------
  covergroup soc_ifc_SS_OTP_FC_BASE_ADDR_H_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_OTP_FC_BASE_ADDR_H_cp : coverpoint i_soc_ifc_reg.field_storage.SS_OTP_FC_BASE_ADDR_H;
    bus_SS_OTP_FC_BASE_ADDR_H_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_UDS_SEED_BASE_ADDR_L -----------------------
  covergroup soc_ifc_SS_UDS_SEED_BASE_ADDR_L_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_UDS_SEED_BASE_ADDR_L_cp : coverpoint i_soc_ifc_reg.field_storage.SS_UDS_SEED_BASE_ADDR_L;
    bus_SS_UDS_SEED_BASE_ADDR_L_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_UDS_SEED_BASE_ADDR_H -----------------------
  covergroup soc_ifc_SS_UDS_SEED_BASE_ADDR_H_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_UDS_SEED_BASE_ADDR_H_cp : coverpoint i_soc_ifc_reg.field_storage.SS_UDS_SEED_BASE_ADDR_H;
    bus_SS_UDS_SEED_BASE_ADDR_H_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET -----------------------
  covergroup soc_ifc_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET_cp : coverpoint i_soc_ifc_reg.field_storage.SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET;
    bus_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES -----------------------
  covergroup soc_ifc_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES_cp : coverpoint i_soc_ifc_reg.field_storage.SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES;
    bus_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_DEBUG_INTENT -----------------------
  covergroup soc_ifc_SS_DEBUG_INTENT_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_DEBUG_INTENT_cp : coverpoint i_soc_ifc_reg.field_storage.SS_DEBUG_INTENT;
    bus_SS_DEBUG_INTENT_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_CALIPTRA_DMA_AXI_USER -----------------------
  covergroup soc_ifc_SS_CALIPTRA_DMA_AXI_USER_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_CALIPTRA_DMA_AXI_USER_cp : coverpoint i_soc_ifc_reg.field_storage.SS_CALIPTRA_DMA_AXI_USER;
    bus_SS_CALIPTRA_DMA_AXI_USER_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L -----------------------
  covergroup soc_ifc_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L_cp : coverpoint i_soc_ifc_reg.field_storage.SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L;
    bus_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H -----------------------
  covergroup soc_ifc_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H_cp : coverpoint i_soc_ifc_reg.field_storage.SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H;
    bus_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_KEY_RELEASE_BASE_ADDR_L -----------------------
  covergroup soc_ifc_SS_KEY_RELEASE_BASE_ADDR_L_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_KEY_RELEASE_BASE_ADDR_L_cp : coverpoint i_soc_ifc_reg.field_storage.SS_KEY_RELEASE_BASE_ADDR_L;
    bus_SS_KEY_RELEASE_BASE_ADDR_L_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_KEY_RELEASE_BASE_ADDR_H -----------------------
  covergroup soc_ifc_SS_KEY_RELEASE_BASE_ADDR_H_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_KEY_RELEASE_BASE_ADDR_H_cp : coverpoint i_soc_ifc_reg.field_storage.SS_KEY_RELEASE_BASE_ADDR_H;
    bus_SS_KEY_RELEASE_BASE_ADDR_H_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_KEY_RELEASE_SIZE -----------------------
  covergroup soc_ifc_SS_KEY_RELEASE_SIZE_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_KEY_RELEASE_SIZE_cp : coverpoint i_soc_ifc_reg.field_storage.SS_KEY_RELEASE_SIZE;
    bus_SS_KEY_RELEASE_SIZE_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_OCP_LOCK_CTRL -----------------------
  covergroup soc_ifc_SS_OCP_LOCK_CTRL_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_OCP_LOCK_CTRL_cp : coverpoint i_soc_ifc_reg.field_storage.SS_OCP_LOCK_CTRL;
    bus_SS_OCP_LOCK_CTRL_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_STRAP_GENERIC [0:3] -----------------------
  covergroup soc_ifc_SS_STRAP_GENERIC_cg (ref logic [3:0] bus_event[0:3]) @(posedge clk);
    SS_STRAP_GENERIC0_cp : coverpoint i_soc_ifc_reg.field_storage.SS_STRAP_GENERIC[0];
    bus_SS_STRAP_GENERIC0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    SS_STRAP_GENERIC1_cp : coverpoint i_soc_ifc_reg.field_storage.SS_STRAP_GENERIC[1];
    bus_SS_STRAP_GENERIC1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    SS_STRAP_GENERIC2_cp : coverpoint i_soc_ifc_reg.field_storage.SS_STRAP_GENERIC[2];
    bus_SS_STRAP_GENERIC2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    SS_STRAP_GENERIC3_cp : coverpoint i_soc_ifc_reg.field_storage.SS_STRAP_GENERIC[3];
    bus_SS_STRAP_GENERIC3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_DBG_SERVICE_REG_REQ -----------------------
  covergroup soc_ifc_SS_DBG_SERVICE_REG_REQ_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_DBG_SERVICE_REG_REQ_cp : coverpoint i_soc_ifc_reg.field_storage.SS_DBG_SERVICE_REG_REQ;
    bus_SS_DBG_SERVICE_REG_REQ_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_DBG_SERVICE_REG_RSP -----------------------
  covergroup soc_ifc_SS_DBG_SERVICE_REG_RSP_cg (ref logic [3:0] bus_event) @(posedge clk);
    SS_DBG_SERVICE_REG_RSP_cp : coverpoint i_soc_ifc_reg.field_storage.SS_DBG_SERVICE_REG_RSP;
    bus_SS_DBG_SERVICE_REG_RSP_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_SOC_DBG_UNLOCK_LEVEL [0:1] -----------------------
  covergroup soc_ifc_SS_SOC_DBG_UNLOCK_LEVEL_cg (ref logic [3:0] bus_event[0:1]) @(posedge clk);
    SS_SOC_DBG_UNLOCK_LEVEL0_cp : coverpoint i_soc_ifc_reg.field_storage.SS_SOC_DBG_UNLOCK_LEVEL[0];
    bus_SS_SOC_DBG_UNLOCK_LEVEL0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    SS_SOC_DBG_UNLOCK_LEVEL1_cp : coverpoint i_soc_ifc_reg.field_storage.SS_SOC_DBG_UNLOCK_LEVEL[1];
    bus_SS_SOC_DBG_UNLOCK_LEVEL1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP SS_GENERIC_FW_EXEC_CTRL [0:3] -----------------------
  covergroup soc_ifc_SS_GENERIC_FW_EXEC_CTRL_cg (ref logic [3:0] bus_event[0:3]) @(posedge clk);
    SS_GENERIC_FW_EXEC_CTRL0_cp : coverpoint i_soc_ifc_reg.field_storage.SS_GENERIC_FW_EXEC_CTRL[0];
    bus_SS_GENERIC_FW_EXEC_CTRL0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    SS_GENERIC_FW_EXEC_CTRL1_cp : coverpoint i_soc_ifc_reg.field_storage.SS_GENERIC_FW_EXEC_CTRL[1];
    bus_SS_GENERIC_FW_EXEC_CTRL1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    SS_GENERIC_FW_EXEC_CTRL2_cp : coverpoint i_soc_ifc_reg.field_storage.SS_GENERIC_FW_EXEC_CTRL[2];
    bus_SS_GENERIC_FW_EXEC_CTRL2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    SS_GENERIC_FW_EXEC_CTRL3_cp : coverpoint i_soc_ifc_reg.field_storage.SS_GENERIC_FW_EXEC_CTRL[3];
    bus_SS_GENERIC_FW_EXEC_CTRL3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_obf_key [0:7] -----------------------
  covergroup soc_ifc_internal_obf_key_cg (ref logic [3:0] bus_event[0:7]) @(posedge clk);
    internal_obf_key0_cp : coverpoint i_soc_ifc_reg.field_storage.internal_obf_key[0];
    bus_internal_obf_key0_cp : coverpoint bus_event[0] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    internal_obf_key1_cp : coverpoint i_soc_ifc_reg.field_storage.internal_obf_key[1];
    bus_internal_obf_key1_cp : coverpoint bus_event[1] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    internal_obf_key2_cp : coverpoint i_soc_ifc_reg.field_storage.internal_obf_key[2];
    bus_internal_obf_key2_cp : coverpoint bus_event[2] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    internal_obf_key3_cp : coverpoint i_soc_ifc_reg.field_storage.internal_obf_key[3];
    bus_internal_obf_key3_cp : coverpoint bus_event[3] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    internal_obf_key4_cp : coverpoint i_soc_ifc_reg.field_storage.internal_obf_key[4];
    bus_internal_obf_key4_cp : coverpoint bus_event[4] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    internal_obf_key5_cp : coverpoint i_soc_ifc_reg.field_storage.internal_obf_key[5];
    bus_internal_obf_key5_cp : coverpoint bus_event[5] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    internal_obf_key6_cp : coverpoint i_soc_ifc_reg.field_storage.internal_obf_key[6];
    bus_internal_obf_key6_cp : coverpoint bus_event[6] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
    internal_obf_key7_cp : coverpoint i_soc_ifc_reg.field_storage.internal_obf_key[7];
    bus_internal_obf_key7_cp : coverpoint bus_event[7] {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_iccm_lock -----------------------
  covergroup soc_ifc_internal_iccm_lock_cg (ref logic [3:0] bus_event) @(posedge clk);
    internal_iccm_lock_cp : coverpoint i_soc_ifc_reg.field_storage.internal_iccm_lock;
    bus_internal_iccm_lock_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_fw_update_reset -----------------------
  covergroup soc_ifc_internal_fw_update_reset_cg (ref logic [3:0] bus_event) @(posedge clk);
    internal_fw_update_reset_cp : coverpoint i_soc_ifc_reg.field_storage.internal_fw_update_reset;
    bus_internal_fw_update_reset_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_fw_update_reset_wait_cycles -----------------------
  covergroup soc_ifc_internal_fw_update_reset_wait_cycles_cg (ref logic [3:0] bus_event) @(posedge clk);
    internal_fw_update_reset_wait_cycles_cp : coverpoint i_soc_ifc_reg.field_storage.internal_fw_update_reset_wait_cycles;
    bus_internal_fw_update_reset_wait_cycles_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_nmi_vector -----------------------
  covergroup soc_ifc_internal_nmi_vector_cg (ref logic [3:0] bus_event) @(posedge clk);
    internal_nmi_vector_cp : coverpoint i_soc_ifc_reg.field_storage.internal_nmi_vector;
    bus_internal_nmi_vector_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_hw_error_fatal_mask -----------------------
  covergroup soc_ifc_internal_hw_error_fatal_mask_cg (ref logic [3:0] bus_event) @(posedge clk);
    internal_hw_error_fatal_mask_cp : coverpoint i_soc_ifc_reg.field_storage.internal_hw_error_fatal_mask;
    bus_internal_hw_error_fatal_mask_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_hw_error_non_fatal_mask -----------------------
  covergroup soc_ifc_internal_hw_error_non_fatal_mask_cg (ref logic [3:0] bus_event) @(posedge clk);
    internal_hw_error_non_fatal_mask_cp : coverpoint i_soc_ifc_reg.field_storage.internal_hw_error_non_fatal_mask;
    bus_internal_hw_error_non_fatal_mask_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_fw_error_fatal_mask -----------------------
  covergroup soc_ifc_internal_fw_error_fatal_mask_cg (ref logic [3:0] bus_event) @(posedge clk);
    internal_fw_error_fatal_mask_cp : coverpoint i_soc_ifc_reg.field_storage.internal_fw_error_fatal_mask;
    bus_internal_fw_error_fatal_mask_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_fw_error_non_fatal_mask -----------------------
  covergroup soc_ifc_internal_fw_error_non_fatal_mask_cg (ref logic [3:0] bus_event) @(posedge clk);
    internal_fw_error_non_fatal_mask_cp : coverpoint i_soc_ifc_reg.field_storage.internal_fw_error_non_fatal_mask;
    bus_internal_fw_error_non_fatal_mask_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_rv_mtime_l -----------------------
  covergroup soc_ifc_internal_rv_mtime_l_cg (ref logic [3:0] bus_event) @(posedge clk);
    internal_rv_mtime_l_cp : coverpoint i_soc_ifc_reg.field_storage.internal_rv_mtime_l;
    bus_internal_rv_mtime_l_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_rv_mtime_h -----------------------
  covergroup soc_ifc_internal_rv_mtime_h_cg (ref logic [3:0] bus_event) @(posedge clk);
    internal_rv_mtime_h_cp : coverpoint i_soc_ifc_reg.field_storage.internal_rv_mtime_h;
    bus_internal_rv_mtime_h_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_rv_mtimecmp_l -----------------------
  covergroup soc_ifc_internal_rv_mtimecmp_l_cg (ref logic [3:0] bus_event) @(posedge clk);
    internal_rv_mtimecmp_l_cp : coverpoint i_soc_ifc_reg.field_storage.internal_rv_mtimecmp_l;
    bus_internal_rv_mtimecmp_l_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP internal_rv_mtimecmp_h -----------------------
  covergroup soc_ifc_internal_rv_mtimecmp_h_cg (ref logic [3:0] bus_event) @(posedge clk);
    internal_rv_mtimecmp_h_cp : coverpoint i_soc_ifc_reg.field_storage.internal_rv_mtimecmp_h;
    bus_internal_rv_mtimecmp_h_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_global_intr_en_r -----------------------
  covergroup soc_ifc_intr_brf_global_intr_en_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_global_intr_en_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.global_intr_en_r;
    bus_intr_brf_global_intr_en_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_intr_en_r -----------------------
  covergroup soc_ifc_intr_brf_error_intr_en_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_intr_en_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_en_r;
    bus_intr_brf_error_intr_en_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_intr_en_r -----------------------
  covergroup soc_ifc_intr_brf_notif_intr_en_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_intr_en_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_en_r;
    bus_intr_brf_notif_intr_en_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_global_intr_r -----------------------
  covergroup soc_ifc_intr_brf_error_global_intr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_global_intr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_global_intr_r;
    bus_intr_brf_error_global_intr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_global_intr_r -----------------------
  covergroup soc_ifc_intr_brf_notif_global_intr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_global_intr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_global_intr_r;
    bus_intr_brf_notif_global_intr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_internal_intr_r -----------------------
  covergroup soc_ifc_intr_brf_error_internal_intr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_internal_intr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_r;
    bus_intr_brf_error_internal_intr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_internal_intr_r -----------------------
  covergroup soc_ifc_intr_brf_notif_internal_intr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_internal_intr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_internal_intr_r;
    bus_intr_brf_notif_internal_intr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_intr_trig_r -----------------------
  covergroup soc_ifc_intr_brf_error_intr_trig_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_intr_trig_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_intr_trig_r;
    bus_intr_brf_error_intr_trig_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_intr_trig_r -----------------------
  covergroup soc_ifc_intr_brf_notif_intr_trig_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_intr_trig_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_intr_trig_r;
    bus_intr_brf_notif_intr_trig_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_internal_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_error_internal_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_internal_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_count_r;
    bus_intr_brf_error_internal_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_inv_dev_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_error_inv_dev_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_inv_dev_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_inv_dev_intr_count_r;
    bus_intr_brf_error_inv_dev_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_cmd_fail_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_error_cmd_fail_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_cmd_fail_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_cmd_fail_intr_count_r;
    bus_intr_brf_error_cmd_fail_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_bad_fuse_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_error_bad_fuse_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_bad_fuse_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_bad_fuse_intr_count_r;
    bus_intr_brf_error_bad_fuse_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_iccm_blocked_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_error_iccm_blocked_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_iccm_blocked_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_iccm_blocked_intr_count_r;
    bus_intr_brf_error_iccm_blocked_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_mbox_ecc_unc_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_error_mbox_ecc_unc_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_mbox_ecc_unc_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_mbox_ecc_unc_intr_count_r;
    bus_intr_brf_error_mbox_ecc_unc_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_wdt_timer1_timeout_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_error_wdt_timer1_timeout_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_wdt_timer1_timeout_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_wdt_timer1_timeout_intr_count_r;
    bus_intr_brf_error_wdt_timer1_timeout_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_wdt_timer2_timeout_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_error_wdt_timer2_timeout_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_wdt_timer2_timeout_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_wdt_timer2_timeout_intr_count_r;
    bus_intr_brf_error_wdt_timer2_timeout_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_cmd_avail_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_notif_cmd_avail_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_cmd_avail_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_cmd_avail_intr_count_r;
    bus_intr_brf_notif_cmd_avail_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_mbox_ecc_cor_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_notif_mbox_ecc_cor_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_mbox_ecc_cor_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_mbox_ecc_cor_intr_count_r;
    bus_intr_brf_notif_mbox_ecc_cor_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_debug_locked_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_notif_debug_locked_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_debug_locked_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_debug_locked_intr_count_r;
    bus_intr_brf_notif_debug_locked_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_scan_mode_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_notif_scan_mode_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_scan_mode_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_scan_mode_intr_count_r;
    bus_intr_brf_notif_scan_mode_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_soc_req_lock_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_notif_soc_req_lock_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_soc_req_lock_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_soc_req_lock_intr_count_r;
    bus_intr_brf_notif_soc_req_lock_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_gen_in_toggle_intr_count_r -----------------------
  covergroup soc_ifc_intr_brf_notif_gen_in_toggle_intr_count_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_gen_in_toggle_intr_count_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_gen_in_toggle_intr_count_r;
    bus_intr_brf_notif_gen_in_toggle_intr_count_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_internal_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_error_internal_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_internal_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_internal_intr_count_incr_r;
    bus_intr_brf_error_internal_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_inv_dev_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_error_inv_dev_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_inv_dev_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_inv_dev_intr_count_incr_r;
    bus_intr_brf_error_inv_dev_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_cmd_fail_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_error_cmd_fail_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_cmd_fail_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_cmd_fail_intr_count_incr_r;
    bus_intr_brf_error_cmd_fail_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_bad_fuse_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_error_bad_fuse_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_bad_fuse_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_bad_fuse_intr_count_incr_r;
    bus_intr_brf_error_bad_fuse_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_iccm_blocked_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_error_iccm_blocked_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_iccm_blocked_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_iccm_blocked_intr_count_incr_r;
    bus_intr_brf_error_iccm_blocked_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_mbox_ecc_unc_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_error_mbox_ecc_unc_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_mbox_ecc_unc_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_mbox_ecc_unc_intr_count_incr_r;
    bus_intr_brf_error_mbox_ecc_unc_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_wdt_timer1_timeout_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_error_wdt_timer1_timeout_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_wdt_timer1_timeout_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_wdt_timer1_timeout_intr_count_incr_r;
    bus_intr_brf_error_wdt_timer1_timeout_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_error_wdt_timer2_timeout_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_error_wdt_timer2_timeout_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_error_wdt_timer2_timeout_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.error_wdt_timer2_timeout_intr_count_incr_r;
    bus_intr_brf_error_wdt_timer2_timeout_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_cmd_avail_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_notif_cmd_avail_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_cmd_avail_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_cmd_avail_intr_count_incr_r;
    bus_intr_brf_notif_cmd_avail_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_mbox_ecc_cor_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_notif_mbox_ecc_cor_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_mbox_ecc_cor_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_mbox_ecc_cor_intr_count_incr_r;
    bus_intr_brf_notif_mbox_ecc_cor_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_debug_locked_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_notif_debug_locked_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_debug_locked_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_debug_locked_intr_count_incr_r;
    bus_intr_brf_notif_debug_locked_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_scan_mode_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_notif_scan_mode_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_scan_mode_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_scan_mode_intr_count_incr_r;
    bus_intr_brf_notif_scan_mode_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_soc_req_lock_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_notif_soc_req_lock_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_soc_req_lock_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_soc_req_lock_intr_count_incr_r;
    bus_intr_brf_notif_soc_req_lock_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup

  // ----------------------- COVERGROUP intr_brf_notif_gen_in_toggle_intr_count_incr_r -----------------------
  covergroup soc_ifc_intr_brf_notif_gen_in_toggle_intr_count_incr_r_cg (ref logic [3:0] bus_event) @(posedge clk);
    intr_brf_notif_gen_in_toggle_intr_count_incr_r_cp : coverpoint i_soc_ifc_reg.field_storage.intr_block_rf.notif_gen_in_toggle_intr_count_incr_r;
    bus_intr_brf_notif_gen_in_toggle_intr_count_incr_r_cp : coverpoint bus_event {
      bins wr_rd[] = (AHB_WR, AXI_WR => IDLE [*1:1000] => AHB_RD, AXI_RD);
      ignore_bins dont_care = {IDLE, 4'hf, (AXI_RD | AXI_WR), (AHB_RD | AHB_WR)};
    }
  endgroup


  // ----------------------- COVERGROUP Instantiations -----------------------

  soc_ifc_CPTRA_HW_ERROR_FATAL_cg CPTRA_HW_ERROR_FATAL_cg = new(bus_CPTRA_HW_ERROR_FATAL);
  soc_ifc_CPTRA_HW_ERROR_NON_FATAL_cg CPTRA_HW_ERROR_NON_FATAL_cg = new(bus_CPTRA_HW_ERROR_NON_FATAL);
  soc_ifc_CPTRA_FW_ERROR_FATAL_cg CPTRA_FW_ERROR_FATAL_cg = new(bus_CPTRA_FW_ERROR_FATAL);
  soc_ifc_CPTRA_FW_ERROR_NON_FATAL_cg CPTRA_FW_ERROR_NON_FATAL_cg = new(bus_CPTRA_FW_ERROR_NON_FATAL);
  soc_ifc_CPTRA_HW_ERROR_ENC_cg CPTRA_HW_ERROR_ENC_cg = new(bus_CPTRA_HW_ERROR_ENC);
  soc_ifc_CPTRA_FW_ERROR_ENC_cg CPTRA_FW_ERROR_ENC_cg = new(bus_CPTRA_FW_ERROR_ENC);
  soc_ifc_CPTRA_FW_EXTENDED_ERROR_INFO_cg CPTRA_FW_EXTENDED_ERROR_INFO_cg = new(bus_CPTRA_FW_EXTENDED_ERROR_INFO);
  soc_ifc_CPTRA_BOOT_STATUS_cg CPTRA_BOOT_STATUS_cg = new(bus_CPTRA_BOOT_STATUS);
  soc_ifc_CPTRA_FLOW_STATUS_cg CPTRA_FLOW_STATUS_cg = new(bus_CPTRA_FLOW_STATUS);
  soc_ifc_CPTRA_RESET_REASON_cg CPTRA_RESET_REASON_cg = new(bus_CPTRA_RESET_REASON);
  // soc_ifc_CPTRA_SECURITY_STATE_cg CPTRA_SECURITY_STATE_cg = new(bus_CPTRA_SECURITY_STATE);
  soc_ifc_CPTRA_MBOX_VALID_AXI_USER_cg CPTRA_MBOX_VALID_AXI_USER_cg = new(bus_CPTRA_MBOX_VALID_AXI_USER);
  soc_ifc_CPTRA_MBOX_AXI_USER_LOCK_cg CPTRA_MBOX_AXI_USER_LOCK_cg = new(bus_CPTRA_MBOX_AXI_USER_LOCK);
  soc_ifc_CPTRA_TRNG_VALID_AXI_USER_cg CPTRA_TRNG_VALID_AXI_USER_cg = new(bus_CPTRA_TRNG_VALID_AXI_USER);
  soc_ifc_CPTRA_TRNG_AXI_USER_LOCK_cg CPTRA_TRNG_AXI_USER_LOCK_cg = new(bus_CPTRA_TRNG_AXI_USER_LOCK);
  soc_ifc_CPTRA_TRNG_DATA_cg CPTRA_TRNG_DATA_cg = new(bus_CPTRA_TRNG_DATA);
  soc_ifc_CPTRA_TRNG_CTRL_cg CPTRA_TRNG_CTRL_cg = new(bus_CPTRA_TRNG_CTRL);
  soc_ifc_CPTRA_TRNG_STATUS_cg CPTRA_TRNG_STATUS_cg = new(bus_CPTRA_TRNG_STATUS);
  soc_ifc_CPTRA_FUSE_WR_DONE_cg CPTRA_FUSE_WR_DONE_cg = new(bus_CPTRA_FUSE_WR_DONE);
  soc_ifc_CPTRA_TIMER_CONFIG_cg CPTRA_TIMER_CONFIG_cg = new(bus_CPTRA_TIMER_CONFIG);
  soc_ifc_CPTRA_BOOTFSM_GO_cg CPTRA_BOOTFSM_GO_cg = new(bus_CPTRA_BOOTFSM_GO);
  soc_ifc_CPTRA_DBG_MANUF_SERVICE_REG_cg CPTRA_DBG_MANUF_SERVICE_REG_cg = new(bus_CPTRA_DBG_MANUF_SERVICE_REG);
  soc_ifc_CPTRA_CLK_GATING_EN_cg CPTRA_CLK_GATING_EN_cg = new(bus_CPTRA_CLK_GATING_EN);
  soc_ifc_CPTRA_GENERIC_INPUT_WIRES_cg CPTRA_GENERIC_INPUT_WIRES_cg = new(bus_CPTRA_GENERIC_INPUT_WIRES);
  soc_ifc_CPTRA_GENERIC_OUTPUT_WIRES_cg CPTRA_GENERIC_OUTPUT_WIRES_cg = new(bus_CPTRA_GENERIC_OUTPUT_WIRES);
  // soc_ifc_CPTRA_HW_REV_ID_cg CPTRA_HW_REV_ID_cg = new(bus_CPTRA_HW_REV_ID);
  soc_ifc_CPTRA_FW_REV_ID_cg CPTRA_FW_REV_ID_cg = new(bus_CPTRA_FW_REV_ID);
  // soc_ifc_CPTRA_HW_CONFIG_cg CPTRA_HW_CONFIG_cg = new(bus_CPTRA_HW_CONFIG);
  soc_ifc_CPTRA_WDT_TIMER1_EN_cg CPTRA_WDT_TIMER1_EN_cg = new(bus_CPTRA_WDT_TIMER1_EN);
  soc_ifc_CPTRA_WDT_TIMER1_CTRL_cg CPTRA_WDT_TIMER1_CTRL_cg = new(bus_CPTRA_WDT_TIMER1_CTRL);
  soc_ifc_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_cg CPTRA_WDT_TIMER1_TIMEOUT_PERIOD_cg = new(bus_CPTRA_WDT_TIMER1_TIMEOUT_PERIOD);
  soc_ifc_CPTRA_WDT_TIMER2_EN_cg CPTRA_WDT_TIMER2_EN_cg = new(bus_CPTRA_WDT_TIMER2_EN);
  soc_ifc_CPTRA_WDT_TIMER2_CTRL_cg CPTRA_WDT_TIMER2_CTRL_cg = new(bus_CPTRA_WDT_TIMER2_CTRL);
  soc_ifc_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_cg CPTRA_WDT_TIMER2_TIMEOUT_PERIOD_cg = new(bus_CPTRA_WDT_TIMER2_TIMEOUT_PERIOD);
  soc_ifc_CPTRA_WDT_STATUS_cg CPTRA_WDT_STATUS_cg = new(bus_CPTRA_WDT_STATUS);
  soc_ifc_CPTRA_FUSE_VALID_AXI_USER_cg CPTRA_FUSE_VALID_AXI_USER_cg = new(bus_CPTRA_FUSE_VALID_AXI_USER);
  soc_ifc_CPTRA_FUSE_AXI_USER_LOCK_cg CPTRA_FUSE_AXI_USER_LOCK_cg = new(bus_CPTRA_FUSE_AXI_USER_LOCK);
  soc_ifc_CPTRA_WDT_CFG_cg CPTRA_WDT_CFG_cg = new(bus_CPTRA_WDT_CFG);
  soc_ifc_CPTRA_iTRNG_ENTROPY_CONFIG_0_cg CPTRA_iTRNG_ENTROPY_CONFIG_0_cg = new(bus_CPTRA_iTRNG_ENTROPY_CONFIG_0);
  soc_ifc_CPTRA_iTRNG_ENTROPY_CONFIG_1_cg CPTRA_iTRNG_ENTROPY_CONFIG_1_cg = new(bus_CPTRA_iTRNG_ENTROPY_CONFIG_1);
  soc_ifc_CPTRA_RSVD_REG_cg CPTRA_RSVD_REG_cg = new(bus_CPTRA_RSVD_REG);
  soc_ifc_CPTRA_HW_CAPABILITIES_cg CPTRA_HW_CAPABILITIES_cg = new(bus_CPTRA_HW_CAPABILITIES);
  soc_ifc_CPTRA_FW_CAPABILITIES_cg CPTRA_FW_CAPABILITIES_cg = new(bus_CPTRA_FW_CAPABILITIES);
  soc_ifc_CPTRA_CAP_LOCK_cg CPTRA_CAP_LOCK_cg = new(bus_CPTRA_CAP_LOCK);
  soc_ifc_CPTRA_OWNER_PK_HASH_cg CPTRA_OWNER_PK_HASH_cg = new(bus_CPTRA_OWNER_PK_HASH);
  soc_ifc_CPTRA_OWNER_PK_HASH_LOCK_cg CPTRA_OWNER_PK_HASH_LOCK_cg = new(bus_CPTRA_OWNER_PK_HASH_LOCK);
  soc_ifc_fuse_uds_seed_cg fuse_uds_seed_cg = new(bus_fuse_uds_seed);
  soc_ifc_fuse_field_entropy_cg fuse_field_entropy_cg = new(bus_fuse_field_entropy);
  soc_ifc_fuse_vendor_pk_hash_cg fuse_vendor_pk_hash_cg = new(bus_fuse_vendor_pk_hash);
  soc_ifc_fuse_ecc_revocation_cg fuse_ecc_revocation_cg = new(bus_fuse_ecc_revocation);
  soc_ifc_fuse_fmc_key_manifest_svn_cg fuse_fmc_key_manifest_svn_cg = new(bus_fuse_fmc_key_manifest_svn);
  soc_ifc_fuse_runtime_svn_cg fuse_runtime_svn_cg = new(bus_fuse_runtime_svn);
  soc_ifc_fuse_anti_rollback_disable_cg fuse_anti_rollback_disable_cg = new(bus_fuse_anti_rollback_disable);
  soc_ifc_fuse_idevid_cert_attr_cg fuse_idevid_cert_attr_cg = new(bus_fuse_idevid_cert_attr);
  soc_ifc_fuse_idevid_manuf_hsm_id_cg fuse_idevid_manuf_hsm_id_cg = new(bus_fuse_idevid_manuf_hsm_id);
  soc_ifc_fuse_lms_revocation_cg fuse_lms_revocation_cg = new(bus_fuse_lms_revocation);
  soc_ifc_fuse_mldsa_revocation_cg fuse_mldsa_revocation_cg = new(bus_fuse_mldsa_revocation);
  soc_ifc_fuse_soc_stepping_id_cg fuse_soc_stepping_id_cg = new(bus_fuse_soc_stepping_id);
  soc_ifc_fuse_manuf_dbg_unlock_token_cg fuse_manuf_dbg_unlock_token_cg = new(bus_fuse_manuf_dbg_unlock_token);
  soc_ifc_fuse_pqc_key_type_cg fuse_pqc_key_type_cg = new(bus_fuse_pqc_key_type);
  soc_ifc_fuse_soc_manifest_svn_cg fuse_soc_manifest_svn_cg = new(bus_fuse_soc_manifest_svn);
  soc_ifc_fuse_soc_manifest_max_svn_cg fuse_soc_manifest_max_svn_cg = new(bus_fuse_soc_manifest_max_svn);
  soc_ifc_fuse_hek_seed_cg fuse_hek_seed_cg = new(bus_fuse_hek_seed);
  soc_ifc_SS_CALIPTRA_BASE_ADDR_L_cg SS_CALIPTRA_BASE_ADDR_L_cg = new(bus_SS_CALIPTRA_BASE_ADDR_L);
  soc_ifc_SS_CALIPTRA_BASE_ADDR_H_cg SS_CALIPTRA_BASE_ADDR_H_cg = new(bus_SS_CALIPTRA_BASE_ADDR_H);
  soc_ifc_SS_MCI_BASE_ADDR_L_cg SS_MCI_BASE_ADDR_L_cg = new(bus_SS_MCI_BASE_ADDR_L);
  soc_ifc_SS_MCI_BASE_ADDR_H_cg SS_MCI_BASE_ADDR_H_cg = new(bus_SS_MCI_BASE_ADDR_H);
  soc_ifc_SS_RECOVERY_IFC_BASE_ADDR_L_cg SS_RECOVERY_IFC_BASE_ADDR_L_cg = new(bus_SS_RECOVERY_IFC_BASE_ADDR_L);
  soc_ifc_SS_RECOVERY_IFC_BASE_ADDR_H_cg SS_RECOVERY_IFC_BASE_ADDR_H_cg = new(bus_SS_RECOVERY_IFC_BASE_ADDR_H);
  soc_ifc_SS_OTP_FC_BASE_ADDR_L_cg SS_OTP_FC_BASE_ADDR_L_cg = new(bus_SS_OTP_FC_BASE_ADDR_L);
  soc_ifc_SS_OTP_FC_BASE_ADDR_H_cg SS_OTP_FC_BASE_ADDR_H_cg = new(bus_SS_OTP_FC_BASE_ADDR_H);
  soc_ifc_SS_UDS_SEED_BASE_ADDR_L_cg SS_UDS_SEED_BASE_ADDR_L_cg = new(bus_SS_UDS_SEED_BASE_ADDR_L);
  soc_ifc_SS_UDS_SEED_BASE_ADDR_H_cg SS_UDS_SEED_BASE_ADDR_H_cg = new(bus_SS_UDS_SEED_BASE_ADDR_H);
  soc_ifc_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET_cg SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET_cg = new(bus_SS_PROD_DEBUG_UNLOCK_AUTH_PK_HASH_REG_BANK_OFFSET);
  soc_ifc_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES_cg SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES_cg = new(bus_SS_NUM_OF_PROD_DEBUG_UNLOCK_AUTH_PK_HASHES);
  soc_ifc_SS_DEBUG_INTENT_cg SS_DEBUG_INTENT_cg = new(bus_SS_DEBUG_INTENT);
  soc_ifc_SS_CALIPTRA_DMA_AXI_USER_cg SS_CALIPTRA_DMA_AXI_USER_cg = new(bus_SS_CALIPTRA_DMA_AXI_USER);
  soc_ifc_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L_cg SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L_cg = new(bus_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_L);
  soc_ifc_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H_cg SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H_cg = new(bus_SS_EXTERNAL_STAGING_AREA_BASE_ADDR_H);
  soc_ifc_SS_KEY_RELEASE_BASE_ADDR_L_cg SS_KEY_RELEASE_BASE_ADDR_L_cg = new(bus_SS_KEY_RELEASE_BASE_ADDR_L);
  soc_ifc_SS_KEY_RELEASE_BASE_ADDR_H_cg SS_KEY_RELEASE_BASE_ADDR_H_cg = new(bus_SS_KEY_RELEASE_BASE_ADDR_H);
  soc_ifc_SS_KEY_RELEASE_SIZE_cg SS_KEY_RELEASE_SIZE_cg = new(bus_SS_KEY_RELEASE_SIZE);
  soc_ifc_SS_OCP_LOCK_CTRL_cg SS_OCP_LOCK_CTRL_cg = new(bus_SS_OCP_LOCK_CTRL);
  soc_ifc_SS_STRAP_GENERIC_cg SS_STRAP_GENERIC_cg = new(bus_SS_STRAP_GENERIC);
  soc_ifc_SS_DBG_SERVICE_REG_REQ_cg SS_DBG_SERVICE_REG_REQ_cg = new(bus_SS_DBG_SERVICE_REG_REQ);
  soc_ifc_SS_DBG_SERVICE_REG_RSP_cg SS_DBG_SERVICE_REG_RSP_cg = new(bus_SS_DBG_SERVICE_REG_RSP);
  soc_ifc_SS_SOC_DBG_UNLOCK_LEVEL_cg SS_SOC_DBG_UNLOCK_LEVEL_cg = new(bus_SS_SOC_DBG_UNLOCK_LEVEL);
  soc_ifc_SS_GENERIC_FW_EXEC_CTRL_cg SS_GENERIC_FW_EXEC_CTRL_cg = new(bus_SS_GENERIC_FW_EXEC_CTRL);
  soc_ifc_internal_obf_key_cg internal_obf_key_cg = new(bus_internal_obf_key);
  soc_ifc_internal_iccm_lock_cg internal_iccm_lock_cg = new(bus_internal_iccm_lock);
  soc_ifc_internal_fw_update_reset_cg internal_fw_update_reset_cg = new(bus_internal_fw_update_reset);
  soc_ifc_internal_fw_update_reset_wait_cycles_cg internal_fw_update_reset_wait_cycles_cg = new(bus_internal_fw_update_reset_wait_cycles);
  soc_ifc_internal_nmi_vector_cg internal_nmi_vector_cg = new(bus_internal_nmi_vector);
  soc_ifc_internal_hw_error_fatal_mask_cg internal_hw_error_fatal_mask_cg = new(bus_internal_hw_error_fatal_mask);
  soc_ifc_internal_hw_error_non_fatal_mask_cg internal_hw_error_non_fatal_mask_cg = new(bus_internal_hw_error_non_fatal_mask);
  soc_ifc_internal_fw_error_fatal_mask_cg internal_fw_error_fatal_mask_cg = new(bus_internal_fw_error_fatal_mask);
  soc_ifc_internal_fw_error_non_fatal_mask_cg internal_fw_error_non_fatal_mask_cg = new(bus_internal_fw_error_non_fatal_mask);
  soc_ifc_internal_rv_mtime_l_cg internal_rv_mtime_l_cg = new(bus_internal_rv_mtime_l);
  soc_ifc_internal_rv_mtime_h_cg internal_rv_mtime_h_cg = new(bus_internal_rv_mtime_h);
  soc_ifc_internal_rv_mtimecmp_l_cg internal_rv_mtimecmp_l_cg = new(bus_internal_rv_mtimecmp_l);
  soc_ifc_internal_rv_mtimecmp_h_cg internal_rv_mtimecmp_h_cg = new(bus_internal_rv_mtimecmp_h);
  soc_ifc_intr_brf_global_intr_en_r_cg intr_brf_global_intr_en_r_cg = new(bus_intr_brf_global_intr_en_r);
  soc_ifc_intr_brf_error_intr_en_r_cg intr_brf_error_intr_en_r_cg = new(bus_intr_brf_error_intr_en_r);
  soc_ifc_intr_brf_notif_intr_en_r_cg intr_brf_notif_intr_en_r_cg = new(bus_intr_brf_notif_intr_en_r);
  soc_ifc_intr_brf_error_global_intr_r_cg intr_brf_error_global_intr_r_cg = new(bus_intr_brf_error_global_intr_r);
  soc_ifc_intr_brf_notif_global_intr_r_cg intr_brf_notif_global_intr_r_cg = new(bus_intr_brf_notif_global_intr_r);
  soc_ifc_intr_brf_error_internal_intr_r_cg intr_brf_error_internal_intr_r_cg = new(bus_intr_brf_error_internal_intr_r);
  soc_ifc_intr_brf_notif_internal_intr_r_cg intr_brf_notif_internal_intr_r_cg = new(bus_intr_brf_notif_internal_intr_r);
  soc_ifc_intr_brf_error_intr_trig_r_cg intr_brf_error_intr_trig_r_cg = new(bus_intr_brf_error_intr_trig_r);
  soc_ifc_intr_brf_notif_intr_trig_r_cg intr_brf_notif_intr_trig_r_cg = new(bus_intr_brf_notif_intr_trig_r);
  soc_ifc_intr_brf_error_internal_intr_count_r_cg intr_brf_error_internal_intr_count_r_cg = new(bus_intr_brf_error_internal_intr_count_r);
  soc_ifc_intr_brf_error_inv_dev_intr_count_r_cg intr_brf_error_inv_dev_intr_count_r_cg = new(bus_intr_brf_error_inv_dev_intr_count_r);
  soc_ifc_intr_brf_error_cmd_fail_intr_count_r_cg intr_brf_error_cmd_fail_intr_count_r_cg = new(bus_intr_brf_error_cmd_fail_intr_count_r);
  soc_ifc_intr_brf_error_bad_fuse_intr_count_r_cg intr_brf_error_bad_fuse_intr_count_r_cg = new(bus_intr_brf_error_bad_fuse_intr_count_r);
  soc_ifc_intr_brf_error_iccm_blocked_intr_count_r_cg intr_brf_error_iccm_blocked_intr_count_r_cg = new(bus_intr_brf_error_iccm_blocked_intr_count_r);
  soc_ifc_intr_brf_error_mbox_ecc_unc_intr_count_r_cg intr_brf_error_mbox_ecc_unc_intr_count_r_cg = new(bus_intr_brf_error_mbox_ecc_unc_intr_count_r);
  soc_ifc_intr_brf_error_wdt_timer1_timeout_intr_count_r_cg intr_brf_error_wdt_timer1_timeout_intr_count_r_cg = new(bus_intr_brf_error_wdt_timer1_timeout_intr_count_r);
  soc_ifc_intr_brf_error_wdt_timer2_timeout_intr_count_r_cg intr_brf_error_wdt_timer2_timeout_intr_count_r_cg = new(bus_intr_brf_error_wdt_timer2_timeout_intr_count_r);
  soc_ifc_intr_brf_notif_cmd_avail_intr_count_r_cg intr_brf_notif_cmd_avail_intr_count_r_cg = new(bus_intr_brf_notif_cmd_avail_intr_count_r);
  soc_ifc_intr_brf_notif_mbox_ecc_cor_intr_count_r_cg intr_brf_notif_mbox_ecc_cor_intr_count_r_cg = new(bus_intr_brf_notif_mbox_ecc_cor_intr_count_r);
  soc_ifc_intr_brf_notif_debug_locked_intr_count_r_cg intr_brf_notif_debug_locked_intr_count_r_cg = new(bus_intr_brf_notif_debug_locked_intr_count_r);
  soc_ifc_intr_brf_notif_scan_mode_intr_count_r_cg intr_brf_notif_scan_mode_intr_count_r_cg = new(bus_intr_brf_notif_scan_mode_intr_count_r);
  soc_ifc_intr_brf_notif_soc_req_lock_intr_count_r_cg intr_brf_notif_soc_req_lock_intr_count_r_cg = new(bus_intr_brf_notif_soc_req_lock_intr_count_r);
  soc_ifc_intr_brf_notif_gen_in_toggle_intr_count_r_cg intr_brf_notif_gen_in_toggle_intr_count_r_cg = new(bus_intr_brf_notif_gen_in_toggle_intr_count_r);
  soc_ifc_intr_brf_error_internal_intr_count_incr_r_cg intr_brf_error_internal_intr_count_incr_r_cg = new(bus_intr_brf_error_internal_intr_count_incr_r);
  soc_ifc_intr_brf_error_inv_dev_intr_count_incr_r_cg intr_brf_error_inv_dev_intr_count_incr_r_cg = new(bus_intr_brf_error_inv_dev_intr_count_incr_r);
  soc_ifc_intr_brf_error_cmd_fail_intr_count_incr_r_cg intr_brf_error_cmd_fail_intr_count_incr_r_cg = new(bus_intr_brf_error_cmd_fail_intr_count_incr_r);
  soc_ifc_intr_brf_error_bad_fuse_intr_count_incr_r_cg intr_brf_error_bad_fuse_intr_count_incr_r_cg = new(bus_intr_brf_error_bad_fuse_intr_count_incr_r);
  soc_ifc_intr_brf_error_iccm_blocked_intr_count_incr_r_cg intr_brf_error_iccm_blocked_intr_count_incr_r_cg = new(bus_intr_brf_error_iccm_blocked_intr_count_incr_r);
  soc_ifc_intr_brf_error_mbox_ecc_unc_intr_count_incr_r_cg intr_brf_error_mbox_ecc_unc_intr_count_incr_r_cg = new(bus_intr_brf_error_mbox_ecc_unc_intr_count_incr_r);
  soc_ifc_intr_brf_error_wdt_timer1_timeout_intr_count_incr_r_cg intr_brf_error_wdt_timer1_timeout_intr_count_incr_r_cg = new(bus_intr_brf_error_wdt_timer1_timeout_intr_count_incr_r);
  soc_ifc_intr_brf_error_wdt_timer2_timeout_intr_count_incr_r_cg intr_brf_error_wdt_timer2_timeout_intr_count_incr_r_cg = new(bus_intr_brf_error_wdt_timer2_timeout_intr_count_incr_r);
  soc_ifc_intr_brf_notif_cmd_avail_intr_count_incr_r_cg intr_brf_notif_cmd_avail_intr_count_incr_r_cg = new(bus_intr_brf_notif_cmd_avail_intr_count_incr_r);
  soc_ifc_intr_brf_notif_mbox_ecc_cor_intr_count_incr_r_cg intr_brf_notif_mbox_ecc_cor_intr_count_incr_r_cg = new(bus_intr_brf_notif_mbox_ecc_cor_intr_count_incr_r);
  soc_ifc_intr_brf_notif_debug_locked_intr_count_incr_r_cg intr_brf_notif_debug_locked_intr_count_incr_r_cg = new(bus_intr_brf_notif_debug_locked_intr_count_incr_r);
  soc_ifc_intr_brf_notif_scan_mode_intr_count_incr_r_cg intr_brf_notif_scan_mode_intr_count_incr_r_cg = new(bus_intr_brf_notif_scan_mode_intr_count_incr_r);
  soc_ifc_intr_brf_notif_soc_req_lock_intr_count_incr_r_cg intr_brf_notif_soc_req_lock_intr_count_incr_r_cg = new(bus_intr_brf_notif_soc_req_lock_intr_count_incr_r);
  soc_ifc_intr_brf_notif_gen_in_toggle_intr_count_incr_r_cg intr_brf_notif_gen_in_toggle_intr_count_incr_r_cg = new(bus_intr_brf_notif_gen_in_toggle_intr_count_incr_r);

  // ------------------------------------------------------------------- 
  // end SCRIPT_OUTPUT
  // ------------------------------------------------------------------- 

endinterface


`endif

