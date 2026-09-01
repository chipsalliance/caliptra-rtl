// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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
//


`include "caliptra_macros.svh"
`include "config_defines.svh"
//`include "kv_defines_pkg.sv"
//`include "doe_defines_pkg.sv"
`ifndef CPTRA_TB_TOP_NAME
  `define CPTRA_TB_TOP_NAME `CALIPTRA_TOP
`endif
`ifndef CPTRA_TOP_PATH
  `define CPTRA_TOP_PATH      `CPTRA_TB_TOP_NAME.caliptra_top_dut
`endif
`define KEYVAULT_PATH       `CPTRA_TOP_PATH.key_vault1
`define KEYVAULT_REG_PATH   `KEYVAULT_PATH.kv_reg1
`define PCRVAULT_PATH       `CPTRA_TOP_PATH.pcr_vault1
`define PCRVAULT_REG_PATH   `PCRVAULT_PATH.pv_reg1
`define DATA_VAULT_PATH     `CPTRA_TOP_PATH.data_vault1
`define DATA_VAULT_REG_PATH `DATA_VAULT_PATH.dv_reg1
`define DOE_INST_PATH       `CPTRA_TOP_PATH.doe.doe_inst
`define DOE_PATH            `DOE_INST_PATH.doe_fsm1
`define DOE_REG_PATH        `DOE_INST_PATH.i_doe_reg
`define SERVICES_PATH       `CPTRA_TB_TOP_NAME.tb_services_i
`define SHA512_PATH         `CPTRA_TOP_PATH.sha512.sha512_inst
`define ABR_PATH            `CPTRA_TOP_PATH.abr_inst.abr_ctrl_inst
`define ABR_REG_PATH        `CPTRA_TOP_PATH.abr_inst.abr_reg_inst
`define HMAC_PATH           `CPTRA_TOP_PATH.hmac.hmac_inst
`define HMAC_REG_PATH       `HMAC_PATH.i_hmac_reg
`define ECC_PATH            `CPTRA_TOP_PATH.ecc_top1.ecc_dsa_ctrl_i
`define ECC_REG_PATH        `CPTRA_TOP_PATH.ecc_top1.ecc_reg1
`define HMAC_DRBG_PATH      `CPTRA_TOP_PATH.ecc_top1.ecc_dsa_ctrl_i.ecc_hmac_drbg_interface_i.hmac_drbg_i
`define SHA256_PATH         `CPTRA_TOP_PATH.sha256.sha256_inst
`define SHA512_MASKED_PATH  `CPTRA_TOP_PATH.ecc_top1.ecc_dsa_ctrl_i.ecc_hmac_drbg_interface_i.hmac_drbg_i.HMAC_K.u_sha512_core_h1
`define SOC_IFC_TOP_PATH    `CPTRA_TOP_PATH.soc_ifc_top1
`define MBOX_PATH           `SOC_IFC_TOP_PATH.i_mbox
`define AXI_DMA_CTRL_PATH   `SOC_IFC_TOP_PATH.i_axi_dma.i_axi_dma_ctrl
`define WDT_PATH            `SOC_IFC_TOP_PATH.i_wdt
`define ABR_RAMS_PATH       `SERVICES_PATH.abr_mem_top_inst
`define ABR_TOP_PATH        `CPTRA_TOP_PATH.abr_inst
// the name 'aes_inst' is used for the top 2 layers of AES core hierarchy :/
`define AES_CLP_PATH        `CPTRA_TOP_PATH.aes_inst
`define AES_PATH            `AES_CLP_PATH.aes_inst

`define SVA_RDC_CLK `CPTRA_TOP_PATH.rdc_clk_cg
`define CPTRA_FW_UPD_RST_WINDOW `SOC_IFC_TOP_PATH.i_soc_ifc_boot_fsm.fw_update_rst_window
`ifdef UVMF_CALIPTRA_TOP
  `define SVA_CLK `CPTRA_TB_TOP_NAME.clk
  `define SVA_RST `CPTRA_TB_TOP_NAME.soc_ifc_subenv_soc_ifc_ctrl_agent_bus.cptra_rst_b
`else
  `define SVA_CLK `CPTRA_TB_TOP_NAME.core_clk
  `define SVA_RST `CPTRA_TB_TOP_NAME.cptra_rst_b
`endif
`define MLDSA_ZEROIZATION   `CPTRA_TOP_PATH.abr_inst.abr_ctrl_inst.abr_reg_hwif_out.MLDSA_CTRL.ZEROIZE.value
`define MLKEM_ZEROIZATION   `CPTRA_TOP_PATH.abr_inst.abr_ctrl_inst.abr_reg_hwif_out.MLKEM_CTRL.ZEROIZE.value
`define ABR_SCAN_DEBUG    `CPTRA_TOP_PATH.abr_inst.debugUnlock_or_scan_mode_switch

module caliptra_top_sva
  import doe_defines_pkg::*;
  import kv_defines_pkg::*;
  import axi_dma_reg_pkg::*;
  import keymgr_pkg::*;
  import caliptra_prim_mubi_pkg::*;
  ();

  //TODO: pass these parameters from their architecture into here
  localparam SHA512_DIG_NUM_DWORDS    = 16;   //`SHA512_PATH.DIG_NUM_DWORDS;
  localparam SHA512_BLOCK_NUM_DWORDS  = 32;   //`SHA512_PATH.BLOCK_NUM_DWORDS;
  localparam MLDSA_SEED_NUM_DWORDS    = 8;   //`ABR_PATH.SEED_NUM_DWORDS;
  localparam MLKEM_SHAREDKEY_NUM_DWORDS = 8; 
  localparam HMAC_KEY_NUM_DWORDS      = 12;   //`HMAC_PATH.KEY_NUM_DWORDS
  localparam HMAC_TAG_NUM_DWORDS      = 12;   //`HMAC_PATH.TAG_NUM_DWORDS
  localparam HMAC_BLOCK_NUM_DWORDS    = 32;   //`HMAC_PATH.BLOCK_NUM_DWORDS
  localparam ECC_REG_NUM_DWORDS       = 12;   //'ECC_PATH.REG_NUM_DWORDS
  localparam ECC_MEM_ADDR             = 2**6; //'ECC_PATH.ecc_arith_unit_i.ram_tdp_file_i.mem.ADDR_LENGTH
  localparam SHA256_DIG_NUM_DWORDS    = 8;    //`SHA256_PATH.DIG_NUM_DWORDS;
  localparam SHA256_BLOCK_NUM_DWORDS  = 16;   //`SHA256_PATH.BLOCK_NUM_DWORDS;
  localparam DOE_256_NUM_ROUNDS       = 14;   //`DOE_INST_PATH.i_doe_core_cbc.keymem.DOE_256_NUM_ROUNDS

  // Local boolean signals for debug_locked (validation collateral — reduce MuBi4 once here)
  logic debug_unlocked_latched = mubi4_test_false_strict(`CPTRA_TOP_PATH.cptra_security_state_Latched.debug_locked);
  logic debug_unlocked_input   = mubi4_test_false_strict(`CPTRA_TOP_PATH.security_state.debug_locked);
  localparam SEED_NUM_DWORDS = 8;
  localparam MSG_NUM_DWORDS = 16;
  localparam PRIVKEY_NUM_DWORDS = 1224;
  localparam PRIVKEY_REG_NUM_DWORDS = 32;
  localparam PRIVKEY_REG_RHO_NUM_DWORDS = 8;
  localparam SIGNATURE_H_NUM_DWORDS = 21;
  localparam VERIFY_RES_NUM_DWORDS = 16;
  localparam PRIVKEY_MEM_NUM_DWORDS = PRIVKEY_NUM_DWORDS - PRIVKEY_REG_NUM_DWORDS;
  localparam SIGNATURE_C_NUM_DWORDS = 16;
  localparam SIGNATURE_Z_NUM_DWORDS = 1120;
  localparam SIGNATURE_NUM_DWORDS = SIGNATURE_H_NUM_DWORDS + SIGNATURE_Z_NUM_DWORDS + SIGNATURE_C_NUM_DWORDS;

  localparam MLDSA_REG_RHO_P_NUM_DWORDS = PRIVKEY_REG_RHO_NUM_DWORDS;
  localparam ABR_SCRATCH_REG_NUM_DWORDS = 48;
  localparam MLDSA_ENTROPY_NUM_DWORDS   = 16;
  localparam MLDSA_SIGN_RND_NUM_DWORDS  = 8; 


  // What: An ECC read-check may only follow a genuine mailbox SRAM read.
  // Why: The mailbox DMA write path must not trigger the ECC read-check on a write.
  // Timing: 1 cycle because the ECC check is sampled from the prior request cycle.
  `CALIPTRA_ASSERT(MboxEccCheckFollowsSramRead_A,
      `MBOX_PATH.sram_rd_ecc_en |-> $past(`MBOX_PATH.mbox_sram_req_cs & ~`MBOX_PATH.mbox_sram_req_we),
      `MBOX_PATH.clk, ~`MBOX_PATH.rst_b);

  // What: Any mailbox SRAM write must not generate an ECC read-check on the next cycle.
  // Why: The #1183 regression was caused by a DMA write into mailbox SRAM.
  // Timing: 1 cycle because the read-check is sampled from the prior request cycle.
  `CALIPTRA_ASSERT(MboxSramWriteNoEccCheck_A,
      $past(`MBOX_PATH.mbox_sram_req_cs & `MBOX_PATH.mbox_sram_req_we) |-> !`MBOX_PATH.sram_rd_ecc_en,
      `MBOX_PATH.clk, ~`MBOX_PATH.rst_b);

  // What: ECC decode inputs must be known whenever a read-check is enabled.
  // Why: The SRAM model returns X on non-read cycles; unknown inputs must not be consumed.
  // Timing: 0 cycles because the property is checked on the same cycle as the enable.
  `CALIPTRA_ASSERT(MboxEccInputKnown_A,
      `MBOX_PATH.sram_rd_ecc_en |-> (!$isunknown(`MBOX_PATH.sram_rdata) && !$isunknown(`MBOX_PATH.sram_rdata_ecc)),
      `MBOX_PATH.clk, ~`MBOX_PATH.rst_b);

  // What: Cover the DMA-write-into-mailbox path that triggered the regression.
  // Why: This prevents a false pass when the functional path is never exercised.
  // Timing: 0 cycles because the cover is sampled on the write cycle itself.
  MboxDmaSramWrite_C: cover property (@(posedge `MBOX_PATH.clk) disable iff (~`MBOX_PATH.rst_b)
      `MBOX_PATH.dma_sram_req_dv_q && `MBOX_PATH.dma_sram_req_write && `MBOX_PATH.mbox_sram_req_cs && `MBOX_PATH.mbox_sram_req_we);

  // What: Cover the protocol/pointer-path analog of the #1183 hazard: a genuine mailbox
  //       SRAM write (mbox_protocol_sram_we, i.e. inc_wrptr) landing in the same cycle as
  //       a mailbox SRAM read/pointer-reset request (mbox_protocol_sram_rd, i.e.
  //       inc_rdptr | rst_mbox_rdptr). This can arise if the current lock-holder (uC, SoC,
  //       or TAP) issues an out-of-order datain/wrptr-increment write in the same cycle its
  //       own status/execute write causes an EXECUTE-state transition arc to fire.
  // Why: If reachable, this is the same failure signature as #1183 (a write cycle
  //      simultaneously satisfying a read-enable term) via a different trigger than DMA.
  //      MboxSramWriteNoEccCheck_A above is the decisive pass/fail check for this path.
  // Timing: 0 cycles because the cover is sampled on the overlap cycle itself.
  MboxProtocolWriteReadOverlap_C: cover property (@(posedge `MBOX_PATH.clk) disable iff (~`MBOX_PATH.rst_b)
      `MBOX_PATH.mbox_protocol_sram_we && `MBOX_PATH.mbox_protocol_sram_rd);

  //Create a flopped version of hmac kv_data_present to be used to disable tag write OCP SVAs in case result is not expected to go to KV
  logic hmac_kv_data_present_f;

  always_ff @(posedge `SVA_RDC_CLK or negedge `SVA_RST) begin
    if (!`SVA_RST) begin
      hmac_kv_data_present_f <= 0;
    end
    else begin
      if (`HMAC_PATH.kv_data_present)
        hmac_kv_data_present_f <= 1;
      else if (`HMAC_PATH.kv_write_done)
        hmac_kv_data_present_f <= 0;
    end
  end

  //TODO: add disable condition based on doe cmd reg
  DOE_lock_uds_set:        assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (~`SVA_RST)
                                            $rose(`DOE_PATH.flow_done) && $past(doe_cmd_reg_t'(`DOE_PATH.doe_cmd_reg.cmd) == DOE_UDS) |=> `DOE_PATH.lock_uds_flow
                                          )
                            else $display("SVA ERROR: lock_uds_flow was not set after UDS flow");

  //Note: lock + reset checks will use ungated clock. Using RDC clk throws the SVA off in the very first cycle where lock was 0
  //but there's no $past value to compare against. This problem doesn't exist when using ungated clk because in the first cycle,
  //pwrgood is also 0, so SVA is disabled.
  DOE_lock_uds_cold_reset: assert property (
                                            @(posedge `SVA_CLK)
                                            ~`DOE_PATH.hard_rst_b |-> (`DOE_PATH.lock_uds_flow == 0)
                                          )
                            else $display("SVA ERROR: lock_uds_flow was not reset on hard reset");

  DOE_lock_uds_warm_reset: assert property (
                                            @(posedge `SVA_CLK)
                                            disable iff (~`DOE_PATH.rst_b && ~`DOE_PATH.hard_rst_b)
                                            ~`DOE_PATH.rst_b |-> $past(`DOE_PATH.lock_uds_flow) == `DOE_PATH.lock_uds_flow
                                          )
                            else $display("SVA ERROR: lock_uds_flow toggled after warm reset");
  DOE_lock_fe_set:         assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (~`SVA_RST)
                                            $rose(`DOE_PATH.flow_done) && $past(doe_cmd_reg_t'(`DOE_PATH.doe_cmd_reg.cmd) == DOE_FE) |=> `DOE_PATH.lock_fe_flow
                                          )
                            else $display("SVA ERROR: lock_fe_flow was not set after FE flow");

  DOE_lock_fe_cold_reset:    assert property (
                                            @(posedge `SVA_CLK)
                                            ~`DOE_PATH.hard_rst_b |-> (`DOE_PATH.lock_fe_flow == 0)
                                          )
                            else $display("SVA ERROR: lock_fe_flow was not reset on hard reset");

  DOE_lock_fe_warm_reset:    assert property (
                                            @(posedge `SVA_CLK)
                                            disable iff (~`DOE_PATH.rst_b && ~`DOE_PATH.hard_rst_b)
                                            ~`DOE_PATH.rst_b |-> $past(`DOE_PATH.lock_fe_flow) == `DOE_PATH.lock_fe_flow
                                          )
                            else $display("SVA ERROR: lock_fe_flow toggled after warm reset");

  DOE_lock_hek_set:        assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (~`SVA_RST)
                                            $rose(`DOE_PATH.flow_done) && $past(doe_cmd_reg_t'(`DOE_PATH.doe_cmd_reg.cmd) == DOE_HEK) |=> `DOE_PATH.lock_hek_flow
                                          )
                            else $display("SVA ERROR: lock_hek_flow was not set after HEK flow");

  DOE_lock_hek_cold_reset:   assert property (
                                            @(posedge `SVA_CLK)
                                            ~`DOE_PATH.hard_rst_b |-> (`DOE_PATH.lock_hek_flow == 0)
                                          )
                            else $display("SVA ERROR: lock_hek_flow was not reset to expected value on hard reset");

  DOE_lock_hek_warm_reset:   assert property (
                                            @(posedge `SVA_CLK)
                                            disable iff (~`DOE_PATH.rst_b && ~`DOE_PATH.hard_rst_b)
                                            ~`DOE_PATH.rst_b |-> $past(`DOE_PATH.lock_hek_flow) == `DOE_PATH.lock_hek_flow
                                          )
                            else $display("SVA ERROR: lock_hek_flow toggled after warm reset");

  //Corner case: when clear_obf_secrets and reset events happen in the same cycle, reset deassertion will cause SVA to start checking
  //But if clear_obf_secrets was already 1 (not a pulse), it expects to see status valid in the next clk, but in design, it takes an extra
  //cycle to update status. Adding a 1 cycle delay to avoid this case by starting the check when reset is deasserted
  DOE_clear_obf_status_valid: assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (~`DOE_PATH.rst_b)
                                            `CPTRA_TOP_PATH.clear_obf_secrets && `DOE_PATH.rst_b |=> (`DOE_REG_PATH.field_storage.DOE_STATUS.VALID.value && `DOE_REG_PATH.field_storage.DOE_STATUS.DEOBF_SECRETS_CLEARED.value)
                                          )
                            else $display("SVA ERROR: DOE STATUS valid bit not set after clear obf secrets cmd");

  KV_haddr_valid:          assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (~`KEYVAULT_PATH.hsel_i)
                                            `KEYVAULT_PATH.hsel_i |-> !$isunknown(`KEYVAULT_PATH.haddr_i)
                                          )
                            else $display("SVA ERROR: AHB address not valid in keyvault");

  // Per-slot function to check debug flush value for a single KV entry
  // Verifies all dwords in the given entry match the expected debug value
  function automatic logic check_kv_slot_debug_value(int entry);
    logic sel_value = `KEYVAULT_PATH.kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value.value;
    logic [31:0] expected_value = sel_value ? CLP_DEBUG_MODE_KV_1 : CLP_DEBUG_MODE_KV_0;
    if ((debug_unlocked_latched || `SOC_IFC_TOP_PATH.cptra_error_fatal || `CPTRA_TOP_PATH.cptra_scan_mode_Latched) && `KEYVAULT_PATH.cptra_pwrgood) begin
      for (int dword = 0; dword < KV_NUM_DWORDS; dword++) begin
        if (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[entry][dword].data.value != expected_value) begin
          $display("SVA ERROR: KV[%0d][%0d] debug flush failed. Expected: %h, Got: %h, SelValue: %0d", entry, dword, expected_value, `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[entry][dword].data.value, sel_value);
          return 1'b0;
        end
      end
    end
    return 1'b1;
  endfunction

  // Per-slot debug flush assertions.
  // Edge-triggered on entry to debug-locked false, fatal error, or scan mode.
  generate
    for (genvar entry = 0; entry < KV_NUM_KEYS; entry++) begin : gen_kv_debug_per_slot
      KV_debug_slot: assert property (
        @(posedge `SVA_RDC_CLK)
        disable iff(!`KEYVAULT_PATH.cptra_pwrgood)
        ($rose( ((debug_unlocked_latched) || `SOC_IFC_TOP_PATH.cptra_error_fatal || `CPTRA_TOP_PATH.cptra_scan_mode_Latched) &&
               `KEYVAULT_PATH.cptra_pwrgood) |=> check_kv_slot_debug_value(entry)))
      else $display("SVA ERROR: KV[%0d] debug flush comprehensive check failed", entry);
    end
  endgenerate

  generate
    for (genvar dword = 0; dword < KV_NUM_DWORDS; dword++) begin
      //mlkem shared key write
      if (dword < MLKEM_SHAREDKEY_NUM_DWORDS) begin
          kv_mlkem_sharedkey_w_flow:       assert property (
                                                @(posedge `SVA_RDC_CLK)
                                                (`ABR_PATH.kv_mlkem_sharedkey_done & ~`SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry][dword].data.value == `ABR_PATH.mlkem_sharedkey_data[dword])
                                                )
                                    else $display("SVA ERROR: MLKEM sharedkey mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry][dword].data.value, `ABR_PATH.mlkem_sharedkey_data[dword]);                    

          kv_mlkem_sharedkey_w_std_to_std_flow: assert property (
                                                @(posedge `SVA_RDC_CLK)
                                                (`ABR_PATH.kv_mlkem_sharedkey_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & 
                                                ((`ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data0_present & `ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data0_entry <= KV_STANDARD_SLOT_HI) |
                                                 (`ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data1_present & `ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data1_entry <= KV_STANDARD_SLOT_HI)) &
                                                (`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry <= KV_STANDARD_SLOT_HI) |-> 
                                                `ABR_PATH.kv_mlkem_sharedkey_write_inst.kv_write_rules.write_allow & 
                                                (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry][dword].data.value == `ABR_PATH.mlkem_sharedkey_data[dword])
                                                )
                                    else $display("SVA ERROR: MLKEM sharedkey mismatch for STD to STD flow in OCP LOCK mode!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry][dword].data.value, `ABR_PATH.mlkem_sharedkey_data[dword]);

          kv_mlkem_sharedkey_lock_to_lock_nonkv23_flow: assert property (
                                                @(posedge `SVA_RDC_CLK)
                                                (`ABR_PATH.kv_mlkem_sharedkey_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & 
                                                ((`ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data0_present & `ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data0_entry >= KV_OCP_LOCK_SLOT_LOW) |
                                                 (`ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data1_present & `ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data1_entry >= KV_OCP_LOCK_SLOT_LOW)) &
                                                ((`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry >= KV_OCP_LOCK_SLOT_LOW) & 
                                                 (`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry != OCP_LOCK_KEY_RELEASE_KV_SLOT)) |-> 
                                                 `ABR_PATH.kv_mlkem_sharedkey_write_inst.kv_write_rules.write_allow & 
                                                 (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry][dword].data.value == `ABR_PATH.mlkem_sharedkey_data[dword])
                                                )
                                    else $display("SVA ERROR: MLKEM sharedkey mismatch for LOCK to LOCK flow in OCP LOCK mode!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry][dword].data.value, `ABR_PATH.mlkem_sharedkey_data[dword]);
`ifndef VERILATOR
          kv_mlkem_sharedkey_kv23_flow: assert property (
                                                @(posedge `SVA_RDC_CLK)
                                                (`ABR_PATH.kv_mlkem_sharedkey_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & 
                                                ((`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT)) |-> 
                                                ~`ABR_PATH.kv_mlkem_sharedkey_write_inst.kv_write_rules.write_allow & 
                                                $stable($past(`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry][dword].data.value,16))
                                                )
                                    else $display("SVA ERROR: MLKEM sharedkey mismatch for LOCK to LOCK flow in OCP LOCK mode!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry][dword].data.value, `ABR_PATH.mlkem_sharedkey_data[dword]);

          kv_mlkem_sharedkey_w_lock_to_std_illegal_flow: assert property (
                                                @(posedge `SVA_RDC_CLK)
                                                (`ABR_PATH.kv_mlkem_sharedkey_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & 
                                                ((`ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data0_present & `ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data0_entry >= KV_OCP_LOCK_SLOT_LOW) |
                                                 (`ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data1_present & `ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data1_entry >= KV_OCP_LOCK_SLOT_LOW)) &
                                                (`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry <= KV_STANDARD_SLOT_HI) |-> 
                                                ~`ABR_PATH.kv_mlkem_sharedkey_write_inst.kv_write_rules.write_allow & 
                                                $stable($past(`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry][dword].data.value, 16))
                                                )
                                    else $display("SVA ERROR: Unexpected MLKEM sharedkey write to illegal slot in LOCK to STD flow in OCP LOCK mode!");

          kv_mlkem_sharedkey_w_std_to_lock_illegal_flow: assert property (
                                                @(posedge `SVA_RDC_CLK)
                                                (`ABR_PATH.kv_mlkem_sharedkey_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & 
                                                ((`ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data0_present & `ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data0_entry <= KV_STANDARD_SLOT_HI) |
                                                 (`ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data1_present & `ABR_PATH.kv_mlkem_sharedkey_write_metrics.kv_data1_entry <= KV_STANDARD_SLOT_HI)) &
                                                (`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry >= KV_OCP_LOCK_SLOT_LOW) |-> 
                                                ~`ABR_PATH.kv_mlkem_sharedkey_write_inst.kv_write_rules.write_allow & 
                                                $stable($past(`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_mlkem_sharedkey_write_ctrl_reg.write_entry][dword].data.value, 16))
                                                )
                                    else $display("SVA ERROR: Unexpected MLKEM sharedkey write to illegal slot in STD to LOCK flow in OCP LOCK mode!");
          
`endif
      end
    end
  endgenerate

  generate
    for(genvar dword = 0; dword < KV_NUM_DWORDS; dword++) begin
      if (dword < MLDSA_SEED_NUM_DWORDS) begin
      //mldsa seed read
      kv_mldsa_seed_r_flow:   assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            $rose(`ABR_PATH.kv_mldsa_seed_done) && (`ABR_PATH.kv_mldsa_seed_error == 0) && (dword < (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_CTRL[`ABR_PATH.kv_read[0].read_entry].last_dword.value + 1)) |-> (`SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress & (`ABR_PATH.kv_read[0].read_entry == 23)) ? (`ABR_PATH.mldsa_seed_reg[dword] == '0) : (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_read[0].read_entry][dword].data.value == `ABR_PATH.mldsa_seed_reg[(MLDSA_SEED_NUM_DWORDS-1) - dword])
                                            )
                                else $display("SVA ERROR: MLDSA seed mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ABR_PATH.kv_read[0].read_entry][dword].data.value, `ABR_PATH.mldsa_seed_reg[(MLDSA_SEED_NUM_DWORDS-1) - dword]);
      end

      //hmac block read
      //If ocp_lock_in_progress = 1 && kv_read_entry == 23, block is not read
      //If ocp_lock_in_progress = 0, block is read from any slot
      kv_hmac_block_r_flow:     assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            $rose(`HMAC_PATH.kv_block_done) && (`HMAC_PATH.kv_block_error == 0) && (dword < (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_CTRL[`HMAC_PATH.kv_read[1].read_entry].last_dword.value + 1)) |-> (`SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress & (`HMAC_PATH.kv_read[1].read_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT)) ? (`HMAC_PATH.block_reg[dword] == '0) : (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_read[1].read_entry][dword].data.value == `HMAC_PATH.block_reg[dword])
                                            )
                                else $display("SVA ERROR: HMAC384 block mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_read[1].read_entry][dword].data.value, `HMAC_PATH.block_reg[dword]);

      //hmac key read
      //If ocp_lock_in_progress = 1 && kv_read_entry == 23, key is not read
      //If ocp_lock_in_progress = 0, key is read from any slot
      if (dword < HMAC_KEY_NUM_DWORDS) begin
        kv_hmac_key_r_flow:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              $rose(`HMAC_PATH.kv_key_done) && (`HMAC_PATH.kv_key_error == 0) && (dword < (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_CTRL[`HMAC_PATH.kv_read[0].read_entry].last_dword.value + 1))|->  (`SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress & (`HMAC_PATH.kv_read[0].read_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT)) ? (`HMAC_PATH.key_reg[dword] == '0) : (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_read[0].read_entry][dword].data.value == `HMAC_PATH.key_reg[dword])
                                              )
                                  else $display("SVA ERROR: HMAC384 key mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_read[0].read_entry][dword].data.value, `HMAC_PATH.key_reg[dword]);
      end

      //hmac tag write
      //If KV entry != 23 && hmac reads key/block/lfsr seed from non-23 KV slot, tag is written (std_to_std or lock_to_lock)
      //If KV entry != 23 && hmac reads key/block/lfsr seed from KV23 && ocp_lock_in_progress = 1, tag is not written
      //If KV entry == 23 && ocp_lock_in_progress = 0, tag is written
      //If KV entry == 23 && ocp_lock_in_progress = 1, tag is not written
      /*
      If ocp_lock_in_progress = 1:
      Key read (input)       Block read (input)      Tag write (output)      Allowed?
      -------------------------------------------------------------------------------------------------------------
      STD                    STD                     STD                     Yes
      LOCK                   LOCK                    LOCK (!= KV23)          Yes
      LOCK                   LOCK                    LOCK (== KV23)          No
      STD                    LOCK                    STD                     No
      LOCK                   STD                     LOCK                    No
      STD                    STD                     LOCK                    No
      LOCK                   LOCK                    STD                     No

      If ocp_lock_in_progress = 0:
      hmac key/block can be read from any KV entry, tag is written to any KV entry
      */
      if (dword < HMAC_TAG_NUM_DWORDS) begin
        kv_hmac_tag_w_flow:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              (`HMAC_PATH.kv_write_done & ~`SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress & (`HMAC_PATH.kv_write_error == 0)) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value == `HMAC_PATH.kv_reg[(`HMAC_PATH.TAG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: HMAC384 tag mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value, `HMAC_PATH.kv_reg[(`HMAC_PATH.TAG_NUM_DWORDS-1) - dword]);                    

        kv_hmac_tag_w_std_to_std_flow: assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              disable iff (!hmac_kv_data_present_f)
                                              (`HMAC_PATH.kv_write_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & (`HMAC_PATH.kv_read[0].read_entry <= KV_STANDARD_SLOT_HI) & (`HMAC_PATH.kv_read[1].read_entry <= KV_STANDARD_SLOT_HI) & (`HMAC_PATH.kv_write_ctrl_reg.write_entry <= KV_STANDARD_SLOT_HI) |-> `HMAC_PATH.hmac_result_kv_write.kv_write_rules.write_allow & (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value == `HMAC_PATH.kv_reg[(`HMAC_PATH.TAG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: HMAC384 tag mismatch for STD to STD flow in OCP LOCK mode!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value, `HMAC_PATH.kv_reg[(`HMAC_PATH.TAG_NUM_DWORDS-1) - dword]);
        kv_hmac_tag_w_lock_to_lock_nonkv23_flow: assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              disable iff (!hmac_kv_data_present_f)
                                              (`HMAC_PATH.kv_write_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & (`HMAC_PATH.kv_read[0].read_entry >= KV_OCP_LOCK_SLOT_LOW) & (`HMAC_PATH.kv_read[1].read_entry >= KV_OCP_LOCK_SLOT_LOW) & ((`HMAC_PATH.kv_write_ctrl_reg.write_entry >= KV_OCP_LOCK_SLOT_LOW) & (`HMAC_PATH.kv_write_ctrl_reg.write_entry != OCP_LOCK_KEY_RELEASE_KV_SLOT)) |-> `HMAC_PATH.hmac_result_kv_write.kv_write_rules.write_allow & (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value == `HMAC_PATH.kv_reg[(`HMAC_PATH.TAG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: HMAC384 tag mismatch for LOCK to LOCK flow in OCP LOCK mode!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value, `HMAC_PATH.kv_reg[(`HMAC_PATH.TAG_NUM_DWORDS-1) - dword]);
`ifndef VERILATOR
        kv_hmac_tag_w_lock_to_lock_kv23_flow: assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              disable iff (!hmac_kv_data_present_f)
                                              (`HMAC_PATH.kv_write_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & (`HMAC_PATH.kv_read[0].read_entry >= KV_OCP_LOCK_SLOT_LOW) & (`HMAC_PATH.kv_read[1].read_entry >= KV_OCP_LOCK_SLOT_LOW) & (`HMAC_PATH.kv_write_ctrl_reg.write_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT) |-> ~`HMAC_PATH.hmac_result_kv_write.kv_write_rules.write_allow & $stable($past(`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value,16))
                                              )
                                  else $display("SVA ERROR: Unexpected HMAC384 tag write to KV23 in LOCK to LOCK flow in OCP LOCK mode!");

        kv_hmac_tag_w_std_to_lock_illegal_flow: assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              disable iff (!hmac_kv_data_present_f)
                                              (`HMAC_PATH.kv_write_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & (`HMAC_PATH.kv_read[0].read_entry <= KV_STANDARD_SLOT_HI) & (`HMAC_PATH.kv_read[1].read_entry <= KV_STANDARD_SLOT_HI) & (`HMAC_PATH.kv_write_ctrl_reg.write_entry >= KV_OCP_LOCK_SLOT_LOW) |-> ~`HMAC_PATH.hmac_result_kv_write.kv_write_rules.write_allow & $stable($past(`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value,16))
                                              )
                                  else $display("SVA ERROR: Unexpected HMAC384 tag write to illegal slot in STD to LOCK flow in OCP LOCK mode!");

        kv_hmac_tag_w_lock_to_std_illegal_flow: assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              disable iff (!hmac_kv_data_present_f)
                                              (`HMAC_PATH.kv_write_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & (`HMAC_PATH.kv_read[0].read_entry >= KV_OCP_LOCK_SLOT_LOW) & (`HMAC_PATH.kv_read[1].read_entry >= KV_OCP_LOCK_SLOT_LOW) & (`HMAC_PATH.kv_write_ctrl_reg.write_entry <= KV_STANDARD_SLOT_HI) |-> ~`HMAC_PATH.hmac_result_kv_write.kv_write_rules.write_allow & $stable($past(`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`HMAC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value,16))
                                              )
                                  else $display("SVA ERROR: Unexpected HMAC384 tag write to illegal slot in LOCK to STD flow in OCP LOCK mode!");


`endif
      end
      
      // ECC
      if (dword < ECC_REG_NUM_DWORDS) begin
        //ecc privkey read
        kv_ecc_privkey_r_flow:    assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              $fell(`ECC_PATH.kv_privkey_write_en) && (`ECC_PATH.kv_privkey_error == 0) && (dword < (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_CTRL[`ECC_PATH.kv_read[0].read_entry].last_dword.value + 1)) |-> (`SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress & (`ECC_PATH.kv_read[0].read_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT)) ? (`ECC_PATH.privkey_reg[dword] == '0) : (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_read[0].read_entry][dword].data.value == `ECC_PATH.privkey_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: ECC privkey read mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_read[0].read_entry][dword].data.value, `ECC_PATH.privkey_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword]);
        kv_ecc_seed_r_flow:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              $fell(`ECC_PATH.kv_seed_write_en) && (`ECC_PATH.kv_seed_error == 0) && (dword < (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_CTRL[`ECC_PATH.kv_read[1].read_entry].last_dword.value + 1)) |-> (`SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress & (`ECC_PATH.kv_read[1].read_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT)) ? (`ECC_PATH.seed_reg[dword] == '0) : (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_read[1].read_entry][dword].data.value == `ECC_PATH.seed_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: ECC seed mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_read[1].read_entry][dword].data.value, `ECC_PATH.seed_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword]);
        //ecc privkey write
        kv_ecc_privkey_w_flow:    assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              (`ECC_PATH.kv_write_done && (`ECC_PATH.kv_write_error == 0) & ~`SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) |-> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value == `ECC_PATH.kv_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: ECC privkey write mismatch!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value, `ECC_PATH.kv_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword]);

        kv_ecc_privkey_w_std_to_std_flow: assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              (`ECC_PATH.kv_write_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & (`ECC_PATH.kv_read[1].read_entry <= KV_STANDARD_SLOT_HI) & (`ECC_PATH.kv_write_ctrl_reg.write_entry <= KV_STANDARD_SLOT_HI) |-> `ECC_PATH.ecc_privkey_kv_write.kv_write_rules.write_allow & (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value == `ECC_PATH.kv_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: ECC privkey mismatch for STD to STD flow in OCP LOCK mode!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value, `ECC_PATH.kv_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword]);
        
        kv_ecc_privkey_w_lock_to_lock_nonkv23_flow: assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              (`ECC_PATH.kv_write_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & (`ECC_PATH.kv_read[1].read_entry >= KV_OCP_LOCK_SLOT_LOW) & (`ECC_PATH.kv_write_ctrl_reg.write_entry >= KV_OCP_LOCK_SLOT_LOW) & (`ECC_PATH.kv_write_ctrl_reg.write_entry != OCP_LOCK_KEY_RELEASE_KV_SLOT) |-> `ECC_PATH.ecc_privkey_kv_write.kv_write_rules.write_allow & (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value == `ECC_PATH.kv_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword])
                                              )
                                  else $display("SVA ERROR: ECC privkey mismatch for LOCK to LOCK flow in OCP LOCK mode!, 0x%04x, 0x%04x", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value, `ECC_PATH.kv_reg[(`ECC_PATH.REG_NUM_DWORDS-1) - dword]);
`ifndef VERILATOR
        kv_ecc_privkey_w_lock_to_lock_kv23_flow: assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              (`ECC_PATH.kv_write_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & (`ECC_PATH.kv_read[1].read_entry >= KV_OCP_LOCK_SLOT_LOW) & (`ECC_PATH.kv_write_ctrl_reg.write_entry >= KV_OCP_LOCK_SLOT_LOW) & (`ECC_PATH.kv_write_ctrl_reg.write_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT) |-> ~`ECC_PATH.ecc_privkey_kv_write.kv_write_rules.write_allow & $stable($past(`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value, 16))
                                              )
                                  else $display("SVA ERROR: Unexpected ECC privkey write to KV23 in LOCK to LOCK flow in OCP LOCK mode!");

        kv_ecc_privkey_w_std_to_lock_illegal_flow: assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              (`ECC_PATH.kv_write_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & (`ECC_PATH.kv_read[1].read_entry <= KV_STANDARD_SLOT_HI) & (`ECC_PATH.kv_write_ctrl_reg.write_entry >= KV_OCP_LOCK_SLOT_LOW) |-> ~`ECC_PATH.ecc_privkey_kv_write.kv_write_rules.write_allow & $stable($past(`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value, 16))
                                              )
                                  else $display("SVA ERROR: Unexpected ECC privkey write to illegal slot in STD to LOCK flow in OCP LOCK mode!");

        kv_ecc_privkey_w_lock_to_std_illegal_flow: assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              (`ECC_PATH.kv_write_done & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress) & (`ECC_PATH.kv_read[1].read_entry >= KV_OCP_LOCK_SLOT_LOW) & (`ECC_PATH.kv_write_ctrl_reg.write_entry <= KV_STANDARD_SLOT_HI) |-> ~`ECC_PATH.ecc_privkey_kv_write.kv_write_rules.write_allow & $stable($past(`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`ECC_PATH.kv_write_ctrl_reg.write_entry][dword].data.value, 16))
                                              )
                                  else $display("SVA ERROR: Unexpected ECC privkey write to illegal slot in LOCK to STD flow in OCP LOCK mode!");

`endif


        //ecc sign r
        pcr_ecc_sign_r:    assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `SERVICES_PATH.check_pcr_ecc_signing |-> (`SERVICES_PATH.ecc_test_vector.R[dword] == `ECC_PATH.hwif_out.ECC_SIGN_R[dword].SIGN_R.value)
                                              )
                                  else $display("SVA ERROR: PCR SIGNING SIGN_R mismatch!, 0x%04x, 0x%04x", `SERVICES_PATH.ecc_test_vector.R[dword], `ECC_PATH.hwif_out.ECC_SIGN_R[dword].SIGN_R.value);                     
        
        //ecc sign s
        pcr_ecc_sign_s:    assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `SERVICES_PATH.check_pcr_ecc_signing |-> (`SERVICES_PATH.ecc_test_vector.S[dword] == `ECC_PATH.hwif_out.ECC_SIGN_S[dword].SIGN_S.value)
                                              )
                                  else $display("SVA ERROR: PCR SIGNING SIGN_S mismatch!, 0x%04x, 0x%04x", `SERVICES_PATH.ecc_test_vector.S[dword], `ECC_PATH.hwif_out.ECC_SIGN_S[dword].SIGN_S.value); 
      end
    end
  endgenerate


  ////////////////////////
  // AES 

  `ifndef VERILATOR
  // Helper function to compare new key with old key
  function automatic logic dw_all_different_or_all_same (input logic [(keymgr_pkg::KeyWidth/32)-1:0][3:0][7:0] op0,
                                                         input logic [(keymgr_pkg::KeyWidth/32)-1:0][3:0][7:0] op1);
      logic same_flag = 1'b0;
      logic diff_flag = 1'b0;
      foreach (op0[dw])
          if (op0[dw] == op1[dw]) begin
              same_flag = 1'b1;
//              $display("[%t] [%m] SAME op0[%d]=0x%x op1[%d]=0x%x", $time, dw, op0[dw], dw, op1[dw]);
          end
      foreach (op0[dw])
          if (op0[dw] != op1[dw]) begin
              diff_flag = 1'b1;
//              $display("[%t] [%m] DIFF op0[%d]=0x%x op1[%d]=0x%x", $time, dw, op0[dw], dw, op1[dw]);
          end
      return same_flag ^ diff_flag;
  endfunction

  // Enforce that every time AES reads new key from KV it either matches the old key in entirety or
  // differs from old key in entirety
  property aes_new_key_fully_overwrites_old_key;
      logic [(keymgr_pkg::KeyWidth/32)-1:0][3:0][7:0] keymgr_key_prev;
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      ($past(`AES_CLP_PATH.keymgr_key.valid) && !`AES_CLP_PATH.keymgr_key.valid, keymgr_key_prev = $past(`AES_CLP_PATH.keymgr_key.key[0] ^ `AES_CLP_PATH.keymgr_key.key[1])) ##0
      (!`AES_CLP_PATH.keymgr_key.valid)[*0:$] ##1
      `AES_CLP_PATH.keymgr_key.valid
      |->
      (dw_all_different_or_all_same(keymgr_key_prev, `AES_CLP_PATH.keymgr_key.key[0] ^ `AES_CLP_PATH.keymgr_key.key[1]) == 1);
  endproperty
  AES_KV_rd_full_key: assert property (aes_new_key_fully_overwrites_old_key)
                      else $display("SVA ERROR: AES core partially read new key into keyvault and kept partial old key!");

  // AES core buffers the KV sideload key as two masked shares
  // (kv_key_masked = key ^ m, kv_key_mask = m).
  // Enforce that both share stages are cleared to 0 for the not-yet-read
  // dwords when reading in a new key.
  AES_KV_rd_reg_clr:  assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      (`AES_CLP_PATH.aes_key_kv_read.write_en && `AES_CLP_PATH.aes_key_kv_read.write_offset == 0)
                                      |=>
                                      // dword 0 is written with new value
                                      // Check that dwords 1:MAX are cleared to 0 in both shares
                                      (~|`AES_CLP_PATH.kv_key_masked[(keymgr_pkg::KeyWidth/32)-1:1] &&
                                       ~|`AES_CLP_PATH.kv_key_mask[(keymgr_pkg::KeyWidth/32)-1:1])
                                      )
                      else $display("SVA ERROR: AES local reg stage for KeyVault not cleared");
  `endif


`ifdef CALIPTRA_MODE_SUBSYSTEM

  // Helper function to check if any key data from KEY_ENTRY[23] exists in DMA FIFO
  function automatic logic key_data_exists_in_fifo();
    logic match_found;
    logic [31:0] key_word;
    logic [31:0] fifo_entry;

    match_found = 1'b0;

    // Check each of the 16 x 32-bit words in KEY_ENTRY[23]
    for (int key_word_idx = 0; key_word_idx < 16; key_word_idx++) begin
      key_word = `KEYVAULT_PATH.kv_reg_hwif_out.KEY_ENTRY[23][key_word_idx];

      // Skip if key word is all zeros (not sensitive data)
      if (key_word != '0) begin
        // Search through all 128 FIFO entries
        for (int fifo_idx = 0; fifo_idx < 128; fifo_idx++) begin
          fifo_entry = `AXI_DMA_CTRL_PATH.i_fifo.gen_normal_fifo.storage[fifo_idx];

          // Check if this key word matches the FIFO entry
          if (fifo_entry == key_word) begin
            $display("[%t] SVA ERROR: AXI DMA KV Assertion: Found key in DMA FIFO: KEY_ENTRY[23][%0d] = %h FIFO entry[%0d] = %h", $time, fifo_idx, fifo_entry, key_word_idx, key_word);
            match_found = 1'b1;
            break;
          end
        end
        if (match_found) break;
      end
    end

    return match_found;
  endfunction

    // Main assertion
  property p_axi_dma_kv_data_isolation;
    @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)

    // Trigger condition: DMA FSM transitions to IDLE with KEYVAULT write route
    ($rose(int'(`AXI_DMA_CTRL_PATH.ctrl_fsm_ps) == int'(axi_dma_reg__status0__axi_dma_fsm_ps__axi_dma_fsm_e__DMA_IDLE)) &&
     (int'(`AXI_DMA_CTRL_PATH.wr_route) == int'(axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT)))

    |->

    // Check condition: No key data should exist in DMA FIFO
    (!key_data_exists_in_fifo());

  endproperty

  // Assertion instantiation
  assert_axi_dma_kv_data_isolation: assert property (p_axi_dma_kv_data_isolation)
    else begin
      $display("SVA ERROR: AXI DMA Key Vault Data Isolation Violation: KEY_ENTRY[23] data detected in DMA FIFO after KEYVAULT operation completion");
    end

`endif 


  `ifndef VERILATOR
  generate
    begin: SHA256_WNTZ_data_check
      for(genvar dword = 0; dword < 8; dword++) begin
        SHA256_WNTZ_data_check: assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            //disable iff (`CPTRA_TOP_PATH.)
                                            (`SERVICES_PATH.WriteData == 'hdd && `SERVICES_PATH.mailbox_write) |=> ##[1:$] $rose(`SHA256_PATH.digest_valid_reg) |=> (`SHA256_PATH.digest_reg[dword] == `SERVICES_PATH.sha256_wntz_test_vector.sha256_wntz_digest[dword])
                                          )
                                  else $display("SVA ERROR: SHA256 wntz digest %h does not match expected digest %h!", `SHA256_PATH.digest_reg[dword], `SERVICES_PATH.sha256_wntz_test_vector.sha256_wntz_digest[dword]);
      end //for
    end //data check
  endgenerate

  generate
    begin: UDS_data_check
    for(genvar dword = 0; dword < `CLP_OBF_UDS_DWORDS; dword++) begin
      DOE_UDS_data_check:  assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
                                            (`SERVICES_PATH.WriteData == 'hEC && `SERVICES_PATH.mailbox_write) |=> ##[1:$] $rose(`DOE_PATH.lock_uds_flow) |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword].data.value == `SERVICES_PATH.doe_test_vector.uds_plaintext[dword])
                                
                                          )
                                  else $display("SVA ERROR: DOE UDS output %h does not match plaintext %h!", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword].data.value, `SERVICES_PATH.doe_test_vector.uds_plaintext[dword]);
    end
    end
  endgenerate
  generate
    begin: FE_data_check
    for(genvar dword = 0; dword < `CLP_OBF_FE_DWORDS; dword++) begin
  
      DOE_FE_data_check:   assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
                                            (`SERVICES_PATH.WriteData == 'hED && `SERVICES_PATH.mailbox_write) |=> ##[1:$] $rose(`DOE_PATH.lock_fe_flow) |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword].data.value == `SERVICES_PATH.doe_test_vector.fe_plaintext[dword])
                                          )
                                  else $display("SVA ERROR: DOE FE output %h does not match plaintext %h!", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword].data.value, `SERVICES_PATH.doe_test_vector.fe_plaintext[dword]);

    end
    end
  endgenerate
  generate
    begin: HEK_data_check
    for(genvar dword = 0; dword < kv_defines_pkg::OCP_LOCK_HEK_NUM_DWORDS; dword++) begin

      DOE_HEK_data_check:  assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
                                            (`SERVICES_PATH.WriteData == 'hD5 && `SERVICES_PATH.mailbox_write) |=> ##[1:$] $rose(`DOE_PATH.lock_hek_flow) |=> (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword].data.value == `SERVICES_PATH.doe_test_vector.hek_plaintext[dword])
                                          )
                                  else $display("SVA ERROR: DOE HEK output %h does not match plaintext %h!", `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_ENTRY[`DOE_REG_PATH.hwif_out.DOE_CTRL.DEST.value][dword].data.value, `SERVICES_PATH.doe_test_vector.hek_plaintext[dword]);

    end
    end
  endgenerate
  `endif

  `ifndef VERILATOR
  // MLDSA Checks

  // Helper function for byte swapping
  function automatic logic [31:0] byte_swap(logic [31:0] data);
    return {data[7:0], data[15:8], data[23:16], data[31:24]};
  endfunction

  // Function to check all private key data (registers + memory banks)
  function automatic logic check_mldsa_privkey();
    // Check scratch registers (0 to PRIVKEY_REG_NUM_DWORDS-1)
    for (int dword = 0; dword < PRIVKEY_REG_NUM_DWORDS; dword++) begin
      logic [31:0] expected = byte_swap(`SERVICES_PATH.mldsa_test_vector.privkey[dword]);
      if (`ABR_PATH.abr_scratch_reg.raw[dword] != expected) begin
        $display("SVA ERROR: [MLDSA keygen] SK register %h does not match expected %h at index %h", 
                 `ABR_PATH.abr_scratch_reg.raw[dword], expected, dword);
        return 1'b0;
      end
    end
    
    // Check even memory bank (bank0)
    for (int dword = 0; dword < PRIVKEY_MEM_NUM_DWORDS/2; dword++) begin
      int idx = PRIVKEY_REG_NUM_DWORDS + (2*dword);
      logic [31:0] expected = byte_swap(`SERVICES_PATH.mldsa_test_vector.privkey[idx]);
      if (`ABR_RAMS_PATH.abr_sk_mem_bank0_inst.ram[dword] != expected) begin
        $display("SVA ERROR: [MLDSA keygen] SK bank0 %h does not match expected %h at index %h",
                 `ABR_RAMS_PATH.abr_sk_mem_bank0_inst.ram[dword], expected, idx);
        return 1'b0;
      end
    end
    
    // Check odd memory bank (bank1)
    for (int dword = 0; dword < PRIVKEY_MEM_NUM_DWORDS/2; dword++) begin
      int idx = PRIVKEY_REG_NUM_DWORDS + 1 + (2*dword);
      logic [31:0] expected = byte_swap(`SERVICES_PATH.mldsa_test_vector.privkey[idx]);
      if (`ABR_RAMS_PATH.abr_sk_mem_bank1_inst.ram[dword] != expected) begin
        $display("SVA ERROR: [MLDSA keygen] SK bank1 %h does not match expected %h at index %h",
                 `ABR_RAMS_PATH.abr_sk_mem_bank1_inst.ram[dword], expected, idx);
        return 1'b0;
      end
    end
    
    return 1'b1;
  endfunction

  // Function to check all public key data (registers + memory)
  function automatic logic check_mldsa_pubkey();
    // Check first 8 dwords in scratch registers
    for (int dword = 0; dword < 8; dword++) begin
      logic [31:0] expected = byte_swap(`SERVICES_PATH.mldsa_test_vector.pubkey[dword]);
      if (`ABR_PATH.abr_scratch_reg.raw[dword] != expected) begin
        $display("SVA ERROR: [MLDSA keygen] PK register %h does not match expected %h at index %h", 
                 `ABR_PATH.abr_scratch_reg.raw[dword], expected, dword);
        return 1'b0;
      end
    end
    
    // Check public key memory (64x10 array)
    for (int i = 0; i < 64; i++) begin
      for (int j = 0; j < 10; j++) begin
        int idx = i*10 + 8 + j;
        logic [31:0] expected = byte_swap(`SERVICES_PATH.mldsa_test_vector.pubkey[idx]);
        logic [31:0] actual = {`ABR_RAMS_PATH.abr_pk_mem_inst.ram[i][(j*4)+3],
                               `ABR_RAMS_PATH.abr_pk_mem_inst.ram[i][(j*4)+2],
                               `ABR_RAMS_PATH.abr_pk_mem_inst.ram[i][(j*4)+1],
                               `ABR_RAMS_PATH.abr_pk_mem_inst.ram[i][(j*4)+0]};
        if (actual != expected) begin
          $display("SVA ERROR: [MLDSA keygen] PK memory %h does not match expected %h at index %0d %0d", 
                   actual, expected, i, j);
          return 1'b0;
        end
      end
    end
    
    return 1'b1;
  endfunction

  // Function to check signature data
  function automatic logic check_mldsa_signature();
    // Check signature C portion (0 to SIGNATURE_C_NUM_DWORDS-1)
    for (int dword = 0; dword < SIGNATURE_C_NUM_DWORDS; dword++) begin
      logic [31:0] expected = byte_swap(`SERVICES_PATH.mldsa_test_vector.signature[dword]);
      if (`ABR_PATH.signature_reg.raw[dword] != expected) begin
        $display("SVA ERROR: [MLDSA signing] Signature C %h does not match expected %h at index %h",
                 `ABR_PATH.signature_reg.raw[dword], expected, dword);
        return 1'b0;
      end
    end
    
    // Check signature H portion (SIGNATURE_C_NUM_DWORDS to SIGNATURE_C_NUM_DWORDS+SIGNATURE_H_NUM_DWORDS-1)
    for (int dword = 0; dword < SIGNATURE_H_NUM_DWORDS; dword++) begin
      int sig_idx = (SIGNATURE_NUM_DWORDS-1) - ((SIGNATURE_H_NUM_DWORDS-1) - dword);
      logic [31:0] expected = byte_swap(`SERVICES_PATH.mldsa_test_vector.signature[sig_idx]);
      if (`ABR_PATH.signature_reg.raw[SIGNATURE_C_NUM_DWORDS + dword] != expected) begin
        $display("SVA ERROR: [MLDSA signing] Signature H %h does not match expected %h at index %h",
                 `ABR_PATH.signature_reg.raw[SIGNATURE_C_NUM_DWORDS + dword], expected, SIGNATURE_C_NUM_DWORDS + dword);
        return 1'b0;
      end
    end
    
    // Check signature Z portion in memory (224x5 array)
    for (int i = 0; i < 224; i++) begin
      for (int j = 0; j < 5; j++) begin
        int sig_idx = i*5+16+j;
        logic [31:0] expected = byte_swap(`SERVICES_PATH.mldsa_test_vector.signature[sig_idx]);
        logic [31:0] actual = {`ABR_RAMS_PATH.abr_sig_z_mem_inst.ram[i][(j*4)+3],
                               `ABR_RAMS_PATH.abr_sig_z_mem_inst.ram[i][(j*4)+2],
                               `ABR_RAMS_PATH.abr_sig_z_mem_inst.ram[i][(j*4)+1],
                               `ABR_RAMS_PATH.abr_sig_z_mem_inst.ram[i][(j*4)+0]};
        
        if (actual != expected) begin
          $display("SVA ERROR: [MLDSA signing] Sig output %h does not match expected sig %h at index %0d %0d", 
                   actual, expected, i, j);
          return 1'b0;
        end
      end
    end

    return 1'b1;
  endfunction

  // Function to check all MLDSA verify results at once  
  function automatic logic check_mldsa_verify_results();
    for (int dword = 0; dword < VERIFY_RES_NUM_DWORDS; dword++) begin
      logic [31:0] expected = byte_swap(`SERVICES_PATH.mldsa_test_vector.verify_res[dword]);
      
      if (`ABR_REG_PATH.hwif_out.MLDSA_VERIFY_RES[dword] != expected) begin
        $display("SVA ERROR: [MLDSA verify] Verify output %h does not match expected verify res %h at index %h",
                 `ABR_REG_PATH.hwif_out.MLDSA_VERIFY_RES[dword], expected, dword);
        return 1'b0;
      end
    end
    return 1'b1;
  endfunction

  // Consolidated assertions
  MLDSA_keygen_privkey_comprehensive: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
    (((`SERVICES_PATH.mldsa_keygen || `SERVICES_PATH.mldsa_keygen_signing) && `ABR_PATH.abr_status_done) |=> 
     check_mldsa_privkey())
  )
  else $display("SVA ERROR: [MLDSA keygen] Private key verification failed");

  MLDSA_keygen_pubkey_comprehensive: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
    (((`SERVICES_PATH.mldsa_keygen || `SERVICES_PATH.mldsa_keygen_signing) && `ABR_PATH.abr_status_done) |=> 
     check_mldsa_pubkey())
  )
  else $display("SVA ERROR: [MLDSA keygen] Public key verification failed");

  MLDSA_signature_comprehensive: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input || `SERVICES_PATH.disable_mldsa_sva)
    (((`SERVICES_PATH.mldsa_signing || `SERVICES_PATH.mldsa_keygen_signing || `SERVICES_PATH.check_pcr_mldsa_signing) && `ABR_PATH.abr_status_done) |=> 
     check_mldsa_signature())
  )
  else $display("SVA ERROR: [MLDSA signing] Signature verification failed");

  MLDSA_verify_comprehensive: assert property (
    @(posedge `SVA_RDC_CLK iff (`SERVICES_PATH.mldsa_verify || `ABR_PATH.abr_status_done))
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
    ((`SERVICES_PATH.mldsa_verify && `ABR_PATH.abr_status_done) |=> 
     check_mldsa_verify_results())
  )
  else $display("SVA ERROR: [MLDSA verify] Verification result check failed");

  // MLDSA_VERIFY_RES matches the c field of the supplied signature, i.e. the
  // condition that MLDSA_STATUS.VERIFY_PASS claims to have checked
  function automatic logic check_mldsa_verify_res_matches_c();
    for (int dword = 0; dword < VERIFY_RES_NUM_DWORDS; dword++)
      if (`ABR_REG_PATH.hwif_out.MLDSA_VERIFY_RES[dword] !== `ABR_PATH.signature_reg.enc.c[dword])
        return 1'b0;
    return 1'b1;
  endfunction

  // The hardware pass/fail bit can never disagree with the data returned to FW
  MLDSA_verify_pass_implies_res_match: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
    ($rose(`ABR_REG_PATH.hwif_in.MLDSA_STATUS.VERIFY_PASS.next) |-> check_mldsa_verify_res_matches_c())
  )
  else $display("SVA ERROR: [MLDSA verify] VERIFY_PASS set while VERIFY_RES does not match signature c");

  // An errored MLDSA operation must never report a passing verification
  MLDSA_verify_pass_clear_on_error: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
    (`ABR_PATH.error_flag_reg |-> !`ABR_REG_PATH.hwif_in.MLDSA_STATUS.VERIFY_PASS.next)
  )
  else $display("SVA ERROR: [MLDSA verify] VERIFY_PASS set while error flag is asserted");

  // VERIFY_PASS is allowed to lead MLDSA_STATUS.VALID, but must never lag it.
  // mldsa_process_done (which is what registers VALID) is raised by
  // mldsa_verify_done at the end of the verify program, so once that fires the
  // result flop must already hold its final value: no further write may occur
  // until the next VERIFY command is dispatched.
  MLDSA_verify_pass_not_later_than_valid: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input || `ABR_PATH.zeroize)
    ((`ABR_PATH.mldsa_verifying_process && `ABR_PATH.mldsa_verify_done)
       |=> (!`ABR_PATH.mldsa_verify_res_we) until `ABR_PATH.set_verify_valid)
  )
  else $display("SVA ERROR: [MLDSA verify] VERIFY_PASS updated after MLDSA_STATUS.VALID was raised");

  // A zeroize is mandatory between ABR commands and must always clear the
  // previous verification result.
  MLDSA_verify_pass_clear_on_zeroize: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
    (`ABR_PATH.zeroize |=> !`ABR_PATH.mldsa_verify_pass_reg)
  )
  else $display("SVA ERROR: [MLDSA verify] VERIFY_PASS not cleared on zeroize");

  // Independently of zeroize, the flop is cleared when a VERIFY starts and when
  // a VERIFY aborts early on a rejected signature. Early-abort paths never
  // assert mldsa_verify_res_we, so this clear is what guarantees a VERIFY can
  // never inherit the verdict of a previous run.
  MLDSA_verify_pass_clear_on_verify_start: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
    ((`ABR_PATH.set_verify_valid || `ABR_PATH.clear_verify_valid) |=> !`ABR_PATH.mldsa_verify_pass_reg)
  )
  else $display("SVA ERROR: [MLDSA verify] VERIFY_PASS not cleared at VERIFY start/abort");

  // ECC_VERIFY_R matches the supplied signature R, i.e. the condition that
  // ECC_STATUS.VERIFY_PASS claims to have checked
  function automatic logic check_ecc_verify_r_matches_sign_r();
    for (int dword = 0; dword < ECC_REG_NUM_DWORDS; dword++)
      if (`ECC_REG_PATH.hwif_out.ECC_VERIFY_R[dword].VERIFY_R.value !== `ECC_REG_PATH.hwif_out.ECC_SIGN_R[dword].SIGN_R.value)
        return 1'b0;
    return 1'b1;
  endfunction

  ECC_verify_pass_implies_res_match: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
    ($rose(`ECC_REG_PATH.hwif_in.ECC_STATUS.VERIFY_PASS.next) |-> check_ecc_verify_r_matches_sign_r())
  )
  else $display("SVA ERROR: [ECC verify] VERIFY_PASS set while VERIFY_R does not match SIGN_R");

  ECC_verify_pass_clear_on_error: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
    ((`ECC_PATH.error_flag || `ECC_PATH.error_flag_reg) |-> !`ECC_REG_PATH.hwif_in.ECC_STATUS.VERIFY_PASS.next)
  )
  else $display("SVA ERROR: [ECC verify] VERIFY_PASS set while error flag is asserted");

  // Same ordering requirement on the ECC side: the result flop is only ever
  // written while the engine is still busy, i.e. strictly before ECC_STATUS.VALID
  // is raised for that operation.
  ECC_verify_pass_not_later_than_valid: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input || `ECC_PATH.zeroize_reg)
    ((`ECC_PATH.verifying_process && `ECC_PATH.hw_verify_r_we) |-> !`ECC_PATH.ecc_valid_reg)
  )
  else $display("SVA ERROR: [ECC verify] VERIFY_PASS updated after ECC_STATUS.VALID was raised");

  ECC_verify_pass_clear_on_cmd_start: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (`CPTRA_TOP_PATH.scan_mode || debug_unlocked_input)
    (`ECC_PATH.ecc_cmd_start |=> !`ECC_PATH.ecc_verify_pass_reg)
  )
  else $display("SVA ERROR: [ECC verify] VERIFY_PASS not cleared at command dispatch");


  // MLDSA Scan, Debug and Zeroization Assertions
  generate
    // Check abr_scratch_reg (accessed via its raw field) word-by-word using MLDSA_PRIVKEY_REG_NUM_DWORDS
    for (genvar i = 0; i < ABR_SCRATCH_REG_NUM_DWORDS; i++) begin: privkey_check
      ZERO_MLDSA_K_scratch_reg_check: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_PATH.abr_scratch_reg.raw[i] == 0))
      )
      else $display("SVA ERROR: ABR_PATH.abr_scratch_reg.raw[%0d] is not zero", i);
    end

    ZERO_MLDSA_priv_key_rd_port: assert property (
      @(posedge `SVA_RDC_CLK)
      ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_PATH.api_reg_rdata == 0))
    )
    else $display("SVA ERROR: ABR_PATH.api_reg_rdata is not zero");

    // Check seed_reg word-by-word using MLDSA_SEED_NUM_DWORDS
    for (genvar i = 0; i < MLDSA_SEED_NUM_DWORDS; i++) begin: seed_check
      ZERO_MLDSA_seed_reg: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_PATH.mldsa_seed_reg[i] == 0))
      )
      else $display("SVA ERROR: ABR_PATH.mldsa_seed_reg[%0d] is not zero", i);
    end

    // Check entropy_reg word-by-word using MLDSA_ENTROPY_NUM_DWORDS
    for (genvar i = 0; i < MLDSA_ENTROPY_NUM_DWORDS; i++) begin: entropy_check
      ZERO_MLDSA_entropy_reg: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_PATH.entropy_reg[i] == 0))
      )
      else $display("SVA ERROR: ABR_PATH.entropy_reg[%0d] is not zero", i);
    end

    // Check sign_rnd_reg word-by-word using MLDSA_SIGN_RND_NUM_DWORDS
    for (genvar i = 0; i < MLDSA_SIGN_RND_NUM_DWORDS; i++) begin: sign_rnd_check
      ZERO_MLDSA_sign_rnd_reg: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_PATH.sign_rnd_reg[i] == 0))
      )
      else $display("SVA ERROR: ABR_PATH.sign_rnd_reg[%0d] is not zero", i);
    end

  endgenerate
  // ABR_TOP_PATH Memory Interface Zeroization Assertions
  generate
    // skencode_mem_rd_data: 2-element array of MLDSA_MEM_DATA_WIDTH bits each.
    for (genvar i = 0; i < 2; i++) begin: skencode_mem_rd_data_check
      ZERO_MLDSA_skencode_mem_rd_data: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_TOP_PATH.skencode_mem_rd_data[i] == 0))
      )
      else $display("SVA ERROR: ABR_TOP_PATH.skencode_mem_rd_data[%0d] is not zero", i);
    end
    // skencode_wr_data: Single vector of DATA_WIDTH bits.
    ZERO_MLDSA_skencode_wr_data: assert property (
      @(posedge `SVA_RDC_CLK)
      ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_TOP_PATH.skencode_wr_data == 0))
    )
    else $display("SVA ERROR: ABR_TOP_PATH.skencode_wr_data is not zero");

    // skdecode_mem_wr_data_a/b: split into per-bank signals
    ZERO_MLDSA_skdecode_mem_wr_data_a: assert property (
      @(posedge `SVA_RDC_CLK)
      ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_TOP_PATH.skdecode_mem_wr_data_a[0] == 0))
    )
    else $display("SVA ERROR: ABR_TOP_PATH.skdecode_mem_wr_data_a[0] is not zero");

    ZERO_MLDSA_skdecode_mem_wr_data_b: assert property (
      @(posedge `SVA_RDC_CLK)
      ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_TOP_PATH.skdecode_mem_wr_data_b[0] == 0))
    )
    else $display("SVA ERROR: ABR_TOP_PATH.skdecode_mem_wr_data_b[0] is not zero");

    // skdecode_rd_data: 2-element array of DATA_WIDTH bits each.
    for (genvar i = 0; i < 2; i++) begin: skdecode_rd_data_check
      ZERO_MLDSA_skdecode_rd_data: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_TOP_PATH.skdecode_rd_data[i] == 0))
      )
      else $display("SVA ERROR: ABR_TOP_PATH.skdecode_rd_data[%0d] is not zero", i);
    end

    // abr_mem_rdata0_bank: 2-element array of MLDSA_MEM_DATA_WIDTH bits.
    for (genvar i = 0; i < 2; i++) begin: abr_mem_rdata0_bank_check
      ZERO_MLDSA_abr_mem_rdata0_bank: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_TOP_PATH.abr_mem_rdata0_bank[0][i] == 0))
      )
      else $display("SVA ERROR: ABR_TOP_PATH.abr_mem_rdata0_bank[0][%0d] is not zero", i);
    end

    // abr_mem_wdata: Now indexed [ABR_NUM_NTT-1:0][2:1] after SCA. Check NTT[0] instances.
    for (genvar i = 1; i < 3; i++) begin: abr_mem_wdata_check
      ZERO_MLDSA_abr_mem_wdata: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_TOP_PATH.abr_mem_wdata[0][i] == 0))
      )
      else $display("SVA ERROR: ABR_TOP_PATH.abr_mem_wdata[0][%0d] is not zero", i);
    end

    // abr_mem_masked_wdata: inst3 removed in SCA optimization — assertion removed

    // abr_mem_wdata0_bank: 2-element array of MLDSA_MEM_DATA_WIDTH bits.
    for (genvar i = 0; i < 2; i++) begin: abr_mem_wdata0_bank_check
      ZERO_MLDSA_abr_mem_wdata0_bank: assert property (
        @(posedge `SVA_RDC_CLK)
        ((`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |-> ##10 (`ABR_TOP_PATH.abr_mem_wdata0_bank[0][i] == 0))
      )
      else $display("SVA ERROR: ABR_TOP_PATH.abr_mem_wdata0_bank[0][%0d] is not zero", i);
    end
  endgenerate
  
  // Function to check all SK memory banks are zero
  function automatic logic check_mldsa_sk_memory_zero();
    // Check bank0 memory (even addresses)
    for (int dword = 0; dword < PRIVKEY_MEM_NUM_DWORDS/2; dword++) begin
      if (`ABR_RAMS_PATH.abr_sk_mem_bank0_inst.ram[dword] != 0) begin
        $display("SVA ERROR: [MLDSA zeroize] SK bank0 at index %0d is not zero: %h", 
                 dword, `ABR_RAMS_PATH.abr_sk_mem_bank0_inst.ram[dword]);
        return 1'b0;
      end
    end
    
    // Check bank1 memory (odd addresses)  
    for (int dword = 0; dword < PRIVKEY_MEM_NUM_DWORDS/2; dword++) begin
      if (`ABR_RAMS_PATH.abr_sk_mem_bank1_inst.ram[dword] != 0) begin
        $display("SVA ERROR: [MLDSA zeroize] SK bank1 at index %0d is not zero: %h", 
                 dword, `ABR_RAMS_PATH.abr_sk_mem_bank1_inst.ram[dword]);
        return 1'b0;
      end
    end
    
    return 1'b1;
  endfunction

  // Consolidated zeroization assertions
  MLDSA_sk_memory_zero_comprehensive: assert property (
    @(posedge `SVA_RDC_CLK)
    $rose(`ABR_PATH.zeroize_mem_done) |-> check_mldsa_sk_memory_zero()
  )
  else $display("SVA ERROR: [MLDSA zeroize] SK memory zeroization verification failed");

  // Assertion to check that `ABR_PATH.zeroize_mem_done` transitions from low to high 
  // when (`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) is active
  ZEROIZE_MEM_DONE_TRANSITION: assert property (
    @(posedge `SVA_RDC_CLK)
    $rose(`MLDSA_ZEROIZATION || `MLKEM_ZEROIZATION || `ABR_SCAN_DEBUG) |=> 
    ( !`ABR_PATH.zeroize_mem_done )[*0:$] ##1 
    $rose(`ABR_PATH.zeroize_mem_done)
  )
  else $display("SVA ERROR: [MLDSA zeroize] zeroize_mem_done did not rise when expected");


  


  `endif
  //Generate disable signal for fuse_wr_check sva when hwclr is asserted. The disable needs to be for 3 clks in order to ignore the fuses being cleared
  logic clear_obf_secrets_f;
  logic clear_obf_secrets_ff;
  logic clear_obf_secrets_int;

  logic cptra_in_debug_scan_mode_f;
  logic cptra_in_debug_scan_mode_fall_trans;
  logic cptra_in_debug_scan_mode_fall_trans_f;
  logic cptra_in_debug_scan_mode_int;

  always@(posedge `SVA_RDC_CLK or negedge `CPTRA_TOP_PATH.cptra_rst_b) begin
    if(!`CPTRA_TOP_PATH.cptra_rst_b) begin
      clear_obf_secrets_f <= 'b0;
      clear_obf_secrets_ff <= 'b0;
    end
    else begin
      clear_obf_secrets_f <= `SOC_IFC_TOP_PATH.clear_obf_secrets;
      clear_obf_secrets_ff <= clear_obf_secrets_f;
    end
  end

  always@(posedge `SVA_RDC_CLK or negedge `CPTRA_TOP_PATH.cptra_rst_b) begin
    if(!`CPTRA_TOP_PATH.cptra_rst_b) begin
      cptra_in_debug_scan_mode_f <= 'b0;
      cptra_in_debug_scan_mode_fall_trans_f <= 'b0;
    end
    else begin
      cptra_in_debug_scan_mode_f <= `CPTRA_TOP_PATH.cptra_in_debug_scan_mode;
      cptra_in_debug_scan_mode_fall_trans_f <= cptra_in_debug_scan_mode_fall_trans;
    end
  end

  assign clear_obf_secrets_int = `SOC_IFC_TOP_PATH.clear_obf_secrets | clear_obf_secrets_f | clear_obf_secrets_ff;
  assign cptra_in_debug_scan_mode_fall_trans = !`CPTRA_TOP_PATH.cptra_in_debug_scan_mode && cptra_in_debug_scan_mode_f;
  assign cptra_in_debug_scan_mode_int = cptra_in_debug_scan_mode_fall_trans | cptra_in_debug_scan_mode_fall_trans_f;

  UDS_fuse_wr_check: assert property (
                                  @(posedge `SVA_RDC_CLK)
                                  disable iff(`CPTRA_TOP_PATH.cptra_in_debug_scan_mode || clear_obf_secrets_int || cptra_in_debug_scan_mode_int)
                                  (`SOC_IFC_TOP_PATH.soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value) |-> `CPTRA_TOP_PATH.obf_uds_seed == $past(`CPTRA_TOP_PATH.obf_uds_seed)
  )
  else $display("SVA ERROR: Unexpected write to obf uds seed!");

  FE_fuse_wr_check: assert property (
                                  @(posedge `SVA_RDC_CLK)
                                  disable iff(`CPTRA_TOP_PATH.cptra_in_debug_scan_mode || clear_obf_secrets_int || cptra_in_debug_scan_mode_int)
                                  (`SOC_IFC_TOP_PATH.soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value) |-> `CPTRA_TOP_PATH.obf_field_entropy == $past(`CPTRA_TOP_PATH.obf_field_entropy)
  )
  else $display("SVA ERROR: Unexpected write to obf field entropy!");

  //ZEROIZE SVA
  generate
    for(genvar dword = 0; dword < SHA256_BLOCK_NUM_DWORDS; dword++) begin
        sha256_block_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `SHA256_PATH.hwif_out.SHA256_CTRL.ZEROIZE.value |=> (`SHA256_PATH.hwif_out.SHA256_BLOCK[dword].BLOCK.value == 0)
                                              )
                                  else $display("SVA ERROR: SHA256 block zeroize mismatch!");
    end

    for(genvar dword = 0; dword < SHA256_DIG_NUM_DWORDS; dword++) begin
        sha256_digest_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `SHA256_PATH.hwif_out.SHA256_CTRL.ZEROIZE.value |=> (`SHA256_PATH.digest_reg[dword] == 0) & (`SHA256_PATH.i_sha256_reg.field_storage.SHA256_DIGEST[dword].DIGEST.value == 0)
                                              )
                                  else $display("SVA ERROR: SHA256 digest zeroize mismatch!");                                
    end

    for(genvar dword = 0; dword < SHA512_BLOCK_NUM_DWORDS; dword++) begin
        sha512_block_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `SHA512_PATH.hwif_out.SHA512_CTRL.ZEROIZE.value |=> (`SHA512_PATH.hwif_out.SHA512_BLOCK[dword].BLOCK.value == 0)
                                              )
                                  else $display("SVA ERROR: SHA512 block zeroize mismatch!");
    end

    for(genvar dword = 0; dword < SHA512_DIG_NUM_DWORDS; dword++) begin
        sha512_digest_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `SHA512_PATH.hwif_out.SHA512_CTRL.ZEROIZE.value |=> (`SHA512_PATH.digest_reg[dword] == 0) & (`SHA512_PATH.i_sha512_reg.field_storage.SHA512_DIGEST[dword].DIGEST.value == 0)
                                              )
                                  else $display("SVA ERROR: SHA512 digest zeroize mismatch!");                                
    end

    for(genvar dword = 0; dword < HMAC_KEY_NUM_DWORDS; dword++) begin
        hmac_key_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `HMAC_PATH.hwif_out.HMAC512_CTRL.ZEROIZE.value |=> (`HMAC_PATH.hwif_out.HMAC512_KEY[dword].KEY.value == 0)
                                              )
                                  else $display("SVA ERROR: HMAC384 key zeroize mismatch!");
    end
    
    for(genvar dword = 0; dword < HMAC_BLOCK_NUM_DWORDS; dword++) begin
        hmac_block_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `HMAC_PATH.hwif_out.HMAC512_CTRL.ZEROIZE.value |=> (`HMAC_PATH.hwif_out.HMAC512_BLOCK[dword].BLOCK.value == 0)
                                              )
                                  else $display("SVA ERROR: HMAC384 block zeroize mismatch!");
    end

    for(genvar dword = 0; dword < HMAC_TAG_NUM_DWORDS; dword++) begin
        hmac_tag_zeroize:       assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `HMAC_PATH.hwif_out.HMAC512_CTRL.ZEROIZE.value |=> (`HMAC_PATH.tag_reg[dword] == 0) & (`HMAC_PATH.i_hmac_reg.field_storage.HMAC512_TAG[dword].TAG.value == 0)
                                              )
                                  else $display("SVA ERROR: HMAC384 tag zeroize mismatch!");                      
    end


    for(genvar dword = 0; dword < ECC_REG_NUM_DWORDS; dword++) begin
        ecc_reg_zeroize:        assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `ECC_PATH.hwif_out.ECC_CTRL.ZEROIZE.value |=> (`ECC_PATH.hwif_out.ECC_SEED[dword].SEED.value == 0) & (`ECC_PATH.hwif_out.ECC_NONCE[dword].NONCE.value == 0) & (`ECC_PATH.hwif_out.ECC_PRIVKEY_IN[dword].PRIVKEY_IN.value == 0) &
                                              (`ECC_PATH.hwif_out.ECC_MSG[dword].MSG.value == 0) & (`ECC_PATH.hwif_out.ECC_PUBKEY_X[dword].PUBKEY_X.value == 0) & (`ECC_PATH.hwif_out.ECC_PUBKEY_Y[dword].PUBKEY_Y.value == 0) &
                                              (`ECC_PATH.hwif_out.ECC_SIGN_R[dword].SIGN_R.value == 0) & (`ECC_PATH.hwif_out.ECC_SIGN_S[dword].SIGN_S.value == 0) & (`ECC_PATH.hwif_out.ECC_VERIFY_R[dword].VERIFY_R.value == 0) & (`ECC_PATH.hwif_out.ECC_IV[dword].IV.value == 0) &
                                              (`ECC_REG_PATH.field_storage.ECC_PRIVKEY_OUT[dword].PRIVKEY_OUT.value == 0)
                                              )
                                  else $display("SVA ERROR: ECC reg zeroize mismatch!"); 
    end
    
    for(genvar addr = 0; addr < ECC_MEM_ADDR; addr++) begin
        ecc_mem_zeroize:        assert property (
                                              @(posedge `SVA_RDC_CLK)
                                              `ECC_PATH.hwif_out.ECC_CTRL.ZEROIZE.value |=> (`ECC_PATH.ecc_arith_unit_i.ram_tdp_file_i.mem[addr] == 0)
                                              )
                                  else $display("SVA ERROR: ECC mem zeroize mismatch!"); 
    end

    for(genvar addr = 0; addr < DOE_256_NUM_ROUNDS; addr++) begin
        doe_mem_zeroize:        assert property (
                                              @(posedge `DOE_INST_PATH.clk)
                                              `DOE_INST_PATH.zeroize |=> (`DOE_INST_PATH.i_doe_core_cbc.keymem.key_mem[addr] == 0)
                                              )
                                  else $display("SVA ERROR: DOE mem zeroize mismatch!"); 
    end
  endgenerate

  sha512_masked_core_digest_zeroize:       assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      `ECC_PATH.hwif_out.ECC_CTRL.ZEROIZE.value |=> (`SHA512_MASKED_PATH.digest == 0) & (`SHA512_MASKED_PATH.a_reg == 0) & (`SHA512_MASKED_PATH.b_reg == 0) & (`SHA512_MASKED_PATH.c_reg == 0) & (`SHA512_MASKED_PATH.d_reg == 0) & (`SHA512_MASKED_PATH.e_reg == 0) & (`SHA512_MASKED_PATH.f_reg == 0) & (`SHA512_MASKED_PATH.g_reg == 0) & (`SHA512_MASKED_PATH.h_reg == 0)
                                      )
                          else $display("SVA ERROR: SHA512_masked_core digest zeroize mismatch!");  
  
  doe_block_zeroize:      assert property (
                                      @(posedge `DOE_INST_PATH.clk)
                                      `DOE_INST_PATH.zeroize |=> (`DOE_INST_PATH.i_doe_core_cbc.enc_block.new_block == 0) & (`DOE_INST_PATH.i_doe_core_cbc.dec_block.new_block == 0)
                                      )
                          else $display("SVA ERROR: DOE block zeroize mismatch!"); 

  doe_block_reg_zeroize:  assert property (
                                      @(posedge `DOE_INST_PATH.clk)
                                      `DOE_INST_PATH.zeroize |=> (`DOE_INST_PATH.core_block == 0)
                                      )
                          else $display("SVA ERROR: DOE block reg zeroize mismatch!"); 

  doe_iv_reg_zeroize:     assert property (
                                      @(posedge `DOE_INST_PATH.clk)
                                      $rose(`DOE_INST_PATH.zeroize) |=> (`DOE_INST_PATH.core_IV == 0)
                                      )
                          else $display("SVA ERROR: DOE iv reg zeroize mismatch!"); 

  doe_key_clear:      assert property (
                                      @(posedge `DOE_INST_PATH.clk)
                                      disable iff(`CPTRA_TOP_PATH.cptra_in_debug_scan_mode)
                                      `DOE_INST_PATH.zeroize |=> (`DOE_INST_PATH.core_key == 0)
                                      )
                          else $display("SVA ERROR: DOE key clear mismatch!"); 

  genvar client;
  generate
    for(client = 0; client < KV_NUM_WRITE; client++) begin
      KV_client_wrdata_not_unknown: assert property (
                                                    @(posedge `SVA_RDC_CLK)
                                                    disable iff (!`KEYVAULT_PATH.kv_write[client].write_en || !`KEYVAULT_PATH.rst_b)
                                                    `KEYVAULT_PATH.kv_write[client].write_en |-> !$isunknown(`KEYVAULT_PATH.kv_write[client].write_data)
                                                  )
                                    else $display("SVA ERROR: KV client %0d data is unknown", client);
    end

    for(client = 0; client < KV_NUM_READ; client++) begin
      KV_client_rddata_not_unknown: assert property (
                                                    @(posedge `SVA_RDC_CLK)
                                                    disable iff (!`KEYVAULT_PATH.rst_b)
                                                    !$isunknown(`KEYVAULT_PATH.kv_rd_resp[client].read_data)
                                                  )
                                    else $display("SVA ERROR: KV client %0d data is unknown", client);
    end
  endgenerate

  //KV read error check
  //If ocp_lock_in_progress = 1, kv23 read is not allowed. Other slots can be read
  //If ocp_lock_in_progress = 0, kv23 read is allowed
  // localparam KV_SUCCESS = 0; //TODO: resolve pkg warning during build
  // localparam KV_READ_FAIL = 1;
  // localparam KV_WRITE_FAIL = 2;

  hmac_key_kv23_read_error_check: assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            ($fell(`HMAC_PATH.kv_key_write_en) & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress &  `KEYVAULT_PATH.kv_read[0].read_entry == 23) |-> /*(`KEYVAULT_PATH.kv_rd_resp[0].error == 1'b1)*/ (`HMAC_PATH.hmac_key_kv_read.error_code == 1)
                                            )
                            else $display("SVA ERROR: KV read error not set for KV23 read when ocp_lock_in_progress = 1");

  hmac_key_kv_others_read_error_check: assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (`CPTRA_FW_UPD_RST_WINDOW)
                                            ($fell(`HMAC_PATH.kv_key_write_en) & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress &  (`KEYVAULT_PATH.kv_read[0].read_entry != 23) & (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_CTRL[`HMAC_PATH.kv_read[0].read_entry].dest_valid.value[0])) |-> /*(`KEYVAULT_PATH.kv_rd_resp[0].error == 1'b0)*/ (`HMAC_PATH.hmac_key_kv_read.error_code == 0)
                                            )
                            else $display("SVA ERROR: KV read error set when ocp_lock_in_progress = 1 for non-KV23 read");

  hmac_block_kv23_read_error_check: assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            ($rose(`HMAC_PATH.kv_block_done) & `SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress &  `KEYVAULT_PATH.kv_read[1].read_entry == 23) |-> /*(`KEYVAULT_PATH.kv_rd_resp[0].error == 1'b1)*/ (`HMAC_PATH.hmac_block_kv_read.error_code == 1)
                                            )
                            else $display("SVA ERROR: KV read error not set for KV23 read when ocp_lock_in_progress = 1");

  hmac_block_kv_others_read_error_check: assert property (
                                            @(posedge `SVA_RDC_CLK)
                                            disable iff (`CPTRA_FW_UPD_RST_WINDOW)
                                            ($rose(`HMAC_PATH.kv_block_done) &`SOC_IFC_TOP_PATH.ss_ocp_lock_in_progress &  `KEYVAULT_PATH.kv_read[1].read_entry != 23 & (`KEYVAULT_PATH.kv_reg1.hwif_out.KEY_CTRL[`HMAC_PATH.kv_read[1].read_entry].dest_valid.value[1])) |-> /*(`KEYVAULT_PATH.kv_rd_resp[1].error == 1'b0)*/ (`HMAC_PATH.hmac_block_kv_read.error_code == 0)
                                            )
                            else $display("SVA ERROR: KV read error set when ocp_lock_in_progress = 1 for non-KV23 read");

                            
  
  //WDT checks:
  cascade_wdt_t1_pet: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.timer1_restart && `WDT_PATH.timer1_en && !`WDT_PATH.timer2_en && !`WDT_PATH.t1_timeout) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer1 did not restart on pet");

  cascade_wdt_t2_pet: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.timer2_restart && !`WDT_PATH.timer2_en && !`WDT_PATH.t2_timeout) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer2 did not restart on pet");

  cascade_wdt_t1_service: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.wdt_timer1_timeout_serviced_qual && `WDT_PATH.timer1_en && !`WDT_PATH.timer2_en && !`WDT_PATH.t2_timeout) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer1 did not restart after interrupt service");

  cascade_wdt_t2_service: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.wdt_timer2_timeout_serviced_qual && !`WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Cascade] WDT Timer2 did not restart after interrupt service");

  independent_wdt_t1_pet: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.timer1_restart && `WDT_PATH.timer1_en && `WDT_PATH.timer2_en) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer1 did not restart on pet");

  independent_wdt_t2_pet: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.timer2_restart && `WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer2 did not restart on pet");

  independent_wdt_t1_service: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.wdt_timer1_timeout_serviced_qual && `WDT_PATH.timer1_en && `WDT_PATH.timer2_en && !`WDT_PATH.t2_timeout) |=> (`WDT_PATH.timer1_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer1 did not restart after interrupt service");

  independent_wdt_t2_service: assert property (
    @(posedge `SVA_RDC_CLK)
    (`WDT_PATH.wdt_timer2_timeout_serviced_qual && `WDT_PATH.timer2_en) |=> (`WDT_PATH.timer2_count == 'h0)
  )
  else $display("SVA ERROR: [Independent] WDT Timer2 did not restart after interrupt service");

  wdt_status_t1_check: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (~`SVA_RST)
    $rose(`WDT_PATH.t1_timeout) |=> $rose(`SOC_IFC_TOP_PATH.soc_ifc_reg_hwif_out.CPTRA_WDT_STATUS.t1_timeout.value)
  )
  else $display("SVA ERROR: WDT Status bit not set on t1 expiry!");

  wdt_status_t2_check: assert property (
    @(posedge `SVA_RDC_CLK)
    disable iff (~`SVA_RST)
    $rose(`WDT_PATH.t2_timeout) |=> $rose(`SOC_IFC_TOP_PATH.soc_ifc_reg_hwif_out.CPTRA_WDT_STATUS.t2_timeout.value)
  )
  else $display("SVA ERROR: WDT Status bit not set on t2 expiry!");



  //VALID flag SVA
  sha512_valid_flag:        assert property (
                                    @(posedge `SVA_RDC_CLK)
                                    `SHA512_PATH.digest_valid_reg |-> `SHA512_PATH.ready_reg
                                    )
                        else $display("SVA ERROR: SHA512 VALID flag mismatch!");
                          
  sha256_valid_flag:        assert property (
                                        @(posedge `SVA_RDC_CLK)
                                        `SHA256_PATH.digest_valid_reg |-> `SHA256_PATH.ready_reg
                                        )
                            else $display("SVA ERROR: SHA256 VALID flag mismatch!");

  HMAC_valid_flag:      assert property (
                                    @(posedge `SVA_RDC_CLK)
                                    `HMAC_PATH.tag_valid_reg |-> `HMAC_PATH.ready_reg
                                    )
                        else $display("SVA ERROR: HMAC VALID flag mismatch!"); 

  ECC_valid_flag:       assert property (
                                    @(posedge `SVA_RDC_CLK)
                                    `ECC_PATH.ecc_valid_reg |-> `ECC_PATH.ecc_ready_reg 
                                    )
                        else $display("SVA ERROR: ECC VALID flag mismatch!");
                        
  //MLDSA_valid_flag:     assert property (
  //                        @(posedge `SVA_RDC_CLK)
  //                        disable iff (`SERVICES_PATH.disable_mldsa_sva)
  //                        `ABR_PATH.mldsa_valid_reg |-> `ABR_PATH.abr_ready
  //                    )
  //                    else $display("SVA ERROR: MLDSA VALID flag mismatch!");

  //SVA for SHA512 restore
  sha512_restore_cmd:   assert property ( 
                                    @(posedge `SVA_RDC_CLK) 
                                    `SHA512_PATH.restore_reg |-> (`SHA512_PATH.next_reg && !`SHA512_PATH.init_reg)
                                    ) 
                         else $display("SVA ERROR: SHA512 restore is not valid!");

  //SVA for modular operations
  ecc_opa_input:        assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      (`ECC_PATH.ecc_arith_unit_i.ecc_fau_i.add_en_i | `ECC_PATH.ecc_arith_unit_i.ecc_fau_i.mult_en_i) |-> (`ECC_PATH.ecc_arith_unit_i.ecc_fau_i.opa_i < `ECC_PATH.ecc_arith_unit_i.ecc_fau_i.prime_i)
                                      )
                          else $display("SVA ERROR: ECC opa input is not valid!"); 

  ecc_opb_input:        assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      (`ECC_PATH.ecc_arith_unit_i.ecc_fau_i.add_en_i | `ECC_PATH.ecc_arith_unit_i.ecc_fau_i.mult_en_i) |-> (`ECC_PATH.ecc_arith_unit_i.ecc_fau_i.opb_i < `ECC_PATH.ecc_arith_unit_i.ecc_fau_i.prime_i)
                                      )
                          else $display("SVA ERROR: ECC opb input is not valid!"); 

  ecc_add_result:       assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      `ECC_PATH.ecc_arith_unit_i.ecc_instr_s.opcode.add_we |-> (`ECC_PATH.ecc_arith_unit_i.add_res_s < `ECC_PATH.ecc_arith_unit_i.adder_prime)
                                      )
                          else $display("SVA ERROR: ECC adder result is not valid!"); 

  ecc_mult_result:       assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      `ECC_PATH.ecc_arith_unit_i.ecc_instr_s.opcode.mult_we |-> (`ECC_PATH.ecc_arith_unit_i.mult_res_s < `ECC_PATH.ecc_arith_unit_i.adder_prime)
                                      )
                          else $display("SVA ERROR: ECC multiplier result is not valid!"); 

  // SVA for LMS WNTZ accelerator
    wntz_mode:        assert property (
                                        @(posedge `SVA_RDC_CLK)
                                        `SHA256_PATH.init_reg |-> !`SHA256_PATH.next_reg
                                        )
                            else $display("SVA ERROR: SHA256 operation is not valid with INIT and NEXT asserted in the same cycle!");

  // Bus IDLE on Firmware Update Reset
  fw_upd_rst_doe_idle:     assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`DOE_REG_PATH.s_cpuif_req)
                           else $display("SVA ERROR: DOE bus not idle after Firmware Update Reset!");
  fw_upd_rst_ecc_idle:     assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`ECC_REG_PATH.s_cpuif_req)
                           else $display("SVA ERROR: ECC bus not idle after Firmware Update Reset!");
  fw_upd_rst_hmac_idle:    assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`HMAC_REG_PATH.s_cpuif_req)
                           else $display("SVA ERROR: HMAC bus not idle after Firmware Update Reset!");
  fw_upd_rst_kv_idle:      assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`KEYVAULT_REG_PATH.s_cpuif_req)
                           else $display("SVA ERROR: Key Vault bus not idle after Firmware Update Reset!");
  fw_upd_rst_pv_idle:      assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`PCRVAULT_REG_PATH.s_cpuif_req)
                           else $display("SVA ERROR: PCR Vault bus not idle after Firmware Update Reset!");
  fw_upd_rst_dv_idle:      assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`DATA_VAULT_REG_PATH.s_cpuif_req)
                           else $display("SVA ERROR: Data Vault bus not idle after Firmware Update Reset!");
  fw_upd_rst_sha256_idle:  assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`SHA256_PATH.i_sha256_reg.s_cpuif_req)
                           else $display("SVA ERROR: SHA256 bus not idle after Firmware Update Reset!");
  fw_upd_rst_sha512_idle:  assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`SHA512_PATH.i_sha512_reg.s_cpuif_req)
                           else $display("SVA ERROR: SHA512 bus not idle after Firmware Update Reset!");
  fw_upd_rst_soc_ifc_idle: assert property (@(posedge `SVA_RDC_CLK) `CPTRA_FW_UPD_RST_WINDOW |-> !`SOC_IFC_TOP_PATH.i_ahb_slv_sif_soc_ifc.dv)
                           else $display("SVA ERROR: SOC_IFC bus not idle after Firmware Update Reset!");


  hmac_drbg_zero_result:  assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      `HMAC_DRBG_PATH.valid |-> (`HMAC_DRBG_PATH.drbg != 384'h0 )
                                      )
                          else $display("SVA ERROR: drbg is zero when valid is high"); 

  hmac_drbg_illegal_above_prime:       assert property (
                                      @(posedge `SVA_RDC_CLK)
                                      `HMAC_DRBG_PATH.valid |-> (`HMAC_DRBG_PATH.drbg < `HMAC_DRBG_PATH.HMAC_DRBG_PRIME)
                                      )
                          else $display("SVA ERROR: drbg >= HMAC_DRBG_PRIME when valid is high"); 

  // ===========================================================================
  // KV SWWE Lock Assertions
  // Verify that KV write control registers (write_entry, dest_valid) are stable
  // while the crypto engine is busy. The SWWE uses !busy_o to prevent FW from
  // redirecting key material mid-transfer.
  // ===========================================================================

  // What: HMAC KV WR_CTRL write_entry must not change while busy
  // Why: Prevents partial-key attack by redirecting KV write to a different slot
  // Note: Guard with $past(busy_o) to skip the first cycle busy_o rises (FW may have just configured it)
  HmacKvWrEntryStableWhileBusy_A: assert property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      $past(`HMAC_PATH.busy_o) && `HMAC_PATH.busy_o |->
      $stable(`HMAC_PATH.kv_write_ctrl_reg.write_entry))
  else $display("SVA ERROR: HMAC KV write_entry changed while busy_o=1");

  // What: HMAC KV WR_CTRL write_en must not be SW-re-enabled while busy
  // Why: Prevents re-triggering KV write mid-operation
  // Note: write_en.hwclr = ~kv_write_ready legitimately clears 1→0; only 0→1 is an attack
  HmacKvWrEnNoRiseWhileBusy_A: assert property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      $past(`HMAC_PATH.busy_o) && `HMAC_PATH.busy_o |->
      !$rose(`HMAC_PATH.kv_write_ctrl_reg.write_en))
  else $display("SVA ERROR: HMAC KV write_en rose while busy_o=1");

  // What: ECC KV WR_PKEY_CTRL write_entry must not change while busy
  // Why: Prevents private key slot redirection during ECC operation
  // Note: Guard with $past(busy_o) to skip first cycle after reset and busy_o rise edge
  EccKvWrEntryStableWhileBusy_A: assert property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      $past(`ECC_PATH.busy_o) && `ECC_PATH.busy_o |->
      $stable(`ECC_PATH.kv_write_ctrl_reg.write_entry))
  else $display("SVA ERROR: ECC KV write_entry changed while busy_o=1");

  // What: ECC KV WR_PKEY_CTRL write_en must not be SW-re-enabled while busy
  // Why: Prevents re-triggering KV write mid-ECC operation
  // Note: write_en.hwclr = ~kv_write_ready legitimately clears 1→0; only 0→1 is an attack
  EccKvWrEnNoRiseWhileBusy_A: assert property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      $past(`ECC_PATH.busy_o) && `ECC_PATH.busy_o |->
      !$rose(`ECC_PATH.kv_write_ctrl_reg.write_en))
  else $display("SVA ERROR: ECC KV write_en rose while busy_o=1");

  // What: AES KV WR_CTRL write_entry must not change while busy
  // Why: Prevents AES output key slot redirection during operation
  // Note: Guard with $past(busy_o) to skip first cycle after reset and busy_o rise edge
  AesKvWrEntryStableWhileBusy_A: assert property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      $past(`AES_CLP_PATH.busy_o) && `AES_CLP_PATH.busy_o |->
      $stable(`AES_CLP_PATH.kv_write_ctrl_reg.write_entry))
  else $display("SVA ERROR: AES KV write_entry changed while busy_o=1");

  // What: AES KV WR_CTRL write_en must not be SW-re-enabled while busy
  // Why: Prevents re-triggering KV write mid-AES operation
  // Note: write_en.hwclr = ~kv_write_ready legitimately clears 1→0; only 0→1 is an attack
  AesKvWrEnNoRiseWhileBusy_A: assert property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      $past(`AES_CLP_PATH.busy_o) && `AES_CLP_PATH.busy_o |->
      !$rose(`AES_CLP_PATH.kv_write_ctrl_reg.write_en))
  else $display("SVA ERROR: AES KV write_en rose while busy_o=1");

  // What: SHA512 KV WR_CTRL write_entry must not change while not (ready && kv_dest_ready && !gen_hash_ip)
  // Why: SHA512 uses a combined condition (ready_reg && kv_dest_ready && !gen_hash_ip) for SWWE
  // Note: Guard with $past to skip first cycle after reset
  Sha512KvWrEntryStableWhileBusy_A: assert property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      $past(~`SHA512_PATH.ready_reg || ~`SHA512_PATH.kv_dest_ready || `SHA512_PATH.gen_hash_ip) &&
      (~`SHA512_PATH.ready_reg || ~`SHA512_PATH.kv_dest_ready || `SHA512_PATH.gen_hash_ip) |->
      $stable(`SHA512_PATH.kv_write_ctrl_reg.write_entry))
  else $display("SVA ERROR: SHA512 KV write_entry changed while engine busy");

  // What: SHA512 KV WR_CTRL write_en must not be SW-re-enabled while busy
  // Note: write_en.hwclr = ~kv_dest_ready legitimately clears 1→0; only 0→1 is an attack
  Sha512KvWrEnNoRiseWhileBusy_A: assert property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      $past(~`SHA512_PATH.ready_reg || ~`SHA512_PATH.kv_dest_ready || `SHA512_PATH.gen_hash_ip) &&
      (~`SHA512_PATH.ready_reg || ~`SHA512_PATH.kv_dest_ready || `SHA512_PATH.gen_hash_ip) |->
      !$rose(`SHA512_PATH.kv_write_ctrl_reg.write_en))
  else $display("SVA ERROR: SHA512 KV write_en rose while engine busy");

  // ===========================================================================
  // KV Read Client Error Code Priority Assertion
  // Verify that kv_read_client captures read_allow failures immediately,
  // even when the error_code already holds a value from a previous beat.
  // ===========================================================================

  // What: When validated_read_en fires with read_allow=0, error_code must be KV_READ_FAIL next cycle
  // Why: Ensures the priority fix in kv_read_client.sv catches access violations immediately
  // Timing: 1 cycle (error_code is registered)
  // NOTE: Check HMAC key read client (representative of all kv_read_client instances)
  // NOTE: Use literal 8'h01 instead of kv_defines_pkg::KV_READ_FAIL to avoid RTL/TB enum scope mismatch
  HmacKvReadAllowErrorCapture_A: assert property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      (`HMAC_PATH.hmac_key_kv_read.kv_read_rules.read_en_o &&
       ~`HMAC_PATH.hmac_key_kv_read.kv_read_rules.read_allow) |=>
      (`HMAC_PATH.hmac_key_kv_read.error_code == 8'h01))
  else $display("SVA ERROR: HMAC KV read_allow=0 did not produce KV_READ_FAIL on next cycle");

  // ===========================================================================
  // KV SWWE Lock Cover Properties
  // Verify that the SWWE lock scenarios are exercised in simulation.
  // ===========================================================================

  // Cover: HMAC KV WR_CTRL write attempted while busy
  HmacKvWrCtrlWriteWhileBusy_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `HMAC_PATH.busy_o && `HMAC_REG_PATH.decoded_reg_strb.HMAC512_KV_WR_CTRL);

  // Cover: ECC KV WR_PKEY_CTRL write attempted while busy
  EccKvWrCtrlWriteWhileBusy_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `ECC_PATH.busy_o && `ECC_REG_PATH.decoded_reg_strb.ecc_kv_wr_pkey_ctrl);

  // Cover: AES KV WR_CTRL write attempted while busy
  AesKvWrCtrlWriteWhileBusy_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `AES_CLP_PATH.busy_o && `AES_CLP_PATH.aes_clp_reg_inst.decoded_reg_strb.AES_KV_WR_CTRL);

  // Cover: HMAC KV read_allow failure captured
  HmacKvReadAllowFailure_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `HMAC_PATH.hmac_key_kv_read.kv_read_rules.read_en_o &&
      ~`HMAC_PATH.hmac_key_kv_read.kv_read_rules.read_allow);

  // -----------------------------------------------------------------
  // KV key-length-mismatch (per-consumer, per RFC)
  // -----------------------------------------------------------------
  // The stored last_dword captured inside kv_read_client must equal the
  // entry's stored last_dword whenever the read completes without error.
  `CALIPTRA_ASSERT(KV_hmac_stored_len_matches_entry,
      $rose(`HMAC_PATH.kv_key_done) && (`HMAC_PATH.kv_key_error == 0) |->
      (`HMAC_PATH.hmac_key_kv_read.stored_last_dword ==
       `KEYVAULT_PATH.kv_reg1.hwif_out.KEY_CTRL[`HMAC_PATH.kv_read[0].read_entry].last_dword.value),
      `SVA_RDC_CLK, ~`SVA_RST)

  // HMAC key path uses relaxed (entry-too-small) check: mismatch fires only
  // when the stored entry is smaller than what the mode requires.
  `CALIPTRA_ASSERT(KV_hmac_len_mismatch_iff_mode_differs,
      `HMAC_PATH.hmac_key_kv_read.length_mismatch |->
      `HMAC_PATH.kv_key_data_present &&
      (`HMAC_PATH.init_reg || `HMAC_PATH.next_reg) &&
      (`HMAC_PATH.hmac_key_kv_read.stored_last_dword < `HMAC_PATH.hmac_expected_key_size),
      `SVA_RDC_CLK, ~`SVA_RST)

  // When mismatch fires, key regs clear via hwclr with a fixed 2-cycle
  // pipeline (mismatch cycle N → error_code registers cycle N+1 →
  // hwclr cycle N+1 → key_reg zero cycle N+2).
  // Note: expressed via $past(..., 2) instead of `|-> ##2` because Verilator
  // does not support "implication with sequence expression" on the RHS.
  // Logically equivalent: if length_mismatch fired 2 cycles ago, the key
  // register must be zero now.
  `CALIPTRA_ASSERT(KV_hmac_key_cleared_on_mismatch,
      $past(`HMAC_PATH.hmac_key_kv_read.length_mismatch, 2) |-> (`HMAC_PATH.key_reg == '0),
      `SVA_RDC_CLK, ~`SVA_RST)

  `CALIPTRA_ASSERT(KV_ecc_len_mismatch_clears_privkey,
      $past(`ECC_PATH.ecc_privkey_kv_read.length_mismatch, 2) |-> (`ECC_PATH.privkey_reg == '0),
      `SVA_RDC_CLK, ~`SVA_RST)

  `CALIPTRA_ASSERT(KV_ecc_len_mismatch_clears_seed,
      $past(`ECC_PATH.ecc_seed_kv_read.length_mismatch, 2) |-> (`ECC_PATH.seed_reg == '0),
      `SVA_RDC_CLK, ~`SVA_RST)

  // Covers: each consumer exercises both match and mismatch.
  KV_hmac_len_match_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      (`HMAC_PATH.init_reg || `HMAC_PATH.next_reg) && `HMAC_PATH.kv_key_data_present && !`HMAC_PATH.hmac_key_kv_read.length_mismatch);
  KV_hmac_len_mismatch_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `HMAC_PATH.hmac_key_kv_read.length_mismatch);
  KV_ecc_privkey_len_match_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      |`ECC_PATH.cmd_reg && `ECC_PATH.kv_key_data_present && !`ECC_PATH.ecc_privkey_kv_read.length_mismatch);
  KV_ecc_privkey_len_mismatch_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `ECC_PATH.ecc_privkey_kv_read.length_mismatch);
  KV_ecc_seed_len_match_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      |`ECC_PATH.cmd_reg && `ECC_PATH.kv_seed_data_present && !`ECC_PATH.ecc_seed_kv_read.length_mismatch);
  KV_ecc_seed_len_mismatch_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `ECC_PATH.ecc_seed_kv_read.length_mismatch);

  // AES key path — length check deferred to key-use (LEN_CHECK_AT_KEY_USE=1).
  // check_key_size pulses on kv_key_done | keymgr_key.valid.
  KV_aes_len_match_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `CPTRA_TOP_PATH.aes_inst.aes_key_kv_read.check_key_size &&
      !`CPTRA_TOP_PATH.aes_inst.aes_key_kv_read.length_mismatch);
  KV_aes_len_mismatch_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `CPTRA_TOP_PATH.aes_inst.aes_key_kv_read.length_mismatch);

  // MLDSA seed path
  KV_mldsa_seed_len_match_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `ABR_PATH.kv_mldsa_seed_read_inst.read_done &&
      !`ABR_PATH.kv_mldsa_seed_read_inst.length_mismatch);
  KV_mldsa_seed_len_mismatch_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `ABR_PATH.kv_mldsa_seed_read_inst.length_mismatch);

  // MLKEM seed path
  KV_mlkem_seed_len_match_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `ABR_PATH.kv_mlkem_seed_read_inst.read_done &&
      !`ABR_PATH.kv_mlkem_seed_read_inst.length_mismatch);
  KV_mlkem_seed_len_mismatch_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `ABR_PATH.kv_mlkem_seed_read_inst.length_mismatch);

  // MLKEM msg path
  KV_mlkem_msg_len_match_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `ABR_PATH.kv_mlkem_msg_read_inst.read_done &&
      !`ABR_PATH.kv_mlkem_msg_read_inst.length_mismatch);
  KV_mlkem_msg_len_mismatch_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `ABR_PATH.kv_mlkem_msg_read_inst.length_mismatch);

  // DMA key-release path (MEK)
  KV_dma_len_match_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `AXI_DMA_CTRL_PATH.dma_data_kv_read.read_done &&
      !`AXI_DMA_CTRL_PATH.dma_data_kv_read.length_mismatch);
  KV_dma_len_mismatch_C: cover property (
      @(posedge `SVA_RDC_CLK) disable iff (~`SVA_RST)
      `AXI_DMA_CTRL_PATH.dma_data_kv_read.length_mismatch);

endmodule
