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
//


module lc_ctrl_top 
    import lc_ctrl_pkg::*;
    import lc_ctrl_reg_pkg::*;
    import lc_ctrl_state_pkg::*;
    import axi_pkg::*;
#(
    // Enable asynchronous transitions on alerts.
    parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
    // Hardware revision numbers exposed in the CSRs.
    parameter logic [SiliconCreatorIdWidth-1:0] SiliconCreatorId = '0,
    parameter logic [ProductIdWidth-1:0]        ProductId        = '0,
    parameter logic [RevisionIdWidth-1:0]       RevisionId       = '0,
    // Idcode value for the JTAG.
    parameter logic [31:0] IdcodeValue = 32'h00000001,
    // Random netlist constants
    parameter lc_keymgr_div_t RndCnstLcKeymgrDivInvalid      = LcKeymgrDivWidth'(0),
    parameter lc_keymgr_div_t RndCnstLcKeymgrDivTestUnlocked = LcKeymgrDivWidth'(1),
    parameter lc_keymgr_div_t RndCnstLcKeymgrDivDev          = LcKeymgrDivWidth'(2),
    parameter lc_keymgr_div_t RndCnstLcKeymgrDivProduction   = LcKeymgrDivWidth'(3),
    parameter lc_keymgr_div_t RndCnstLcKeymgrDivRma          = LcKeymgrDivWidth'(4),
    parameter lc_token_mux_t  RndCnstInvalidTokens           = {TokenMuxBits{1'b1}},
    parameter bit             SecVolatileRawUnlockEn         = 0
) (
    // Life cycle controller clock
    input                                              clk_i,
    input                                              rst_ni,
    // Clock for KMAC interface
    input                                              clk_kmac_i,
    input                                              rst_kmac_ni,
    // AXI interface (device)
    axi_if.w_sub                                       s_lc_axi_w_if,
    axi_if.r_sub                                       s_lc_axi_r_if,

    // JTAG TAP.
    input  jtag_pkg::jtag_req_t                        jtag_i,
    output jtag_pkg::jtag_rsp_t                        jtag_o,
    // This bypasses the clock inverter inside the JTAG TAP for scanmmode.
    input                                              scan_rst_ni,
    input  caliptra_prim_mubi_pkg::mubi4_t                      scanmode_i,
    // Alert outputs.
    input  caliptra_prim_alert_pkg::alert_rx_t [NumAlerts-1:0]  alert_rx_i,
    output caliptra_prim_alert_pkg::alert_tx_t [NumAlerts-1:0]  alert_tx_o,
    // Escalation inputs (severity 1 and 2).
    // These need not be synchronized since the alert handler is
    // in the same clock domain as the LC controller.
    input  caliptra_prim_esc_pkg::esc_rx_t                      esc_scrap_state0_tx_i,
    output caliptra_prim_esc_pkg::esc_tx_t                      esc_scrap_state0_rx_o,
    input  caliptra_prim_esc_pkg::esc_rx_t                      esc_scrap_state1_tx_i,
    output caliptra_prim_esc_pkg::esc_tx_t                      esc_scrap_state1_rx_o,
    // Power manager interface (inputs are synced to lifecycle clock domain).
    input  pwrmgr_pkg::pwr_lc_req_t                    pwr_lc_i,
    output pwrmgr_pkg::pwr_lc_rsp_t                    pwr_lc_o,
    // Strap sampling override that is only used when SecVolatileRawUnlockEn = 1,
    // Otherwise this output is tied off to 0.
    output logic                                       strap_en_override_o,
    // Strap override - this is only used when
    // Macro-specific test registers going to lifecycle TAP
    output caliptra_otp_ctrl_pkg::lc_otp_vendor_test_req_t      lc_otp_vendor_test_o,
    input  caliptra_otp_ctrl_pkg::lc_otp_vendor_test_rsp_t      lc_otp_vendor_test_i,
    // Life cycle transition command interface.
    // No sync required since LC and OTP are in the same clock domain.
    output caliptra_otp_ctrl_pkg::lc_otp_program_req_t          lc_otp_program_o,
    input  caliptra_otp_ctrl_pkg::lc_otp_program_rsp_t          lc_otp_program_i,
    // Life cycle hashing interface for raw unlock
    // Synchronized in the life cycle controller.
    // SEC_CM: TOKEN.DIGEST
    input  kmac_pkg::app_rsp_t                         kmac_data_i,
    output kmac_pkg::app_req_t                         kmac_data_o,
    // OTP broadcast outputs
    // No sync required since LC and OTP are in the same clock domain.
    // SEC_CM: TOKEN_VALID.CTRL.MUBI
    input  caliptra_otp_ctrl_pkg::otp_lc_data_t                 otp_lc_data_i,
    // Life cycle broadcast outputs (all of them are registered).
    // SEC_CM: INTERSIG.MUBI
    output lc_tx_t                                     lc_dft_en_o,
    output lc_tx_t                                     lc_nvm_debug_en_o,
    output lc_tx_t                                     lc_hw_debug_en_o,
    output lc_tx_t                                     lc_cpu_en_o,
    output lc_tx_t                                     lc_creator_seed_sw_rw_en_o,
    output lc_tx_t                                     lc_owner_seed_sw_rw_en_o,
    output lc_tx_t                                     lc_iso_part_sw_rd_en_o,
    output lc_tx_t                                     lc_iso_part_sw_wr_en_o,
    output lc_tx_t                                     lc_seed_hw_rd_en_o,
    output lc_tx_t                                     lc_keymgr_en_o,
    output lc_tx_t                                     lc_escalate_en_o,
    output lc_tx_t                                     lc_check_byp_en_o,
    // Request and feedback to/from clock manager and AST.
    // The ack is synced to the lc clock domain using prim_lc_sync.
    // SEC_CM: INTERSIG.MUBI
    output lc_tx_t                                     lc_clk_byp_req_o,
    input  lc_tx_t                                     lc_clk_byp_ack_i,
    // Request and feedback to/from flash controller.
    // The ack is synced to the lc clock domain using prim_lc_sync.
    output lc_flash_rma_seed_t                         lc_flash_rma_seed_o,
    // SEC_CM: INTERSIG.MUBI
    output lc_tx_t                                     lc_flash_rma_req_o,
    input  lc_tx_t [NumRmaAckSigs-1:0]                 lc_flash_rma_ack_i,
    // State group dive32rsification value for keymgr.
    output lc_keymgr_div_t                             lc_keymgr_div_o,
    // Hardware config input, needed for the DEVICE_ID field.
    input  caliptra_otp_ctrl_pkg::otp_device_id_t               otp_device_id_i,
    // Hardware config input, needed for the MANUF_STATE field.
    input  caliptra_otp_ctrl_pkg::otp_device_id_t               otp_manuf_state_i,
    // Hardware revision output (static)
    output lc_hw_rev_t                                 hw_rev_o
);

    // AXI2TLUL interface signals
    tlul_pkg::tl_h2d_t      tl_i;
    tlul_pkg::tl_d2h_t      tl_o;

    // AXI2TLUL instance
    axi2tlul #(
        .AW     (32),
        .DW     (32),
        .UW     (32),
        .IW     (1 )
    ) u_lc_axi2tlul (
        .clk            (clk_i),
        .rst_n          (rst_ni),
        .s_axi_w_if     (s_lc_axi_w_if),
        .s_axi_r_if     (s_lc_axi_r_if),
        .tl_o           (tl_i),
        .tl_i           (tl_o)
    );

    // LC CTRL instance
    lc_ctrl #(
        .AlertAsyncOn	                (   AlertAsyncOn                    ),
        .SiliconCreatorId	            (   SiliconCreatorId                ),
        .ProductId	                    (   ProductId                       ),
        .RevisionId	                    (   RevisionId                      ),
        .IdcodeValue	                (   IdcodeValue                     ),
        .RndCnstLcKeymgrDivInvalid	    (   RndCnstLcKeymgrDivInvalid       ),
        .RndCnstLcKeymgrDivTestUnlocked	(   RndCnstLcKeymgrDivTestUnlocked  ),
        .RndCnstLcKeymgrDivDev	        (   RndCnstLcKeymgrDivDev           ),
        .RndCnstLcKeymgrDivProduction	(   RndCnstLcKeymgrDivProduction    ),
        .RndCnstLcKeymgrDivRma	        (   RndCnstLcKeymgrDivRma           ),
        .RndCnstInvalidTokens	        (   RndCnstInvalidTokens            ),
        .SecVolatileRawUnlockEn	        (   SecVolatileRawUnlockEn          )
    ) u_lc_ctrl (
        // Life cycle controller clock
        .clk_i,
        .rst_ni,
        // Clock for KMAC interface
        .clk_kmac_i,
        .rst_kmac_ni,
        // Bus Interface (device)
        .tl_i,
        .tl_o,
        // JTAG TAP.
        .jtag_i,
        .jtag_o,
        // This bypasses the clock inverter inside the JTAG TAP for scanmmode.
        .scan_rst_ni,
        .scanmode_i,
        // Alert outputs.
        .alert_rx_i,
        .alert_tx_o,
        // Escalation inputs (severity 1 and 2).
        // These need not be synchronized since the alert handler is
        // in the same clock domain as the LC controller.
        .esc_scrap_state0_tx_i,
        .esc_scrap_state0_rx_o,
        .esc_scrap_state1_tx_i,
        .esc_scrap_state1_rx_o,
        // Power manager interface (inputs are synced to lifecycle clock domain).
        .pwr_lc_i,
        .pwr_lc_o,
        // Strap sampling override that is only used when SecVolatileRawUnlockEn = 1,
        // Otherwise this is tied off to 0.
        .strap_en_override_o,
        // Strap override - this is only used when
        // Macro-specific test registers going to lifecycle TAP
        .lc_otp_vendor_test_o,
        .lc_otp_vendor_test_i,
        // Life cycle transition command interface.
        // No sync required since LC and OTP are in the same clock domain.
        .lc_otp_program_o,
        .lc_otp_program_i,
        // Life cycle hashing interface for raw unlock
        // Synchronized in the life cycle controller.
        // SEC_CM: TOKEN.DIGEST
        .kmac_data_i,
        .kmac_data_o,
        // OTP broadcast outputs
        // No sync required since LC and OTP are in the same clock domain.
        // SEC_CM: TOKEN_VALID.CTRL.MUBI
        .otp_lc_data_i,
        // Life cycle broadcast outputs (all of them are registered).
        // SEC_CM: INTERSIG.MUBI
        .lc_dft_en_o,
        .lc_nvm_debug_en_o,
        .lc_hw_debug_en_o,
        .lc_cpu_en_o,
        .lc_creator_seed_sw_rw_en_o,
        .lc_owner_seed_sw_rw_en_o,
        .lc_iso_part_sw_rd_en_o,
        .lc_iso_part_sw_wr_en_o,
        .lc_seed_hw_rd_en_o,
        .lc_keymgr_en_o,
        .lc_escalate_en_o,
        .lc_check_byp_en_o,
        // Request and feedback to/from clock manager and AST.
        // The ack is synced to the lc clock domain using prim_lc_sync.
        // SEC_CM: INTERSIG.MUBI
        .lc_clk_byp_req_o,
        .lc_clk_byp_ack_i,
        // Request and feedback to/from flash controller.
        // The ack is synced to the lc clock domain using prim_lc_sync.
        .lc_flash_rma_seed_o,
        // SEC_CM: INTERSIG.MUBI
        .lc_flash_rma_req_o,
        .lc_flash_rma_ack_i,
        // State group diversification value for keymgr.
        .lc_keymgr_div_o,
        // Hardware config input, needed for the DEVICE_ID field.
        .otp_device_id_i,
        // Hardware config input, needed for the MANUF_STATE field.
        .otp_manuf_state_i,
        // Hardware revision (static)
        .hw_rev_o
    );

endmodule : lc_ctrl_top