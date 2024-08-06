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


module otp_ctrl_top
    import axi_pkg::*;
    (
        input clk_i,
        input rst_ni, 

        //AXI Interface Core
        axi_if.w_sub s_core_axi_w_if,
        axi_if.r_sub s_core_axi_r_if,

        //AXI Interface Prim
        axi_if.w_sub s_prim_axi_w_if,
        axi_if.r_sub s_prim_axi_r_if,

        // Interrupt Requests
        output logic                                       intr_otp_operation_done_o,
        output logic                                       intr_otp_error_o,
        // Alerts
        input  caliptra_prim_alert_pkg::alert_rx_t [NumAlerts-1:0]  alert_rx_i,
        output caliptra_prim_alert_pkg::alert_tx_t [NumAlerts-1:0]  alert_tx_o,
        // Observability to AST
        input ast_pkg::ast_obs_ctrl_t                      obs_ctrl_i,
        output logic [7:0]                                 otp_obs_o,
        // Macro-specific power sequencing signals to/from AST.
        output otp_ast_req_t                               otp_ast_pwr_seq_o,
        input  otp_ast_rsp_t                               otp_ast_pwr_seq_h_i,
        // Power manager interface (inputs are synced to OTP clock domain)
        input  pwrmgr_pkg::pwr_otp_req_t                   pwr_otp_i,
        output pwrmgr_pkg::pwr_otp_rsp_t                   pwr_otp_o,
        // Macro-specific test registers going to lifecycle TAP
        input  lc_otp_vendor_test_req_t                    lc_otp_vendor_test_i,
        output lc_otp_vendor_test_rsp_t                    lc_otp_vendor_test_o,
        // Lifecycle transition command interface
        input  lc_otp_program_req_t                        lc_otp_program_i,
        output lc_otp_program_rsp_t                        lc_otp_program_o,
        // Lifecycle broadcast inputs
        // SEC_CM: LC_CTRL.INTERSIG.MUBI
        input  lc_ctrl_pkg::lc_tx_t                        lc_creator_seed_sw_rw_en_i,
        input  lc_ctrl_pkg::lc_tx_t                        lc_owner_seed_sw_rw_en_i,
        input  lc_ctrl_pkg::lc_tx_t                        lc_seed_hw_rd_en_i,
        input  lc_ctrl_pkg::lc_tx_t                        lc_dft_en_i,
        input  lc_ctrl_pkg::lc_tx_t                        lc_escalate_en_i,
        input  lc_ctrl_pkg::lc_tx_t                        lc_check_byp_en_i,
        // OTP broadcast outputs
        // SEC_CM: TOKEN_VALID.CTRL.MUBI
        output otp_lc_data_t                               otp_lc_data_o,
        output otp_keymgr_key_t                            otp_keymgr_key_o,
        // Scrambling key requests
        input  flash_otp_key_req_t                         flash_otp_key_i,
        output flash_otp_key_rsp_t                         flash_otp_key_o,
        input  sram_otp_key_req_t [NumSramKeyReqSlots-1:0] sram_otp_key_i,
        output sram_otp_key_rsp_t [NumSramKeyReqSlots-1:0] sram_otp_key_o,
        input  otbn_otp_key_req_t                          otbn_otp_key_i,
        output otbn_otp_key_rsp_t                          otbn_otp_key_o,
        // Hardware config bits
        output otp_broadcast_t                             otp_broadcast_o,
        // External voltage for OTP
        inout wire                                         otp_ext_voltage_h_io,
        // Scan
        input                                              scan_en_i,
        input                                              scan_rst_ni,
        input prim_mubi_pkg::mubi4_t                       scanmode_i,
        // Test-related GPIO output
        output logic [OtpTestVectWidth-1:0]                cio_test_o,
        output logic [OtpTestVectWidth-1:0]                cio_test_en_o

    );

    logic           core_dv;
    logic [AW-1:0]  core_addr;
    logic           core_write;
    logic [UW-1:0]  core_user;
    logic [IW-1:0]  core_id;
    logic [DW-1:0]  core_wdata;
    logic [BC-1:0]  core_wstrb;
    logic [DW-1:0]  core_rdata;
    logic           core_last;
    logic           core_hld;
    logic           core_err;

    logic           prim_dv;
    logic [AW-1:0]  prim_addr;
    logic           prim_write;
    logic [UW-1:0]  prim_user;
    logic [IW-1:0]  prim_id;
    logic [DW-1:0]  prim_wdata;
    logic [BC-1:0]  prim_wstrb;
    logic [DW-1:0]  prim_rdata;
    logic           prim_last;
    logic           prim_hld;
    logic           prim_err;


    // Core AXI sub instance
    axi_sub core_axi_sub #(

    ) (
        .clk            (clk_i),
        .rst_n          (rst_ni), 
        .s_axi_w_if     (s_core_axi_w_if),
        .s_axi_r_if     (s_core_axi_r_if),
        .dv             (core_dv),
        .addr           (core_addr),
        .write          (core_user),
        .id             (core_id),
        .wdata          (core_wdata),
        .rdata          (core_rdata),
        .last           (core_last),
        .hld            (core_hld),
        .err            (core_err)
    );
    
    // Prim AXI sub instance
    axi_sub prim_axi_sub #(

    ) (
        .clk            (clk_i),
        .rst_n          (rst_ni), 
        .s_axi_w_if     (s_prim_axi_w_if),
        .s_axi_r_if     (s_prim_axi_r_if),
        .dv             (prim_dv),
        .addr           (prim_addr),
        .write          (prim_user),
        .id             (prim_id),
        .wdata          (prim_wdata),
        .rdata          (prim_rdata),
        .last           (prim_last),
        .hld            (prim_hld),
        .err            (prim_err)
    );

    //  OTP Ctrl instance
    otp_ctrl otp_ctrl #( 
        
    ) (
        .clk_i,
        .rst_ni,
        .clk_edn_i,
        .rst_edn_ni,
        .edn_o, 
        .edn_i,
        .core_dv        (core_dv),
        .core_addr      (core_addr),
        .core_write     (core_write),
        .core_wstrb     (core_wstrb),
        .core_id        (core_id),
        .core_wdata     (core_wdata),
        .core_rdata     (core_rdata),
        .core_last      (core_last),
        .core_hld       (core_hld),
        .core_err       (core_err),
        .prim_dv        (prim_dv),
        .prim_addr      (prim_addr),
        .prim_write     (prim_write),
        .prim_wstrb     (prim_wstrb),
        .prim_id        (prim_id),
        .prim_wdata     (prim_wdata),
        .prim_rdata     (prim_rdata),
        .prim_last      (prim_last),
        .prim_hld       (prim_hld),
        .prim_err       (prim_err),
        .intr_otp_operation_done_o,
        .intr_otp_error_o,
        .alert_rx_i,
        .alert_rx_o,
        .obs_ctrl_i,
        .otp_obs_o,
        .otp_ast_pwr_seq_o,
        .otp_ast_pwr_seq_h_i,
        .pwr_otp_i,
        .pwr_otp_o,
        .lc_otp_vendor_test_i,
        .lc_otp_vendor_test_o,
        .lc_otp_program_i,
        .lc_otp_program_o,
        .lc_creator_seed_sw_rw_en_i,
        .lc_owner_seed_sw_rw_en_i,
        .lc_seed_hw_rd_en_i,
        .lc_dft_en_i,
        .lc_escalate_en_i,
        .lc_check_byp_en_i,
        .otp_lc_data_o,
        .otp_keymgr_key_o,
        .flash_otp_key_i (),
        .flash_otp_key_o (),
        .sram_otp_key_i (),
        .sram_otp_key_o (),
        .otbn_otp_key_i (),
        .otbn_otp_key_o (),
        .otp_broadcast_o,
        .otp_ext_voltage_h_io,
        .scan_en_i,
        .scan_rst_ni,
        .scanmode_i,
        .cio_test_o,
        .cio_test_en_o
    );

endmodule
