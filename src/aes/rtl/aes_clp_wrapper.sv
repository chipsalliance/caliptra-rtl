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
//======================================================================
//
// aes_clp_wrapper.sv
// --------
// Wrapper for instantiation aes engine
//
// 
// 
//======================================================================

module aes_clp_wrapper
  import kv_defines_pkg::*;
  import aes_clp_reg_pkg::*;
  #(
  parameter AHB_DATA_WIDTH = 32,
  parameter AHB_ADDR_WIDTH = 32
)
(
  // Clock and reset.
  input wire           clk,
  input wire           reset_n,
  input wire           cptra_pwrgood,

  input logic [AHB_ADDR_WIDTH-1:0] haddr_i,
  input logic [AHB_DATA_WIDTH-1:0] hwdata_i,
  input logic hsel_i,
  input logic hwrite_i,
  input logic hready_i,
  input logic [1:0] htrans_i,
  input logic [2:0] hsize_i,

  output logic hresp_o,
  output logic hreadyout_o,
  output logic [AHB_DATA_WIDTH-1:0] hrdata_o,
  
  // kv interface
  output kv_read_t kv_read,
  input kv_rd_resp_t kv_rd_resp,

  output logic busy_o,

  // Interrupt
  output logic error_intr,
  output logic notif_intr,
  input  logic debugUnlock_or_scan_mode_switch
);

tlul_pkg::tl_h2d_t adapter_to_aes_tl;
tlul_pkg::tl_d2h_t aes_to_adapter_tl;

logic ahb_dv;
logic ahb_hold;
logic ahb_write;
logic ahb_err;
logic  [AHB_ADDR_WIDTH-1 : 0] ahb_addr;
logic  [31 : 0] ahb_wdata;
logic  [31 : 0] ahb_rdata;

logic clp_reg_dv;
logic clp_reg_write;
logic [31 : 0] clp_reg_rdata;
logic [31 : 0] clp_reg_wdata;
logic [tlul_pkg::TL_AW-1 : 0] clp_reg_addr;

aes_clp_reg_pkg::aes_clp_reg__in_t hwif_in;
aes_clp_reg_pkg::aes_clp_reg__out_t hwif_out;

caliptra_prim_mubi_pkg::mubi4_t aes_idle;

assign busy_o = caliptra_prim_mubi_pkg::mubi4_test_false_loose(aes_idle);

//AHB interface
ahb_slv_sif #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(32)
) ahb_slv_sif_inst
(
    //AMBA AHB Lite INF
    .hclk(clk),
    .hreset_n(reset_n),
    .haddr_i(haddr_i),
    .hwdata_i(hwdata_i),
    .hsel_i(hsel_i),
    .hwrite_i(hwrite_i),
    .hready_i(hready_i),
    .htrans_i(htrans_i),
    .hsize_i(hsize_i),

    .hresp_o(hresp_o),
    .hreadyout_o(hreadyout_o),
    .hrdata_o(hrdata_o),


    //COMPONENT INF
    .dv(ahb_dv),
    .hld(ahb_hold),
    .err(ahb_err),
    .write(ahb_write),
    .wdata(ahb_wdata),
    .addr(ahb_addr),

    .rdata(ahb_rdata)
);

//TLUL Adapter
tlul_adapter_vh
tlul_adapter_vh_inst
(
  .clk_i(clk),
  .rst_ni(reset_n),

  .tl_o(adapter_to_aes_tl),
  .tl_i(aes_to_adapter_tl),

  // Valid-Hold device interface (VH to TLUL).
  .dv_i(ahb_dv),
  .hld_o(ahb_hold),
  .addr_i({ {tlul_pkg::TL_AW-AHB_ADDR_WIDTH{1'b0}}, ahb_addr }),
  .write_i(ahb_write),
  .wdata_i(ahb_wdata),
  .wstrb_i('1),
  .size_i(3'b010),
  .rdata_o(ahb_rdata),
  .error_o(ahb_err),
  .last_i('0),
  .user_i('0),
  .id_i('0),

  // Valid-Hold host interface (VH to internal registers). The signals from the VH device interface
  // are routed to the VH host interface for every internal access, see the `internal_access` signal.
  .int_dv_o(clp_reg_dv),
  .int_hld_i('0),
  .int_addr_o(clp_reg_addr),
  .int_write_o(clp_reg_write),
  .int_wdata_o(clp_reg_wdata),
  .int_wstrb_o(),
  .int_size_o(),
  .int_rdata_i(clp_reg_rdata),
  .int_error_i('0),
  .int_last_o(),
  .int_user_o(),
  .int_id_o()
);

//Internal register block
aes_clp_reg aes_clp_reg_inst (
  .clk(clk),
  .rst(1'b0),

  .s_cpuif_req         (clp_reg_dv),
  .s_cpuif_req_is_wr   (clp_reg_write),
  .s_cpuif_addr        (clp_reg_addr[AES_CLP_REG_MIN_ADDR_WIDTH-1:0]),
  .s_cpuif_wr_data     (clp_reg_wdata),
  .s_cpuif_wr_biten    ('1),
  .s_cpuif_req_stall_wr(),
  .s_cpuif_req_stall_rd(),
  .s_cpuif_rd_ack      (),
  .s_cpuif_rd_err      (),
  .s_cpuif_rd_data     (clp_reg_rdata),
  .s_cpuif_wr_ack      (),
  .s_cpuif_wr_err      (),

  .hwif_in (hwif_in),
  .hwif_out(hwif_out)
);

//AES Engine
aes
aes_inst (
  .clk_i(clk),
  .rst_ni(reset_n),
  .rst_shadowed_ni(reset_n), //FIXME

  .idle_o(aes_idle),

  // Life cycle
  .lc_escalate_en_i(lc_ctrl_pkg::Off),

  // Entropy distribution network (EDN) interface
  .clk_edn_i(clk),
  .rst_edn_ni(reset_n),
  .edn_o(),
  .edn_i('{edn_ack:0, edn_fips:0, edn_bus:'0}), //FIXME

  // Key manager (keymgr) key sideload interface
  .keymgr_key_i('0), //FIXME

  // Bus interface
  .tl_i(adapter_to_aes_tl),
  .tl_o(aes_to_adapter_tl),

  // Alerts
  .alert_rx_i({caliptra_prim_alert_pkg::ALERT_RX_DEFAULT, caliptra_prim_alert_pkg::ALERT_RX_DEFAULT}),
  .alert_tx_o()
);

always_comb begin
  hwif_in.error_reset_b = cptra_pwrgood;
  hwif_in.reset_b =  reset_n;
  hwif_in.AES_NAME[0].NAME.next = '0; //FIXME
  hwif_in.AES_NAME[1].NAME.next = '0; //FIXME
  hwif_in.AES_VERSION[0].VERSION.next = '0; //FIXME
  hwif_in.AES_VERSION[1].VERSION.next = '0; //FIXME

  hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = '0; //FIXME
  hwif_in.intr_block_rf.error_internal_intr_r.error0_sts.hwset = 1'b0; // TODO
  hwif_in.intr_block_rf.error_internal_intr_r.error1_sts.hwset = 1'b0; // TODO
  hwif_in.intr_block_rf.error_internal_intr_r.error2_sts.hwset = 1'b0; // TODO
  hwif_in.intr_block_rf.error_internal_intr_r.error3_sts.hwset = 1'b0; // TODO
end

//keyault FSM

//Drive keymgr interface into AES

endmodule