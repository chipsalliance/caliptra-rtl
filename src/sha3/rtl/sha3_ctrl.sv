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
// sha3_ctrl.sv
// --------
// Wrapper for instantiation sha3 engine
//
// 
// 
//======================================================================

module sha3_ctrl
  import sha3_param_pkg::*;
  import sha3_reg_pkg::*;
  import kmac_pkg::*;
#(
  parameter AHB_DATA_WIDTH = 32,
  parameter AHB_ADDR_WIDTH = 32
) (
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

  output logic busy_o,

  output logic error_intr,
  output logic notif_intr,
  input  logic debugUnlock_or_scan_mode_switch
);

caliptra_tlul_pkg::tl_h2d_t adapter_to_kmac_tl;
caliptra_tlul_pkg::tl_d2h_t kmac_to_adapter_tl;

logic ahb_dv;
logic ahb_hold;
logic ahb_write;
logic ahb_err;
logic  [AHB_ADDR_WIDTH-1 : 0] ahb_addr;
logic  [31 : 0] ahb_wdata;
logic  [31 : 0] ahb_rdata;
logic  [2 : 0] ahb_size;
logic  [3 : 0] ahb_wstrb;

logic clp_reg_dv;
logic clp_reg_write;
logic [31 : 0] clp_reg_rdata;
logic [31 : 0] clp_reg_wdata;
logic [caliptra_tlul_pkg::TL_AW-1 : 0] clp_reg_addr;

sha3_reg__in_t hwif_in;
sha3_reg__out_t hwif_out;

caliptra_prim_mubi_pkg::mubi4_t sha_idle;

logic intr_kmac_done, intr_kmac_done_reg, intr_kmac_done_edge;
logic intr_fifo_empty, intr_fifo_empty_reg, intr_fifo_empty_edge;
logic intr_kmac_err, intr_kmac_err_reg, intr_kmac_err_edge;

assign busy_o = caliptra_prim_mubi_pkg::mubi4_test_false_loose(sha_idle);

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

// This is a workaround. A cleaner solution is tracked in issue #914 to integrate this functionality into ahb_slv_sif:
// https://github.com/chipsalliance/caliptra-rtl/issues/914
always_ff @(posedge clk or negedge reset_n) begin
  if(!reset_n) begin
    ahb_size <= '0;
  end else begin
    if(hready_i & hsel_i) begin
      ahb_size <= hsize_i;
    end
  end
end

always_comb begin
  unique case (ahb_size)
    'h0: begin
      ahb_wstrb = 1 << ahb_addr[1:0];
    end
    'h1: begin
      ahb_wstrb = ahb_addr[1] ? 4'b1100 : 4'b0011;
    end
    'h2: begin
      ahb_wstrb = 4'b1111;
    end
    default: begin
      ahb_wstrb = 4'b0000;
    end
  endcase
end

//TLUL Adapter
caliptra_tlul_adapter_vh
#(
  .VH_REGISTER_ADDRESS_OFFSET(32'h0000_1000)
)
caliptra_tlul_adapter_vh_inst
(
  .clk_i(clk),
  .rst_ni(reset_n),

  .tl_o(adapter_to_kmac_tl),
  .tl_i(kmac_to_adapter_tl),

  // Valid-Hold device interface (VH to TLUL).
  .dv_i(ahb_dv),
  .hld_o(ahb_hold),
  .addr_i({ {caliptra_tlul_pkg::TL_AW-AHB_ADDR_WIDTH{1'b0}}, ahb_addr }),
  .write_i(ahb_write),
  .wdata_i(ahb_wdata),
  .wstrb_i(ahb_wstrb),
  .size_i(ahb_size),
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
sha3_reg sha_reg_inst (
  .clk(clk),
  .rst(1'b0),

  .s_cpuif_req         (clp_reg_dv),
  .s_cpuif_req_is_wr   (clp_reg_write),
  .s_cpuif_addr        (clp_reg_addr[SHA3_REG_MIN_ADDR_WIDTH-1:0]),
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

kmac
#(
  .EnMasking                      (0),
  .EnFullKmac                     (0),
  .SwKeyMasked                    (0),
  .NumAppIntf                     (2),
  .AppCfg                         ('{AppCfgKeyMgrStripped, AppCfgKeyMgrStripped})
)
u_sha_inst (
  .clk_i                          (clk),
  .rst_ni                         (reset_n),
  .rst_shadowed_ni                (reset_n),

  .clk_edn_i                      (1'b0),
  .rst_edn_ni                     (1'b1),

  // Bus interface
  .tl_i                           (adapter_to_kmac_tl),
  .tl_o                           (kmac_to_adapter_tl),

  // Alerts
  .alert_rx_i                     ('0),
  .alert_tx_o                     (),

  // KeyMgr sideload (secret key) interface
  .keymgr_key_i                   ('0),

  // KeyMgr KDF data path
  .app_i                          ('0),
  .app_o                          (),

  // EDN interface
  .entropy_o                      (),
  .entropy_i                      ('0),

  // Life cycle
  .lc_escalate_en_i               (lc_ctrl_pkg::Off),

  // interrupts
  .intr_kmac_done_o               (intr_kmac_done),
  .intr_fifo_empty_o              (intr_fifo_empty),
  .intr_kmac_err_o                (intr_kmac_err),

  // parameter consistency check with keymgr
  .en_masking_o                   (),

  // Idle signal
  .idle_o                         (sha_idle)
);

always_comb begin
  hwif_in.error_reset_b = cptra_pwrgood;
  hwif_in.reset_b = reset_n;
  hwif_in.SHA3_NAME[0].NAME.next = SHA3_CORE_NAME[31:0];
  hwif_in.SHA3_NAME[1].NAME.next = SHA3_CORE_NAME[63:32];
  hwif_in.SHA3_VERSION[0].VERSION.next = SHA3_CORE_VERSION[31:0];
  hwif_in.SHA3_VERSION[1].VERSION.next = SHA3_CORE_VERSION[63:32];

  // Duplicates of regs in top_reg are tied to 0.
  hwif_in.STATUS = '{default: '0};
  hwif_in.STATE = '{default: '0};
  hwif_in.MSG_FIFO = '{default: '0};
  hwif_in.ERR_CODE.ERR_CODE.next = '0;
  hwif_in.CFG_SHADOWED = '{default: '0};
  hwif_in.CFG_REGWEN.en.next = 1'b0;
end

// Detect edges for interrupts and errors.
always_ff @(posedge clk or negedge reset_n) 
begin : error_interrupt_detection
    if(!reset_n) begin
      intr_kmac_err_reg   <= 1'b0;
      intr_kmac_done_reg  <= 1'b0;
      intr_fifo_empty_reg <= 1'b0;
    end
    else begin
      intr_kmac_err_reg   <= intr_kmac_err;
      intr_kmac_done_reg  <= intr_kmac_done;
      intr_fifo_empty_reg <= intr_fifo_empty;
    end
end // error_interrupt_detection

// Error/Interrupt edge detection signals.
always_comb intr_kmac_err_edge = intr_kmac_err & (!intr_kmac_err_reg);
always_comb intr_kmac_done_edge = intr_kmac_done & (!intr_kmac_done_reg);
always_comb intr_fifo_empty_edge = intr_fifo_empty & (!intr_fifo_empty_reg);

// Assign error/interrupt signals
assign hwif_in.intr_block_rf.error_internal_intr_r.sha3_error_sts.hwset = intr_kmac_err_edge;
assign hwif_in.intr_block_rf.error_internal_intr_r.error1_sts.hwset = 1'b0;
assign hwif_in.intr_block_rf.error_internal_intr_r.error2_sts.hwset = 1'b0;
assign hwif_in.intr_block_rf.error_internal_intr_r.error3_sts.hwset = 1'b0;
assign hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = intr_kmac_done_edge;
assign hwif_in.intr_block_rf.notif_internal_intr_r.notif_msg_fifo_empty_sts.hwset = intr_fifo_empty_edge;

assign error_intr = hwif_out.intr_block_rf.error_global_intr_r.intr;
assign notif_intr = hwif_out.intr_block_rf.notif_global_intr_r.intr;

endmodule
