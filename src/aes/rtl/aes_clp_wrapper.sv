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

`include "caliptra_reg_field_defines.svh"
`include "kv_macros.svh"

module aes_clp_wrapper
  import aes_pkg::*;
  import kv_defines_pkg::*;
  import aes_clp_reg_pkg::*;
  #(
  parameter AHB_DATA_WIDTH = 32,
  parameter AHB_ADDR_WIDTH = 32,
  parameter CIF_DATA_WIDTH = 32,
  localparam CIF_DATA_NUM_BYTES = CIF_DATA_WIDTH / 8
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
  
  // OCP LOCK
  input  logic ocp_lock_in_progress,
  input logic [15:0] key_release_key_size,

  // status signals
  output logic input_ready_o,
  output logic output_valid_o,
  output logic status_idle_o,
    
  // DMA CIF
  input  logic dma_req_dv,
  input  logic dma_req_write,
  input  logic   [AHB_ADDR_WIDTH-1 : 0] dma_req_addr,
  input  logic   [CIF_DATA_WIDTH-1 : 0] dma_req_wdata,
  output logic dma_req_hold,
  output logic dma_req_error,
  output logic   [CIF_DATA_WIDTH-1 : 0] dma_req_rdata,
  
  // kv interface
  output kv_read_t kv_read,
  input kv_rd_resp_t kv_rd_resp,
  output kv_write_t kv_write,
  input kv_wr_resp_t kv_wr_resp,

  output logic busy_o,

  // Interrupt
  output logic error_intr,
  output logic notif_intr,
  input  logic debugUnlock_or_scan_mode_switch
);

localparam AES_KV_KEY_DW_WIDTH = $clog2(keymgr_pkg::KeyWidth/32);

caliptra_tlul_pkg::tl_h2d_t adapter_to_aes_tl;
caliptra_tlul_pkg::tl_d2h_t aes_to_adapter_tl;

logic ahb_dv;
logic ahb_hold;
logic ahb_write;
logic ahb_err;
logic  [AHB_ADDR_WIDTH-1 : 0] ahb_addr;
logic  [CIF_DATA_WIDTH-1 : 0] ahb_wdata;
logic  [CIF_DATA_WIDTH-1 : 0] ahb_rdata;
  
logic req_collision;
logic aes_cif_endian_swap;
  
logic aes_cif_req_dv;
logic aes_cif_req_write;
logic   [AHB_ADDR_WIDTH-1 : 0] aes_cif_req_addr;
logic   [CIF_DATA_WIDTH-1 : 0] aes_cif_req_wdata;
logic   [CIF_DATA_WIDTH-1 : 0] aes_cif_req_wdata_post_endian;
logic aes_cif_req_hold;
logic aes_cif_req_error;
logic   [CIF_DATA_WIDTH-1 : 0] aes_cif_req_rdata;
logic   [CIF_DATA_WIDTH-1 : 0] aes_cif_req_rdata_post_endian;

logic clp_reg_dv;
logic clp_reg_write;
logic [31 : 0] clp_reg_rdata;
logic [31 : 0] clp_reg_wdata;
logic [caliptra_tlul_pkg::TL_AW-1 : 0] clp_reg_addr;

aes_clp_reg_pkg::aes_clp_reg__in_t hwif_in;
aes_clp_reg_pkg::aes_clp_reg__out_t hwif_out;

caliptra2aes_t caliptra2aes;
aes2caliptra_t aes2caliptra;

caliptra_prim_mubi_pkg::mubi4_t aes_idle;

kv_read_ctrl_reg_t kv_key_read_ctrl_reg;
kv_read_filter_metrics_t kv_key_read_metrics;
kv_error_code_e kv_key_error;
logic kv_key_ready, kv_key_done;
logic [KV_ENTRY_ADDR_W-1:0] kv_key_present_slot;

logic kv_key_write_en;
logic [AES_KV_KEY_DW_WIDTH-1:0] kv_key_write_offset;
logic [3:0][7:0] kv_key_write_data;

kv_write_ctrl_reg_t kv_write_ctrl_reg;
kv_write_filter_metrics_t kv_write_metrics;
kv_error_code_e kv_write_error;
logic kv_write_ready;
logic [$clog2(CLP_AES_KV_WR_DW/32):0] kv_wr_num_dwords;

edn_pkg::edn_req_t edn_req;

keymgr_pkg::hw_key_req_t keymgr_key;

assign error_intr = '0; // Unused
assign notif_intr = '0;  // Unused 

assign busy_o = caliptra_prim_mubi_pkg::mubi4_test_false_loose(aes_idle) || ~kv_key_ready || ~kv_write_ready;
assign status_idle_o = caliptra_prim_mubi_pkg::mubi4_test_true_loose(aes_idle);


//AHB interface
ahb_slv_sif #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(CIF_DATA_WIDTH)
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

// AHB CIF Mux
// No real muxing, just respond with error if we detect a request collision.
// It is FW responsiblity to ensure only AHB or DMA accesses AES at a time
assign req_collision = dma_req_dv & ahb_dv;

assign aes_cif_endian_swap = aes_cif_req_dv && hwif_out.CTRL0.ENDIAN_SWAP.value  && (
        aes_cif_req_addr == `AES_REG_DATA_IN_0 ||
        aes_cif_req_addr == `AES_REG_DATA_IN_1 ||
        aes_cif_req_addr == `AES_REG_DATA_IN_2 ||
        aes_cif_req_addr == `AES_REG_DATA_IN_3 ||
        aes_cif_req_addr == `AES_REG_DATA_OUT_0 ||
        aes_cif_req_addr == `AES_REG_DATA_OUT_1 ||
        aes_cif_req_addr == `AES_REG_DATA_OUT_2 ||
        aes_cif_req_addr == `AES_REG_DATA_OUT_3 
    );

assign aes_cif_req_dv = dma_req_dv | ahb_dv;
assign aes_cif_req_write = dma_req_dv ? dma_req_write : ahb_write ;
assign aes_cif_req_addr = dma_req_dv ? dma_req_addr : ahb_addr ;
assign aes_cif_req_wdata = dma_req_dv ? dma_req_wdata : ahb_wdata ;

always_comb begin
  for (int b=0; b<CIF_DATA_NUM_BYTES; b++) begin
      aes_cif_req_wdata_post_endian[b*8 +: 8] = aes_cif_endian_swap ?
                                                  aes_cif_req_wdata[(CIF_DATA_NUM_BYTES-1-b)*8 +: 8] : // convert data from big endian to little endian
                                                  aes_cif_req_wdata[b*8 +: 8];                         // assign data as-is to AES (little endian)
  end
end

assign dma_req_hold = dma_req_dv & aes_cif_req_hold;
assign ahb_hold = ahb_dv & aes_cif_req_hold;
assign dma_req_error = (dma_req_dv & aes_cif_req_error) | req_collision;
assign ahb_err = (ahb_dv & aes_cif_req_error) | req_collision;

always_comb begin
  for (int b=0; b<CIF_DATA_NUM_BYTES; b++) begin
      aes_cif_req_rdata_post_endian[b*8 +: 8] = aes_cif_endian_swap ? 
                                                  aes_cif_req_rdata[(CIF_DATA_NUM_BYTES-1-b)*8 +: 8] : // convert data from little endian to big endian
                                                  aes_cif_req_rdata[b*8 +: 8];                         // assign data as-is from AES (little endian)
  end 
end

assign dma_req_rdata = dma_req_dv ? aes_cif_req_rdata_post_endian : '0; // TODO block dma interface when kv write is requested
assign ahb_rdata = ahb_dv ? aes_cif_req_rdata_post_endian: '0;


//TLUL Adapter
caliptra_tlul_adapter_vh
#(
  .VH_REGISTER_ADDRESS_OFFSET(32'h0000_0800)
)
caliptra_tlul_adapter_vh_inst
(
  .clk_i(clk),
  .rst_ni(reset_n),

  .tl_o(adapter_to_aes_tl),
  .tl_i(aes_to_adapter_tl),

  // Valid-Hold device interface (VH to TLUL).
  .dv_i(aes_cif_req_dv),
  .hld_o(aes_cif_req_hold),
  .addr_i({ {caliptra_tlul_pkg::TL_AW-AHB_ADDR_WIDTH{1'b0}}, aes_cif_req_addr}),
  .write_i(aes_cif_req_write),
  .wdata_i(aes_cif_req_wdata_post_endian),
  .wstrb_i('1),
  .size_i(3'b010),
  .rdata_o(aes_cif_req_rdata),
  .error_o(aes_cif_req_error),
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

edn_pkg::edn_rsp_t edn_i;
logic [edn_pkg::ENDPOINT_BUS_WIDTH-1:0] edn_bus;
assign edn_i = '{edn_ack:edn_req.edn_req, edn_fips:0, edn_bus:edn_bus};

assign caliptra2aes.clear_secrets = debugUnlock_or_scan_mode_switch;
assign caliptra2aes.key_release_key_size = key_release_key_size;

//AES Engine
aes
aes_inst (
  .clk_i(clk),
  .rst_ni(reset_n),
  .rst_shadowed_ni(reset_n),

  .idle_o(aes_idle),

  // Life cycle
  .lc_escalate_en_i(lc_ctrl_pkg::Off),
  
  // status signals
  .input_ready_o,
  .output_valid_o,

  // Caliptra interface
  .caliptra2aes(caliptra2aes),
  .aes2caliptra(aes2caliptra),

  // Entropy distribution network (EDN) interface
  .clk_edn_i(clk),
  .rst_edn_ni(reset_n),
  .edn_o(edn_req),
  .edn_i(edn_i),

  // Key manager (keymgr) key sideload interface
  .keymgr_key_i(keymgr_key),

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
  hwif_in.AES_NAME[0].NAME.next = 32'h0061657; //"aes"
  hwif_in.AES_NAME[1].NAME.next = '0; 
  hwif_in.AES_VERSION[0].VERSION.next = 32'h00312e30; //"1.0"
  hwif_in.AES_VERSION[1].VERSION.next = '0; 

  //set ready when keyvault isn't busy
  hwif_in.AES_KV_RD_KEY_STATUS.READY.next = kv_key_ready;
  //set error code
  hwif_in.AES_KV_RD_KEY_STATUS.ERROR.next = kv_key_error;
  //set valid when fsm is done
  hwif_in.AES_KV_RD_KEY_STATUS.VALID.hwset = kv_key_done;
  //clear valid when new request is made
  hwif_in.AES_KV_RD_KEY_STATUS.VALID.hwclr = kv_key_read_ctrl_reg.read_en;
  //clear enable when busy
  hwif_in.AES_KV_RD_KEY_CTRL.read_en.hwclr = ~kv_key_ready;
  //set ready when keyvault isn't busy
  hwif_in.AES_KV_WR_STATUS.READY.next = kv_write_ready;
  //set error code
  hwif_in.AES_KV_WR_STATUS.ERROR.next = kv_write_error;
  //set valid when fsm is done
  hwif_in.AES_KV_WR_STATUS.VALID.hwset = caliptra2aes.kv_write_done;
  //clear valid when new request is made
  hwif_in.AES_KV_WR_STATUS.VALID.hwclr = kv_write_ctrl_reg.write_en;
  //clear enable when busy
  hwif_in.AES_KV_WR_CTRL.write_en.hwclr = ~kv_write_ready;

  hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = '0; //unused
  hwif_in.intr_block_rf.error_internal_intr_r.error0_sts.hwset = 1'b0; // unused
  hwif_in.intr_block_rf.error_internal_intr_r.error1_sts.hwset = 1'b0; // unused
  hwif_in.intr_block_rf.error_internal_intr_r.error2_sts.hwset = 1'b0; // unused
  hwif_in.intr_block_rf.error_internal_intr_r.error3_sts.hwset = 1'b0; // unused
end

// Software write-enables to prevent KV reg manipulation mid-operation
always_comb hwif_in.AES_KV_RD_KEY_CTRL.read_en.swwe         = status_idle_o && input_ready_o && kv_key_ready;
always_comb hwif_in.AES_KV_RD_KEY_CTRL.read_entry.swwe      = status_idle_o && input_ready_o && kv_key_ready;
always_comb hwif_in.AES_KV_RD_KEY_CTRL.pcr_hash_extend.swwe = status_idle_o && input_ready_o && kv_key_ready;
always_comb hwif_in.AES_KV_RD_KEY_CTRL.rsvd.swwe            = status_idle_o && input_ready_o && kv_key_ready;

// KV write control must be written while AES engine is idle, even though
// output isn't written to KV until the end of the operation.
// Prevent partial-key attacks by blocking register modifications during core execution.
always_comb hwif_in.AES_KV_WR_CTRL.write_en.swwe              = status_idle_o && input_ready_o;
always_comb hwif_in.AES_KV_WR_CTRL.write_entry.swwe           = status_idle_o && input_ready_o;
always_comb hwif_in.AES_KV_WR_CTRL.hmac_key_dest_valid.swwe   = status_idle_o && input_ready_o;
always_comb hwif_in.AES_KV_WR_CTRL.hmac_block_dest_valid.swwe = status_idle_o && input_ready_o;
always_comb hwif_in.AES_KV_WR_CTRL.mldsa_seed_dest_valid.swwe = status_idle_o && input_ready_o;
always_comb hwif_in.AES_KV_WR_CTRL.ecc_pkey_dest_valid.swwe   = status_idle_o && input_ready_o;
always_comb hwif_in.AES_KV_WR_CTRL.ecc_seed_dest_valid.swwe   = status_idle_o && input_ready_o;
always_comb hwif_in.AES_KV_WR_CTRL.aes_key_dest_valid.swwe    = status_idle_o && input_ready_o;
always_comb hwif_in.AES_KV_WR_CTRL.mlkem_seed_dest_valid.swwe = status_idle_o && input_ready_o;
always_comb hwif_in.AES_KV_WR_CTRL.mlkem_msg_dest_valid.swwe  = status_idle_o && input_ready_o;
always_comb hwif_in.AES_KV_WR_CTRL.dma_data_dest_valid.swwe   = status_idle_o && input_ready_o;
always_comb hwif_in.AES_KV_WR_CTRL.rsvd.swwe                  = status_idle_o && input_ready_o;

//keyault FSM
//keyvault control reg macros for assigning to struct
`CALIPTRA_KV_READ_CTRL_REG2STRUCT(kv_key_read_ctrl_reg, AES_KV_RD_KEY_CTRL)
`CALIPTRA_KV_WRITE_CTRL_REG2STRUCT(kv_write_ctrl_reg, AES_KV_WR_CTRL)

//Read Key context
always_ff@(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        kv_key_present_slot <= '0;
    end
    else if (kv_key_read_ctrl_reg.read_en) begin
        kv_key_present_slot <= kv_key_read_ctrl_reg.read_entry;
    end
end

always_comb begin
    kv_key_read_metrics.ocp_lock_in_progress = ocp_lock_in_progress;
    kv_key_read_metrics.kv_read_dest         = KV_NUM_READ'(1<<KV_DEST_IDX_AES_KEY);
    kv_key_read_metrics.kv_key_entry         = kv_key_read_ctrl_reg.read_entry;
end

//Read Key
kv_read_client #(
  .DATA_WIDTH(keymgr_pkg::KeyWidth),
  .PAD(0)
)
aes_key_kv_read
(
    .clk(clk),
    .rst_b(reset_n),
    .zeroize(debugUnlock_or_scan_mode_switch), 

    //client control register
    .read_ctrl_reg(kv_key_read_ctrl_reg),

    //access filtering rule metrics
    .read_metrics (kv_key_read_metrics),

    //interface with kv
    .kv_read(kv_read),
    .kv_resp(kv_rd_resp),

    //interface with client
    .write_en(kv_key_write_en),
    .write_offset(kv_key_write_offset),
    .write_data(kv_key_write_data),

    .error_code(kv_key_error),
    .kv_ready(kv_key_ready),
    .read_done(kv_key_done)
);

logic [(keymgr_pkg::KeyWidth/32)-1:0][3:0][7:0] kv_key_reg;

// AES KV write is only supported for key-release in ocp-lock mode, with the AES-ECB-decrypt use-case
// Key size is in bytes
always_comb kv_wr_num_dwords = ($clog2(CLP_AES_KV_WR_DW/32)+1)'(key_release_key_size>>2);

always_comb begin
    kv_write_metrics.ocp_lock_in_progress = ocp_lock_in_progress;
    kv_write_metrics.kv_data0_present     = aes2caliptra.kv_key_in_use; // TODO -- what if FW toggles sideload while op is in progress?
    kv_write_metrics.kv_data0_entry       = kv_key_present_slot;
    kv_write_metrics.kv_data1_present     = 1'b0;
    kv_write_metrics.kv_data1_entry       = KV_ENTRY_ADDR_W'(0);
    kv_write_metrics.kv_write_src         = KV_NUM_WRITE'(1 << KV_WRITE_IDX_AES);
    kv_write_metrics.kv_write_entry       = kv_write_ctrl_reg.write_entry;
    kv_write_metrics.aes_decrypt_ecb_op   = aes2caliptra.aes_operation_is_ecb_decrypt;
end

always_comb caliptra2aes.block_reg_output = ocp_lock_in_progress &&
                                            (aes2caliptra.kv_key_in_use && kv_key_present_slot == OCP_LOCK_RT_OBF_KEY_KV_SLOT) &&
                                            aes2caliptra.aes_operation_is_ecb_decrypt;

//Write to keyvault
kv_write_client #(
  .DATA_WIDTH(CLP_AES_KV_WR_DW),
  .KV_WRITE_SWAP_DWORDS(0)
)
aes_result_kv_write
(
  .clk(clk),
  .rst_b(reset_n),
  .zeroize(debugUnlock_or_scan_mode_switch),

  //client control register
  .write_ctrl_reg(kv_write_ctrl_reg),
  .num_dwords    (kv_wr_num_dwords ),

  //access filtering rule metrics
  .write_metrics (kv_write_metrics),

  //interface with kv
  .kv_write(kv_write  ),
  .kv_resp (kv_wr_resp),

  //interface with client
  .dest_keyvault  (caliptra2aes.kv_en            ),
  .dest_data_avail(aes2caliptra.kv_data_out_valid),
  .dest_data      (aes2caliptra.kv_data_out      ),

  .error_code(kv_write_error            ),
  .kv_ready  (kv_write_ready            ),
  .dest_done (caliptra2aes.kv_write_done)
);

//load keyvault key into local reg
//swizzle keyvault value to match endianness of aes engine
genvar g_dword;
genvar g_byte;
generate
  for (g_dword = 0; g_dword < keymgr_pkg::KeyWidth/32; g_dword++) begin
    for (g_byte = 0; g_byte < 4; g_byte++) begin
      always_ff @(posedge clk or negedge reset_n) begin
        if (~reset_n) begin
          kv_key_reg[g_dword][g_byte] <= '0;
        end else if(debugUnlock_or_scan_mode_switch) begin
          kv_key_reg[g_dword][g_byte] <= '0;
        // zeroize the buffered KeyVault value when reading in a new key
        // On the first beat, the least-sig dword is set, all other dwords set to 0
        end else if (kv_key_write_en && (g_dword > 0) && (kv_key_write_offset < AES_KV_KEY_DW_WIDTH'(g_dword))) begin
          kv_key_reg[g_dword][g_byte] <= 0;
        end else if (kv_key_write_en && (kv_key_write_offset == AES_KV_KEY_DW_WIDTH'(g_dword))) begin
          kv_key_reg[g_dword][g_byte] <= kv_key_write_data[3-g_byte];
        end
      end
    end
  end
endgenerate

//Drive keymgr interface into AES
always_ff @(posedge clk or negedge reset_n) begin
  if (~reset_n) begin
    keymgr_key.valid <= '0;
    keymgr_key.key <= '0;
  end
  else if (kv_key_read_ctrl_reg.read_en || (kv_key_error == KV_READ_FAIL) || debugUnlock_or_scan_mode_switch) begin //new request, invalidate old key
    keymgr_key.valid <= '0;
    keymgr_key.key[0] <= '0;
    keymgr_key.key[1] <= '0;
  end
  else if (kv_key_done) begin //key is copied, drive valid to aes
    keymgr_key.valid <= '1;
    keymgr_key.key[0] <= kv_key_reg;
    keymgr_key.key[1] <= '0;
  end
end

// Entropy interface
// We use a Trivium stream cipher primitive which is parameterized as follows:
// - It takes 288 bits of seed material at a time provided by firmware via the ENTROPY_IF_SEED
//   registers to reseed the entire Trivium state in one shot. Firmware has to perform 9 write
//   operations to the ENTROPY_IF_SEED registers.
// - It delivers 32 bits per clock cycle to AES via the EDN interface. AES will repeatedly request
//   fresh entropy via this interface. The rate depends on the value of
//   CTRL_SHADOWED.PRNG_RESEED_RATE.
//
// Note: Upon reset, the state of the Trivium primitive is initialized to a netlist constant. The
//       primitive thus always generates the same output after reset. It is the responsibility of
//       firmware to provide a new state seed after reset.
localparam int unsigned NumSeedChunks =
    caliptra_prim_trivium_pkg::TriviumStateWidth / aes_clp_reg_pkg::AES_CLP_REG_DATA_WIDTH;
logic [caliptra_prim_trivium_pkg::TriviumStateWidth-1:0] trivium_seed;
logic [NumSeedChunks-1:0] trivium_seed_qe;
logic [NumSeedChunks-1:0] trivium_seed_chunk_vld_q, trivium_seed_chunk_vld_d;
logic trivium_seed_en;

// Concatenate the register values to produce the full state seed.
assign trivium_seed = {hwif_out.ENTROPY_IF_SEED[8].ENTROPY_IF_SEED.value,
                       hwif_out.ENTROPY_IF_SEED[7].ENTROPY_IF_SEED.value,
                       hwif_out.ENTROPY_IF_SEED[6].ENTROPY_IF_SEED.value,
                       hwif_out.ENTROPY_IF_SEED[5].ENTROPY_IF_SEED.value,
                       hwif_out.ENTROPY_IF_SEED[4].ENTROPY_IF_SEED.value,
                       hwif_out.ENTROPY_IF_SEED[3].ENTROPY_IF_SEED.value,
                       hwif_out.ENTROPY_IF_SEED[2].ENTROPY_IF_SEED.value,
                       hwif_out.ENTROPY_IF_SEED[1].ENTROPY_IF_SEED.value,
                       hwif_out.ENTROPY_IF_SEED[0].ENTROPY_IF_SEED.value};

// Concatenate the register write enables.
assign trivium_seed_qe = {hwif_out.ENTROPY_IF_SEED[8].ENTROPY_IF_SEED.swmod,
                          hwif_out.ENTROPY_IF_SEED[7].ENTROPY_IF_SEED.swmod,
                          hwif_out.ENTROPY_IF_SEED[6].ENTROPY_IF_SEED.swmod,
                          hwif_out.ENTROPY_IF_SEED[5].ENTROPY_IF_SEED.swmod,
                          hwif_out.ENTROPY_IF_SEED[4].ENTROPY_IF_SEED.swmod,
                          hwif_out.ENTROPY_IF_SEED[3].ENTROPY_IF_SEED.swmod,
                          hwif_out.ENTROPY_IF_SEED[2].ENTROPY_IF_SEED.swmod,
                          hwif_out.ENTROPY_IF_SEED[1].ENTROPY_IF_SEED.swmod,
                          hwif_out.ENTROPY_IF_SEED[0].ENTROPY_IF_SEED.swmod};

// Track write operations:
// - Perform the reseed once every register has been written at least once.
// - Clear the tracking upon doing the reseed operation.
assign trivium_seed_chunk_vld_d = trivium_seed_en ? '0 : trivium_seed_chunk_vld_q | trivium_seed_qe;
assign trivium_seed_en = &trivium_seed_chunk_vld_q;

always_ff @(posedge clk or negedge reset_n) begin
  if (~reset_n) begin
    trivium_seed_chunk_vld_q <= '0;
  end else begin
    trivium_seed_chunk_vld_q <= trivium_seed_chunk_vld_d;
  end
end

caliptra_prim_trivium #(
  .OutputWidth(edn_pkg::ENDPOINT_BUS_WIDTH),
  .SeedType   (caliptra_prim_trivium_pkg::SeedTypeStateFull)
)
u_caliptra_prim_trivium
(
    .clk_i(clk),
    .rst_ni(reset_n),

    .en_i                (edn_req.edn_req),
    .allow_lockup_i      ('0), // Not used.
    .seed_en_i           (trivium_seed_en),
    .seed_done_o         (), // Not used.
    .seed_req_o          (), // Not used.
    .seed_ack_i          (trivium_seed_en),
    .seed_key_i          ('0), // Not used.
    .seed_iv_i           ('0), // Not used.
    .seed_state_full_i   (trivium_seed),
    .seed_state_partial_i('0), // Not used.

    .key_o(edn_bus),
    .err_o()
);

`CALIPTRA_ASSERT_STABLE(ERR_AES_KEY_RD_CTRL_NOT_STABLE, kv_key_read_ctrl_reg, clk, (!reset_n || status_idle_o) )
`CALIPTRA_ASSERT_STABLE(ERR_AES_WR_CTRL_NOT_STABLE, kv_write_ctrl_reg, clk, (!reset_n || status_idle_o) )
`CALIPTRA_ASSERT_STABLE(ERR_AES_KEY_NOT_STABLE, kv_key_reg, clk, (!reset_n || status_idle_o) )

endmodule
