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
// Description:
//      Control State Machine for Caliptra AXI Manager (DMA) block
//

module axi_dma_ctrl
import axi_pkg::*;
import soc_ifc_pkg::*;
import kv_defines_pkg::*;
#(
    parameter AW = 64,
    parameter DW = 32,         // Data Width
              BC = DW/8,       // Byte Count
              BW = $clog2(BC)  // Byte count Width
)(
    input logic clk,
    input logic cptra_pwrgood,
    input logic rst_n,

    // Recovery INF Interrupt
    // Should only assert when a full block_size of data is available at the
    // recovery interface FIFO
    input logic recovery_data_avail,
    input logic recovery_image_activated,

    // Internal Signaling
    input logic mbox_lock,
    input logic sha_lock,
    input logic debugUnlock_or_scan_mode_switch,
    input logic ocp_lock_in_progress,
    input logic [63:0] key_release_addr,
    input logic [15:0] key_release_size,

    // Mailbox SRAM INF
    output logic             mb_dv,
    input  logic             mb_hold,
    input  logic             mb_error,
    output var soc_ifc_req_t mb_data,
    input  logic [DW-1:0]    mb_rdata,

    // AES Interface
    input  logic             aes_input_ready,
    input  logic             aes_output_valid,
    input  logic             aes_status_idle,
    output logic             aes_req_dv,
    input  logic             aes_req_hold,
    output soc_ifc_req_t     aes_req_data,
    input  logic [DW-1:0]    aes_rdata,
    input  logic             aes_err,

    // kv interface
    output kv_read_t    kv_read,
    input  kv_rd_resp_t kv_rd_resp,

    // AXI Manager Read INF
    axi_dma_req_if.src    r_req_if,
    output logic          r_ready_o,
    input  logic          r_valid_i,
    input  logic [DW-1:0] r_data_i,

    // AXI Manager Write INF
    axi_dma_req_if.src    w_req_if,
    input  logic          w_ready_i,
    output logic          w_valid_o,
    output logic [DW-1:0] w_data_o,

    // Register INF
    input  logic                      dv,
    input var soc_ifc_req_t           req_data,
    output logic                      hold,
    output logic [SOC_IFC_DATA_W-1:0] rdata,
    output logic                      error,

    // Interrupt
    output logic notif_intr,
    output logic error_intr

);

    // --------------------------------------- //
    // Imports                                 //
    // --------------------------------------- //
    import axi_dma_reg_pkg::*;
    `include "caliptra_prim_assert.sv"


    // --------------------------------------- //
    // Localparams/Typedefs                    //
    // --------------------------------------- //

    `define MIN_OF(a,b) ((a < b) ? a : b)
    `define MAX_OF(a,b) ((a > b) ? a : b)
    
    localparam FIFO_BC = 512; // depth in bytes
    localparam FIFO_BW = caliptra_prim_util_pkg::vbits((FIFO_BC/BC)+1); // width of a signal that reports FIFO slot consumption

    localparam AES_FIFO_BC = 16; // depth in bytes
    localparam AES_FIFO_BW = caliptra_prim_util_pkg::vbits((AES_FIFO_BC/BC)+1); // width of a signal that reports FIFO slot consumption

    // Smaller of
    //   a) 4096 (AXI max burst size)
    //   b) Configured data width X max supported AXI burst length value
    localparam AXI_MAX_BLOCK_SIZE = `MIN_OF(AXI_LEN_MAX_BYTES,(AXI_LEN_MAX_VALUE * BC));
    // Smaller of
    //   a) Largest legal AXI block size
    //   b) Largest burst that can fit in the FIFO
    localparam MAX_BLOCK_SIZE     = `MIN_OF(AXI_MAX_BLOCK_SIZE,FIFO_BC/2);
    // Smaller of
    //   a) MAX_BLOCK_SIZE
    //   b) Configured data width X max supported AXI burst length value for FIXED bursts
    localparam AXI_MAX_FIXED_BLOCK_SIZE = `MIN_OF(AXI_LEN_MAX_BYTES,(AXI_FIXED_LEN_MAX_VALUE * BC));
    localparam MAX_FIXED_BLOCK_SIZE     = `MIN_OF(AXI_MAX_FIXED_BLOCK_SIZE,MAX_BLOCK_SIZE);
    localparam DMA_MAX_XFER_SIZE = 32'h10_0000; // 1MiB


    // --------------------------------------- //
    // Signals                                 //
    // --------------------------------------- //

    axi_dma_reg_pkg::axi_dma_reg__in_t hwif_in;
    axi_dma_reg_pkg::axi_dma_reg__out_t hwif_out;

    enum logic [1:0] {
        DMA_IDLE,
        DMA_WAIT_DATA,
        DMA_DONE,
        DMA_ERROR
    } ctrl_fsm_ns,ctrl_fsm_ps;
    
    
    enum logic [3:0] {
        AES_IDLE,
        AES_WAIT_INPUT_READY,
        AES_WAIT_IDLE,
        AES_UPDATE_BYTE_COUNT,
        AES_WRITE_BLOCK,
        AES_WAIT_OUTPUT_VALID,
        AES_READ_OUTPUT,
        AES_DONE,
        AES_ERROR
    } aes_fsm_ns, aes_fsm_ps;

    logic start_aes_fsm;
    logic aes_init_done;
    logic aes_init_done_next;
    logic [1:0] aes_cif_write_cnt, aes_cif_write_cnt_next;
    logic aes_cif_write_cnt_reset;
    logic aes_cif_write_block_done;
    logic aes_cif_read_block_done;
    logic aes_cif_update_byte_count_done; 
    logic aes_cif_write_cnt_incr;
    logic aes_req_wait;
    logic aes_req_wait_next;
    logic aes_error;
    logic aes_req_dv_q;
    logic aes_to_axi_last_transfer;
    logic aes_to_axi_last_transfer_next;
    
    logic [1:0] aes_cif_read_cnt;
    logic [1:0] aes_cif_read_cnt_next;
    logic aes_cif_read_cnt_incr;
      
    // AES Fifo Controls
    logic aes_fifo_w_valid;
    logic aes_fifo_w_ready;
    logic [DW-1:0] aes_fifo_w_data ;
    logic aes_fifo_r_valid;
    logic aes_fifo_r_ready;
    logic [DW-1:0] aes_fifo_r_data; 
    logic aes_fifo_full ;
    logic [AES_FIFO_BW-1:0] aes_fifo_depth;
    logic aes_fifo_empty;


    logic [SOC_IFC_DATA_W-1:0] reg_biten;
    logic reg_rd_err, reg_wr_err;
    logic reg_rd_stall, reg_wr_stall;
    logic reg_rd_ack_nc, reg_wr_ack_nc;

    // FIFO signals
    logic               fifo_w_ready;
    logic               fifo_w_valid;
    logic [DW-1:0]      fifo_w_data;
    logic               fifo_r_ready;
    logic               fifo_r_valid;
    logic [DW-1:0]      fifo_r_data;
    logic [FIFO_BW-1:0] fifo_depth;
    logic               fifo_full, fifo_full_r;
    logic               fifo_empty, fifo_empty_r;

    // Read Route Signals
    logic [DW-1:0] rd_route_data;
    logic          rd_route_valid;
    logic          rd_route_ready;
    logic [DW-1:0] aes_fsm_rd_route_data;
    logic          aes_fsm_rd_route_valid;
    logic          aes_fsm_rd_route_ready;

    // Internal signals
    axi_dma_reg__ctrl__rd_route__rd_route_e_e rd_route;
    axi_dma_reg__ctrl__wr_route__wr_route_e_e wr_route;

    logic cmd_inv_rd_route;
    logic cmd_inv_wr_route;
    logic cmd_inv_route_combo;
    logic cmd_inv_src_addr;
    logic cmd_inv_dst_addr;
    logic cmd_inv_byte_count;
    logic cmd_inv_block_size;
    logic cmd_inv_rd_fixed;
    logic cmd_inv_wr_fixed;
    logic cmd_inv_mbox_lock;
    logic cmd_inv_sha_lock;
    logic cmd_parse_error;
    logic cmd_inv_aes_route_combo;
    logic cmd_inv_aes_block_size;
    logic cmd_inv_aes_fixed;      

    logic rd_req_hshake, rd_req_hshake_bypass;
    logic wr_req_hshake, wr_req_hshake_bypass;
    // Count read requests that have been enqueued due to recovery_data_avail.
    // Width of signal is sufficient to track 2x the maximum number of requests
    // possible for any given "block" of data.
    // The maximum number of requests for a given "block" is calculated as:
    //   max_block_size / min_size_per_request
    // Where
    //   max_block_size = AXI_LEN_MAX_BYTES
    //   min_size_per_request = BC
    // In payload_available edge-detection configuration, this allows the counter to schedule
    // the next set of requests if recovery_data_avail pulse is observed
    // while there are still requests that have not been issued from the prior pulse.
    logic [AXI_LEN_BC_WIDTH-BW:0] rd_req_count_for_payload, rd_req_count_for_payload_next;
    logic rd_req_stall;
    `ifndef CALIPTRA_AXI_DMA_PAYLOAD_AVAILABLE_EDGE_DETECTION_MODE
    logic rd_wait_to_ack_avail; // Used to enforce that requests go one at a time
    `else 
    logic recovery_data_avail_d, recovery_data_avail_p; // Edge detection
    `endif
    logic [3:0] wr_resp_pending; // Counts up to 15 pending Write responses.
                                 // Once this counter saturates, we stall new requests
                                 // until further responses arrive.
                                 // This is an artificially imposed limit, intended
                                 // to allow a subordinate to have some delay in sending
                                 // write responses without ever throttling this DMA.

    logic [DW-1:0] r_data_mask;

    logic [AW-1:0] src_addr, dst_addr;
    logic [FIFO_BW-1:0] rd_credits;
    logic [FIFO_BW-1:0] wr_credits;
    logic wr_credits_fifo_w_valid;
    logic wr_credits_fifo_w_ready;
    logic [AXI_LEN_BC_WIDTH-1:0] block_size_mask;
    // 1's based counters
    logic [31:0] rd_bytes_requested;
    logic        rd_bytes_rem_thresh; // Number of read bytes remaining to be requested is lower than the threshold of MAX_BLOCK_SIZE
    logic [31:0] wr_bytes_requested;
    logic        wr_bytes_rem_thresh; // Number of write bytes remaining to be requested is lower than the threshold of MAX_BLOCK_SIZE
    logic [AXI_LEN_BC_WIDTH-1:0] rd_align_req_byte_count; // byte-count in a request until nearest AXI boundary
    logic [AXI_LEN_BC_WIDTH-1:0] rd_final_req_byte_count; // byte-count in the final request, which may be smaller than a typical request
    logic [AXI_LEN_BC_WIDTH-1:0] rd_req_byte_count;       // byte-count calculated for the current read request
    logic [AXI_LEN_BC_WIDTH-1:0] wr_align_req_byte_count; // byte-count in a request until nearest AXI boundary
    logic [AXI_LEN_BC_WIDTH-1:0] wr_sel_req_byte_count;         // byte-count select between AES and FIFO count
    logic [AXI_LEN_BC_WIDTH-1:0] wr_aes_ceil_req_byte_count;    // byte-count select between AES FIFO max size or number of bytes left
    logic [AXI_LEN_BC_WIDTH-1:0] wr_final_req_byte_count; // byte-count in the final request, which may be smaller than a typical request
    logic [AXI_LEN_BC_WIDTH-1:0] wr_req_byte_count;       // byte-count calculated for the current read request

    logic [31:0] bytes_remaining; // Decrements with arrival of beat at DESTINATION.
    logic [31:0] rd_fifo_bytes_remaining; // Decrements with arrival of data into FIFO
    logic all_bytes_transferred;
    logic axi_error;
    logic mb_lock_dropped, mb_lock_error;

    // KeyVault signals
    kv_read_ctrl_reg_t        kv_read_ctrl_reg;
    kv_read_filter_metrics_t  kv_read_metrics;
    logic                     kv_read_en;
    logic                     kv_read_once;
    logic                     kv_data_write_en;
//    logic [$clog2(OCP_LOCK_MEK_NUM_DWORDS)-1:0] kv_data_write_offset;
    logic [31:0]              kv_data_write_data;
    kv_error_code_e           kv_data_error_code;
    logic                     kv_data_kv_ready;
    logic                     kv_data_read_done;
    logic                     kv_read_error;           // KV read operation error
    logic                     kv_premature_done_error; // KV read done before expected key size read
    logic                     kv_any_error; // Any KV read error  


    // --------------------------------------- //
    // Control Register Block                  //
    // --------------------------------------- //
    genvar i;
    generate
        for (i=0;i<SOC_IFC_DATA_W;i++) begin: assign_biten_from_wstrb
            assign reg_biten[i] = req_data.wstrb[i/8];
        end
    endgenerate
    axi_dma_reg i_axi_dma_reg (
        .clk(clk ),
        .rst(1'b0),

        .s_cpuif_req         (dv                                                            ),
        .s_cpuif_req_is_wr   (req_data.write                                                ),
        .s_cpuif_addr        (req_data.addr[axi_dma_reg_pkg::AXI_DMA_REG_MIN_ADDR_WIDTH-1:0]),
        .s_cpuif_wr_data     (req_data.wdata                                                ),
        .s_cpuif_wr_biten    (reg_biten                                                     ),
        .s_cpuif_req_stall_wr(reg_wr_stall                                                  ),
        .s_cpuif_req_stall_rd(reg_rd_stall                                                  ),
        .s_cpuif_rd_ack      (reg_rd_ack_nc                                                 ),
        .s_cpuif_rd_err      (reg_rd_err                                                    ),
        .s_cpuif_rd_data     (rdata                                                         ),
        .s_cpuif_wr_ack      (reg_wr_ack_nc                                                 ),
        .s_cpuif_wr_err      (reg_wr_err                                                    ),

        .hwif_in             (hwif_in                                                       ),
        .hwif_out            (hwif_out                                                      )
    );
    assign error = reg_rd_err   || reg_wr_err;
    assign hold  = reg_rd_stall || reg_wr_stall;


    always_comb begin
        hwif_in.cptra_pwrgood = cptra_pwrgood;
        hwif_in.cptra_rst_b   = rst_n;
        hwif_in.soc_req       = req_data.soc_req;
        hwif_in.dma_swwel     = req_data.soc_req || ctrl_fsm_ps != DMA_IDLE;
    end


    // --------------------------------------- //
    // Control FSM                             //
    // --------------------------------------- //
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ctrl_fsm_ps <= DMA_IDLE;
        end else begin
            ctrl_fsm_ps <= ctrl_fsm_ns;
        end
    end

    always_comb begin
        ctrl_fsm_ns = ctrl_fsm_ps;
        case(ctrl_fsm_ps) inside
            DMA_IDLE: begin
                if (hwif_out.ctrl.go.value && cmd_parse_error) begin
                    ctrl_fsm_ns = DMA_ERROR;
                end
                else if (hwif_out.ctrl.go.value) begin
                    ctrl_fsm_ns = DMA_WAIT_DATA;
                end
            end
            DMA_WAIT_DATA: begin
                // KV error occurs prior to any data movement, so DMA can transfer immediately to ERROR state
                // without waiting for AXI transfer to gracefully end
                if ((all_bytes_transferred && (axi_error || mb_lock_error || aes_error)) ||
                    (kv_any_error)) begin
                    ctrl_fsm_ns = DMA_ERROR;
                end
                else if (all_bytes_transferred) begin
                    ctrl_fsm_ns = DMA_DONE;
                end
            end
            DMA_DONE: begin
                    ctrl_fsm_ns = DMA_IDLE;
            end
            DMA_ERROR: begin
                if (hwif_out.ctrl.flush.value) begin
                    ctrl_fsm_ns = DMA_IDLE;
                end
            end
            default: begin
                    ctrl_fsm_ns = ctrl_fsm_ps;
            end
        endcase
    end

    always_comb hwif_in.ctrl.go.hwclr    = (ctrl_fsm_ps == DMA_DONE) || ((ctrl_fsm_ps == DMA_ERROR) && hwif_out.ctrl.flush.value);
    always_comb hwif_in.ctrl.flush.hwclr = (ctrl_fsm_ps == DMA_IDLE);

    always_comb hwif_in.cap.fifo_max_depth.next        = FIFO_BC/BC;
    always_comb hwif_in.status0.busy.next              = (ctrl_fsm_ps != DMA_IDLE);
    always_comb hwif_in.status0.error.next             = (ctrl_fsm_ps == DMA_ERROR);
    always_comb hwif_in.status0.fifo_depth.next        = 12'(fifo_depth);
    always_comb hwif_in.status0.axi_dma_fsm_ps.next    = ctrl_fsm_ps;
    always_comb hwif_in.status0.axi_dma_aes_fsm_ps.next    = aes_fsm_ps;
    always_comb hwif_in.status0.payload_available.next = recovery_data_avail;
    always_comb hwif_in.status0.image_activated.next   = recovery_image_activated;
    always_comb hwif_in.status1.bytes_remaining.next   = bytes_remaining;
    
    assign all_bytes_transferred = ctrl_fsm_ps == DMA_WAIT_DATA &&
                                   bytes_remaining == 0 &&
                                   wr_resp_pending == 0 &&
                                   wr_bytes_requested == hwif_out.byte_count.count &&
                                   (aes_fsm_ps == AES_IDLE || aes_fsm_ps == AES_DONE || aes_fsm_ps == AES_ERROR); // Interlock with AES FSM due to DMA FSM going
                                                                                                                  // to "DONE" before AES FSM with 1 DWORD 
                                                                                                                  // because AES FSM is still reading the 
                                                                                                                  // other 3 DWORDs from the AES while the DMA 
                                                                                                                  // has already completed the AXI write 
                                                                                                                  // transaction.



    // --------------------------------------- //
    // Command Decode                          //
    // --------------------------------------- //
    generate
        if (AW <= 32) begin
            always_comb begin
                src_addr    = hwif_out.src_addr_l.addr_l.value[AW-1:0];
                dst_addr    = hwif_out.dst_addr_l.addr_l.value[AW-1:0];
            end
        end
        else if (AW < 64) begin
            always_comb begin
                src_addr    = {hwif_out.src_addr_h.addr_h.value[AW-32-1:0],
                               hwif_out.src_addr_l.addr_l.value};
                dst_addr    = {hwif_out.dst_addr_h.addr_h.value[AW-32-1:0],
                               hwif_out.dst_addr_l.addr_l.value};
            end
        end
        else begin
            always_comb begin
                src_addr    = {hwif_out.src_addr_h.addr_h.value,
                               hwif_out.src_addr_l.addr_l.value};
                dst_addr    = {hwif_out.dst_addr_h.addr_h.value,
                               hwif_out.dst_addr_l.addr_l.value};
            end
        end
    endgenerate

    // Simulation visibility to enumerated value is helpful for debug
    always_comb begin
        rd_route = axi_dma_reg__ctrl__rd_route__rd_route_e_e'(hwif_out.ctrl.rd_route.value);
        wr_route = axi_dma_reg__ctrl__wr_route__wr_route_e_e'(hwif_out.ctrl.wr_route.value);
    end

    always_comb begin
        cmd_inv_rd_route    = 1'b0; // There are no unassigned values from the 2-bit field, all individual configs are legal
        cmd_inv_wr_route    = !(hwif_out.ctrl.wr_route.value inside {axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE ,
                                                                     axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX    ,
                                                                     axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO,
                                                                     axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD  ,
                                                                     axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT}) ||
                              ((hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT) &&
                               !ocp_lock_in_progress);
        // Some COMBINATIONS of routes are disallowed
        case({hwif_out.ctrl.rd_route.value, hwif_out.ctrl.wr_route.value}) inside
            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE)}:    cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX)}:       cmd_inv_route_combo = 0;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO)}:   cmd_inv_route_combo = 0;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD)}:     cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT)}:   cmd_inv_route_combo = 0;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE)}:    cmd_inv_route_combo = 0;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX)}:       cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO)}:   cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD)}:     cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT)}:   cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE)}:    cmd_inv_route_combo = 0;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX)}:       cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO)}:   cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD)}:     cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT)}:   cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE)}:    cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX)}:       cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO)}:   cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD)}:     cmd_inv_route_combo = 0;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR),
             3'(axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT)}:   cmd_inv_route_combo = 1;

            default:                                                   cmd_inv_route_combo = 1;
        endcase
        cmd_inv_aes_route_combo = hwif_out.ctrl.aes_mode_en.value && (
                                    hwif_out.ctrl.rd_route.value != 2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR) ||  
                                    hwif_out.ctrl.wr_route.value != 3'(axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD));
        cmd_inv_aes_block_size = hwif_out.ctrl.aes_mode_en.value && hwif_out.block_size.size.value != '0;
        cmd_inv_aes_fixed      = hwif_out.ctrl.aes_mode_en.value && (hwif_out.ctrl.rd_fixed.value || hwif_out.ctrl.wr_fixed.value);
        cmd_inv_byte_count  = |hwif_out.byte_count.count.value[BW-1:0] ||
                              ~|hwif_out.byte_count.count.value ||
                              (hwif_out.byte_count.count.value > DMA_MAX_XFER_SIZE) ||
                              (hwif_out.byte_count.count.value > CPTRA_MBOX_SIZE_BYTES &&
                               ((hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX) ||
                                (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX))) ||
                              ((hwif_out.byte_count.count.value != 32'(key_release_size)) &&
                               (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT)) ||
                              ((hwif_out.byte_count.count.value > (OCP_LOCK_MEK_NUM_DWORDS << 2))  &&
                               (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT));
        // power of 2 and word-aligned
        cmd_inv_block_size  = |(hwif_out.block_size.size.value & (hwif_out.block_size.size.value-1)) ||
                              |hwif_out.block_size.size.value[BW-1:0];
        cmd_inv_rd_fixed    = hwif_out.ctrl.rd_fixed.value && hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE;
        cmd_inv_wr_fixed    = hwif_out.ctrl.wr_fixed.value && hwif_out.ctrl.wr_route.value inside {axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE,
                                                                                                   axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT};
        cmd_inv_mbox_lock   = !mbox_lock && ((hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX) || (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX));
        cmd_inv_sha_lock    = !sha_lock && (1'b0/*addr decode? NOTE: Direct-access to sha accelerator not implemented. Disable this check.*/);
        cmd_parse_error     = cmd_inv_rd_route    ||
                              cmd_inv_wr_route    ||
                              cmd_inv_route_combo ||
                              cmd_inv_aes_route_combo||
                              cmd_inv_aes_block_size ||
                              cmd_inv_aes_fixed   ||
                              cmd_inv_src_addr    ||
                              cmd_inv_dst_addr    ||
                              cmd_inv_byte_count  ||
                              cmd_inv_block_size  ||
                              cmd_inv_rd_fixed    ||
                              cmd_inv_wr_fixed    ||
                              cmd_inv_mbox_lock   ||
                              cmd_inv_sha_lock;
    end
    generate
        // An address is invalid if:
        //   * improperly aligned
        //   * MSB bits are set (out of address range)
        //   * Mismatches key_release_addr for KEYVAULT wr_route
        if (AW < 32) begin
            always_comb begin
                cmd_inv_src_addr    = |src_addr[BW-1:0] ||
                                      |hwif_out.src_addr_l.addr_l.value[31:AW] ||
                                      |hwif_out.src_addr_h.addr_h.value;
                cmd_inv_dst_addr    = |dst_addr[BW-1:0] ||
                                      |hwif_out.dst_addr_l.addr_l.value[31:AW] ||
                                      |hwif_out.dst_addr_h.addr_h.value ||
                                     (|(64'(dst_addr) ^ key_release_addr) && (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT));
            end
        end
        else if (AW < 64) begin
            always_comb begin
                cmd_inv_src_addr    = |src_addr[BW-1:0] ||
                                      |hwif_out.src_addr_h.addr_h.value[31:AW-32];
                cmd_inv_dst_addr    = |dst_addr[BW-1:0] ||
                                      |hwif_out.dst_addr_h.addr_h.value[31:AW-32] ||
                                     (|(64'(dst_addr) ^ key_release_addr) && (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT));
            end
        end
        else begin
            always_comb begin
                cmd_inv_src_addr    = |src_addr[BW-1:0];
                cmd_inv_dst_addr    = |dst_addr[BW-1:0] ||
                                     (|(64'(dst_addr) ^ key_release_addr) && (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT));
            end
        end
    endgenerate

    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_cmd_dec_sts       .hwset = (ctrl_fsm_ps == DMA_IDLE) && hwif_out.ctrl.go.value && cmd_parse_error;
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_axi_rd_sts        .hwset = r_req_if.resp_valid && r_req_if.resp inside {AXI_RESP_SLVERR,AXI_RESP_DECERR};
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_axi_wr_sts        .hwset = w_req_if.resp_valid && w_req_if.resp inside {AXI_RESP_SLVERR,AXI_RESP_DECERR};
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_mbox_lock_sts     .hwset = mb_lock_dropped && !mb_lock_error; // pulse to set
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_aes_cif_sts       .hwset = aes_err && aes_req_dv; // Pulse to set
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_sha_lock_sts      .hwset = 1'b0; // SHA accelerator direct-mode not enabled; sha locking should be checked by API user (i.e. FW) instead of in HW
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_fifo_oflow_sts    .hwset = (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO) &&  fifo_w_valid && !fifo_w_ready;
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_fifo_uflow_sts    .hwset = (hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO) && !fifo_r_valid &&  fifo_r_ready;
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_kv_rd_sts         .hwset = kv_read_error;
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_kv_rd_large_sts   .hwset = kv_premature_done_error;

    always_comb hwif_in.intr_block_rf.notif_internal_intr_r.notif_txn_done_sts      .hwset = ctrl_fsm_ps inside {DMA_DONE,DMA_ERROR};
    always_comb hwif_in.intr_block_rf.notif_internal_intr_r.notif_fifo_empty_sts    .hwset =  fifo_empty && !fifo_empty_r;
    always_comb hwif_in.intr_block_rf.notif_internal_intr_r.notif_fifo_not_empty_sts.hwset = !fifo_empty &&  fifo_empty_r;
    always_comb hwif_in.intr_block_rf.notif_internal_intr_r.notif_fifo_full_sts     .hwset =  fifo_full && !fifo_full_r;
    always_comb hwif_in.intr_block_rf.notif_internal_intr_r.notif_fifo_not_full_sts .hwset = !fifo_full &&  fifo_full_r;

    assign notif_intr = hwif_out.intr_block_rf.notif_global_intr_r.intr;
    assign error_intr = hwif_out.intr_block_rf.error_global_intr_r.intr;


    // --------------------------------------- //
    // Control Logic                           //
    // --------------------------------------- //

    `ifndef CALIPTRA_AXI_DMA_PAYLOAD_AVAILABLE_EDGE_DETECTION_MODE
    // Don't queue any more requests up in response to recovery_data_avail unless both:
    //  * the current request count is 0
    //  * there is no data transfer pending
    assign rd_wait_to_ack_avail = |rd_req_count_for_payload || (rd_credits < FIFO_BC/BC);

    // When block_size != 0, we are guaranteed to be interacting with the SS recovery interface
    // which means transactions will also be of FIXED burst type.
    // This guarantees that each read request will be sized according to the constraints of
    // block_size and MAX_FIXED_BLOCK_SIZE, without regard for address alignment boundaries or
    // other conditions.
    // Treat recovery_data_avail as a level signal indicating there is some data in the FIFO
    always_comb begin
        case ({rd_wait_to_ack_avail,recovery_data_avail,rd_req_hshake}) inside
            3'b000: rd_req_count_for_payload_next = rd_req_count_for_payload;
            3'b001: rd_req_count_for_payload_next = rd_req_count_for_payload - 1;
            3'b010: rd_req_count_for_payload_next = rd_req_count_for_payload + `MAX_OF(hwif_out.block_size.size.value>>$clog2(MAX_FIXED_BLOCK_SIZE),1);
            3'b011: rd_req_count_for_payload_next = '0; // If block_size != 0, we would only expect to see rd_req_hshake when rd_wait_to_ack_avail is 1
                                                        // If we see a rd_req_hshake in this case it would be erroneous, so reset the pending req count to 0
                                                        // and watch for another indicator on recovery_data_avail.
                                                        // If block_size == 0, this case might occur. E.g., while Caliptra is reading registers from the
                                                        // recovery interface in response to the initial assertion of recovery_data_avail.
                                                        // rd_req_count_for_payload is only used when block_size != 0, so hold it at a 0 value.
            3'b100: rd_req_count_for_payload_next = rd_req_count_for_payload;
            3'b101: rd_req_count_for_payload_next = rd_req_count_for_payload - 1;
            3'b110: rd_req_count_for_payload_next = rd_req_count_for_payload; // Don't queue new requests when current requests are pending
            3'b111: rd_req_count_for_payload_next = rd_req_count_for_payload - 1; // Don't queue new requests when current requests are pending
        endcase
    end

    // Requirement:
    //   * never stall read requests if block_size == 0, i.e. not using recovery mode
    //   * upon observing recovery_data_avail, request block_size bytes of data
    //   * make AXI requests one at a time
    //   * after all requests are made, stall until all data is transferred
    //   * after all data is transferred, continue stalling until recovery_data_avail
    //   * Final burst size may be less than block_size - so 'rd_req_count_for_payload' may remain non-zero
    //     until it is cleared by returning to IDLE state, although this is not a bug
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_req_count_for_payload <= '0;
            rd_req_stall             <= 1'b0;
        end
        else if (hwif_out.block_size.size.value == '0) begin
            rd_req_count_for_payload <= '0;
            rd_req_stall             <= 1'b0;
        end
        else if (ctrl_fsm_ps == DMA_IDLE) begin
            rd_req_count_for_payload <= '0;
            rd_req_stall             <= 1'b1;
        end
        else begin
            rd_req_count_for_payload <= rd_req_count_for_payload_next;
            rd_req_stall             <= ~|rd_req_count_for_payload_next || rd_req_hshake || (rd_credits < FIFO_BC/BC); // Force requests for "block_size != 0" to go out one at a time
        end
    end

    `else
    // Detect recovery_data_avail rising edge
    assign recovery_data_avail_p = recovery_data_avail && !recovery_data_avail_d;

    // When block_size != 0, we are guaranteed to be interacting with the SS recovery interface
    // which means transactions will also be of FIXED burst type.
    // This guarantees that each read request will be sized according to the constraints of
    // block_size and MAX_FIXED_BLOCK_SIZE, without regard for address alignment boundaries or
    // other conditions.
    always_comb begin
        case ({recovery_data_avail_p,rd_req_hshake}) inside
            2'b00: rd_req_count_for_payload_next = rd_req_count_for_payload;
            2'b01: rd_req_count_for_payload_next = rd_req_count_for_payload - 1;
            2'b10: rd_req_count_for_payload_next = rd_req_count_for_payload + `MAX_OF(hwif_out.block_size.size.value>>$clog2(MAX_FIXED_BLOCK_SIZE),1);
            2'b11: rd_req_count_for_payload_next = rd_req_count_for_payload + `MAX_OF(hwif_out.block_size.size.value>>$clog2(MAX_FIXED_BLOCK_SIZE),1) - 1;
        endcase
    end

    // Requirement:
    //   * never stall read requests if block_size == 0, i.e. not using recovery mode
    //   * upon observing recovery_data_avail, request block_size bytes of data
    //   * after all requests are made, stall until another rising edge on recovery_data_avail
    //   * Final burst size may be less than block_size - so 'rd_req_count_for_payload' may remain non-zero
    //     until it is cleared by returning to IDLE state
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            recovery_data_avail_d    <= 1'b0;
            rd_req_count_for_payload <= '0;
            rd_req_stall             <= 1'b0;
        end
        else if (hwif_out.block_size.size.value == '0) begin
            recovery_data_avail_d    <= 1'b0;
            rd_req_count_for_payload <= '0;
            rd_req_stall             <= 1'b0;
        end
        // Treat 'go' as the rising edge-detection if recovery_data_avail is already set before DMA is armed
        else if (ctrl_fsm_ps == DMA_IDLE) begin
            recovery_data_avail_d    <= 1'b0;
            rd_req_count_for_payload <= '0;
            rd_req_stall             <= 1'b1;
        end
        else begin
            recovery_data_avail_d    <= recovery_data_avail;
            rd_req_count_for_payload <= rd_req_count_for_payload_next;
            rd_req_stall             <= ~|rd_req_count_for_payload_next;
        end
    end

    `endif

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_resp_pending <= '0;
        end
        else if (ctrl_fsm_ps == DMA_IDLE) begin
            wr_resp_pending <= '0;
        end
        else begin
            case ({w_req_if.resp_valid,wr_req_hshake}) inside
                2'b00: wr_resp_pending <= wr_resp_pending;
                2'b01: wr_resp_pending <= wr_resp_pending + 2'b01;
                2'b10: wr_resp_pending <= wr_resp_pending - 2'b01;
                2'b11: wr_resp_pending <= wr_resp_pending;
            endcase
        end
    end

    always_comb block_size_mask = hwif_out.block_size.size.value - 1;
    always_comb begin
        rd_align_req_byte_count = (hwif_out.ctrl.rd_fixed.value && (~|hwif_out.block_size.size.value || (MAX_FIXED_BLOCK_SIZE < hwif_out.block_size.size.value))) ? AXI_LEN_BC_WIDTH'(MAX_FIXED_BLOCK_SIZE) :
                                  (hwif_out.ctrl.rd_fixed.value)                                                                                                  ? AXI_LEN_BC_WIDTH'(hwif_out.block_size.size.value) :
                                                                   (~|hwif_out.block_size.size.value || (MAX_BLOCK_SIZE       < hwif_out.block_size.size.value))  ? AXI_LEN_BC_WIDTH'(MAX_BLOCK_SIZE - r_req_if.addr[$clog2(MAX_BLOCK_SIZE)-1:0]) :
                                                                                                                                                                    AXI_LEN_BC_WIDTH'(hwif_out.block_size.size.value - (AXI_LEN_BC_WIDTH'(r_req_if.addr[$clog2(MAX_BLOCK_SIZE)-1:0]) & block_size_mask));
        rd_final_req_byte_count = rd_bytes_rem_thresh ? AXI_LEN_BC_WIDTH'(hwif_out.byte_count.count.value - rd_bytes_requested) :
                                                        {AXI_LEN_BC_WIDTH{1'b1}};
        rd_req_byte_count       = rd_final_req_byte_count < rd_align_req_byte_count ? rd_final_req_byte_count :
                                                                                      rd_align_req_byte_count;
        wr_align_req_byte_count = (hwif_out.ctrl.wr_fixed.value && (~|hwif_out.block_size.size.value || (MAX_FIXED_BLOCK_SIZE < hwif_out.block_size.size.value))) ? AXI_LEN_BC_WIDTH'(MAX_FIXED_BLOCK_SIZE) :
                                  (hwif_out.ctrl.wr_fixed.value)                                                                                                  ? AXI_LEN_BC_WIDTH'(hwif_out.block_size.size.value) :
                                                                   (~|hwif_out.block_size.size.value || (MAX_BLOCK_SIZE       < hwif_out.block_size.size.value))  ? AXI_LEN_BC_WIDTH'(MAX_BLOCK_SIZE - w_req_if.addr[$clog2(MAX_BLOCK_SIZE)-1:0]) :
                                                                                                                                                                    AXI_LEN_BC_WIDTH'(hwif_out.block_size.size.value - (AXI_LEN_BC_WIDTH'(w_req_if.addr[$clog2(MAX_BLOCK_SIZE)-1:0]) & block_size_mask));
        wr_final_req_byte_count     = wr_bytes_rem_thresh ? AXI_LEN_BC_WIDTH'(hwif_out.byte_count.count.value - wr_bytes_requested) :
                                                        {AXI_LEN_BC_WIDTH{1'b1}};
        wr_aes_ceil_req_byte_count  = hwif_out.byte_count.count.value - wr_bytes_requested > AES_FIFO_BC ? AES_FIFO_BC :
                                                                                      AXI_LEN_BC_WIDTH'(hwif_out.byte_count.count.value - wr_bytes_requested);
        wr_sel_req_byte_count       =  hwif_out.ctrl.aes_mode_en.value ? wr_aes_ceil_req_byte_count : wr_final_req_byte_count; 
        wr_req_byte_count           = wr_sel_req_byte_count < wr_align_req_byte_count ? wr_sel_req_byte_count :
                                                                                    wr_align_req_byte_count;
    end

    always_comb begin
        r_req_if.valid    = (ctrl_fsm_ps == DMA_WAIT_DATA) && !rd_req_hshake_bypass && (rd_bytes_requested < hwif_out.byte_count.count.value) && ((AXI_LEN_BC_WIDTH-BW)'(rd_credits) >= rd_req_byte_count[AXI_LEN_BC_WIDTH-1:BW]) && !rd_req_stall;
        r_req_if.addr     = src_addr + (hwif_out.ctrl.rd_fixed.value ? 0 : rd_bytes_requested);
        r_req_if.byte_len = rd_req_byte_count - AXI_LEN_BC_WIDTH'(BC);
        r_req_if.fixed    = hwif_out.ctrl.rd_fixed.value;
        r_req_if.lock     = 1'b0;

        w_req_if.valid    = (ctrl_fsm_ps == DMA_WAIT_DATA) && !wr_req_hshake_bypass && (wr_bytes_requested < hwif_out.byte_count.count.value) && ((AXI_LEN_BC_WIDTH-BW)'(wr_credits) >= wr_req_byte_count[AXI_LEN_BC_WIDTH-1:BW]);
        w_req_if.addr     = dst_addr + (hwif_out.ctrl.wr_fixed.value ? 0 : wr_bytes_requested);
        w_req_if.byte_len = wr_req_byte_count - AXI_LEN_BC_WIDTH'(BC);
        w_req_if.fixed    = hwif_out.ctrl.wr_fixed.value;
        w_req_if.lock     = 1'b0;
    end

    always_comb begin
        // rd_route_MBOX is tied to wr_bytes_requested because AXI Reads translate to Mailbox writes
        // and vice-versa for wr_route_MBOX
        mb_dv           = ctrl_fsm_ps == DMA_WAIT_DATA &&
                          ((hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX &&
                            (wr_bytes_requested < hwif_out.byte_count.count) &&
                            rd_route_valid) ||
                           (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX &&
                            (rd_bytes_requested < hwif_out.byte_count.count) &&
                            fifo_w_ready));
        mb_data.addr    = hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX ? SOC_IFC_ADDR_W'(w_req_if.addr) :
                                                                                                          SOC_IFC_ADDR_W'(r_req_if.addr);
        mb_data.wdata   = rd_route_data;
        mb_data.wstrb   = '1;
        mb_data.user    = SOC_IFC_USER_W'(0);
        mb_data.id      = '1;
        mb_data.write   = hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX;
        mb_data.soc_req = 1'b0;
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            kv_read_en <= 1'b0;
        end
        else if (!kv_read_once && 
                 hwif_out.ctrl.go.value &&
                 (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT) &&
                 (!cmd_parse_error)) begin
            kv_read_en <= 1'b1;
        end
        else if (kv_data_read_done) begin
            kv_read_en <= 1'b0;
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            kv_read_once <= 1'b0;
        end
        else if (kv_read_en) begin
            kv_read_once <= 1'b1;
        end
        else if (ctrl_fsm_ps == DMA_IDLE) begin
            kv_read_once <= 1'b0;
        end
    end

    // KeyVault Error Detection - Separate Signals for Better Observability
    always_comb begin
        // KV read operation error (existing functionality)
        kv_read_error = kv_read_en && (kv_data_error_code != KV_SUCCESS) && (ctrl_fsm_ps == DMA_WAIT_DATA);

        // KV premature completion error (new functionality)
        kv_premature_done_error = kv_data_read_done && 
                                 (ctrl_fsm_ps == DMA_WAIT_DATA) && 
                                 (rd_fifo_bytes_remaining != 32'h0);

        // Combined error signal for FSM transitions
        kv_any_error = kv_read_error || kv_premature_done_error;
    end 

    always_comb begin
        kv_read_ctrl_reg.read_en         = kv_read_en && kv_data_kv_ready;
        kv_read_ctrl_reg.pcr_hash_extend = '0;
        kv_read_ctrl_reg.read_entry      = OCP_LOCK_KEY_RELEASE_KV_SLOT;
        kv_read_ctrl_reg.rsvd            = '0;
    end

    always_comb begin
        rd_req_hshake        = r_req_if.valid && r_req_if.ready;
        wr_req_hshake        = w_req_if.valid && w_req_if.ready;
        rd_req_hshake_bypass = hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE;
        wr_req_hshake_bypass = hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE;
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_bytes_requested  <= '0;
            rd_bytes_rem_thresh <= 1'b0;
        end
        else if (rd_req_hshake) begin
            rd_bytes_requested  <= rd_bytes_requested + rd_req_byte_count;
            rd_bytes_rem_thresh <= ~|((hwif_out.byte_count.count.value - (rd_bytes_requested + rd_req_byte_count)) >> AXI_LEN_BC_WIDTH);
        end
        else if (mb_dv && !mb_data.write && !mb_hold) begin
            rd_bytes_requested  <= rd_bytes_requested + BC;
            rd_bytes_rem_thresh <= ~|((hwif_out.byte_count.count.value - (rd_bytes_requested + BC)) >> AXI_LEN_BC_WIDTH);
        end
        else if (ctrl_fsm_ps == DMA_IDLE) begin
            rd_bytes_requested  <= '0;
            rd_bytes_rem_thresh <= ~|hwif_out.byte_count.count.value[31:AXI_LEN_BC_WIDTH];
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_bytes_requested  <= '0;
            wr_bytes_rem_thresh <= 1'b0;
        end
        else if (wr_req_hshake) begin
            wr_bytes_requested  <= wr_bytes_requested + wr_req_byte_count;
            wr_bytes_rem_thresh <= ~|((hwif_out.byte_count.count.value - (wr_bytes_requested + wr_req_byte_count)) >> AXI_LEN_BC_WIDTH);
        end
        else if (mb_dv && mb_data.write && !mb_hold) begin
            wr_bytes_requested  <= wr_bytes_requested + BC;
            wr_bytes_rem_thresh <= ~|((hwif_out.byte_count.count.value - (wr_bytes_requested + BC)) >> AXI_LEN_BC_WIDTH);
        end
        else if (hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO && hwif_out.read_data.rdata.swacc) begin
            wr_bytes_requested  <= wr_bytes_requested + BC;
            wr_bytes_rem_thresh <= ~|((hwif_out.byte_count.count.value - (wr_bytes_requested + BC)) >> AXI_LEN_BC_WIDTH);
        end
        else if (ctrl_fsm_ps == DMA_IDLE) begin
            wr_bytes_requested  <= '0;
            wr_bytes_rem_thresh <= ~|hwif_out.byte_count.count.value[31:AXI_LEN_BC_WIDTH];
        end
    end

    // Read credits logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_credits <= FIFO_BC/BC;
        end
        else if ((ctrl_fsm_ps == DMA_IDLE) || (rd_req_hshake_bypass)) begin
            rd_credits <= FIFO_BC/BC;
        end
        // Request byte count is restricted to not exceed the credit capacity
        // Assertions (below) enforce a legal byte_count for sims
        else if (rd_req_hshake && (fifo_r_valid && fifo_r_ready)) begin
            rd_credits <= rd_credits + 1 - FIFO_BW'(rd_req_byte_count[AXI_LEN_BC_WIDTH-1:BW]);
        end
        else if (rd_req_hshake) begin
            rd_credits <= rd_credits - FIFO_BW'(rd_req_byte_count[AXI_LEN_BC_WIDTH-1:BW]);
        end
        else if (fifo_r_valid && fifo_r_ready) begin
            rd_credits <= rd_credits + 1;
        end
    end
    
    // Write credits logic
    assign wr_credits_fifo_w_valid = hwif_out.ctrl.aes_mode_en.value ? aes_fifo_w_valid: fifo_w_valid;
    assign wr_credits_fifo_w_ready = hwif_out.ctrl.aes_mode_en.value ? aes_fifo_w_ready: fifo_w_ready;


    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_credits <= 0;
        end
        else if ((ctrl_fsm_ps == DMA_IDLE) || (wr_req_hshake_bypass)) begin
            wr_credits <= 0;
        end
        // Request byte count is restricted to not exceed the credit capacity
        // Assertions (below) enforce a legal byte_count for sims
        else if (wr_req_hshake && (wr_credits_fifo_w_valid && wr_credits_fifo_w_ready)) begin
            wr_credits <= wr_credits + 1 - FIFO_BW'(wr_req_byte_count[AXI_LEN_BC_WIDTH-1:BW]);
        end
        else if (wr_req_hshake) begin
            wr_credits <= wr_credits - FIFO_BW'(wr_req_byte_count[AXI_LEN_BC_WIDTH-1:BW]);
        end
        else if (wr_credits_fifo_w_valid && wr_credits_fifo_w_ready) begin
            wr_credits <= wr_credits + 1;
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bytes_remaining <= '0;
        end
        else if (ctrl_fsm_ps == DMA_IDLE && hwif_out.ctrl.go.value) begin
            bytes_remaining <= hwif_out.byte_count.count;
        end
        else if (fifo_r_valid && fifo_r_ready) begin
            bytes_remaining <= bytes_remaining - BC;
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_fifo_bytes_remaining <= '0;
        end
        else if (ctrl_fsm_ps == DMA_IDLE && hwif_out.ctrl.go.value) begin
            rd_fifo_bytes_remaining <= hwif_out.byte_count.count;
        end
        else if (fifo_w_valid && fifo_w_ready) begin
            rd_fifo_bytes_remaining <= rd_fifo_bytes_remaining - BC;
        end
    end

    always_comb begin
        if (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO) begin
            fifo_w_data  = req_data.wdata;
            fifo_w_valid = hwif_out.write_data.wdata.swmod;
        end
        else if (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX) begin
            fifo_w_data  = mb_rdata;
            fifo_w_valid = mb_dv && !mb_hold;
        end
        else if (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT) begin
            fifo_w_data  = kv_data_write_data;
            fifo_w_valid = kv_data_write_en && |(rd_fifo_bytes_remaining); // FIXME no backpressure on this signal, FIFO must accept every assertion
        end
        else begin
            fifo_w_data  = r_data_i;
            fifo_w_valid = r_valid_i;
        end
        r_ready_o = fifo_w_ready;
    end

    ////////////////////////////////////////////////////
    // FIFO -> Read Route
    ////////////////////////////////////////////////////
    assign rd_route_data = hwif_out.ctrl.aes_mode_en.value ? aes_fsm_rd_route_data: fifo_r_data;
    assign rd_route_valid = hwif_out.ctrl.aes_mode_en.value ? aes_fsm_rd_route_valid: fifo_r_valid;

    ////////////////////////////////////////////////////
    // Read Route -> FIFO
    ////////////////////////////////////////////////////
    assign  fifo_r_ready = hwif_out.ctrl.aes_mode_en.value ? aes_fsm_rd_route_ready: rd_route_ready;

    always_comb begin
        
        if (hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX) begin
            rd_route_ready = !mb_hold;
        end
        else if (hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO) begin
            rd_route_ready = hwif_out.read_data.rdata.swacc;
        end
        else begin
            rd_route_ready = w_ready_i;
        end
    end

    ////////////////////////////////////////////////////
    // Read Route -> AXI
    ////////////////////////////////////////////////////
    assign w_valid_o = rd_route_valid;
    assign w_data_o  = rd_route_data;

    ////////////////////////////////////////////////////
    // Read Route -> AHB
    ////////////////////////////////////////////////////
    always_comb r_data_mask = {DW{hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO}};
    always_comb hwif_in.read_data.rdata.next = rd_route_data & r_data_mask;


    // Runtime Errors
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi_error <= 1'b0;
        end
        else if (ctrl_fsm_ps == DMA_IDLE || hwif_out.ctrl.flush.value) begin
            axi_error <= 1'b0;
        end
        else if (r_req_if.resp_valid) begin
            axi_error <= axi_error | (r_req_if.resp inside {AXI_RESP_SLVERR,AXI_RESP_DECERR});
        end
        else if (w_req_if.resp_valid) begin
            axi_error <= axi_error | (w_req_if.resp inside {AXI_RESP_SLVERR,AXI_RESP_DECERR});
        end
    end

    always_comb mb_lock_dropped = ctrl_fsm_ps == DMA_WAIT_DATA &&
                                  ((hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX) ||
                                   (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX)) &&
                                  !mbox_lock;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mb_lock_error <= 1'b0;
        end
        else if (ctrl_fsm_ps == DMA_IDLE || hwif_out.ctrl.flush.value) begin
            mb_lock_error <= 1'b0;
        end
        else if (mb_lock_dropped) begin
            mb_lock_error <= mb_lock_error | 1'b1;
        end
    end
    
    // --------------------------------------- //
    // AES FSM                                 //
    // --------------------------------------- //
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            aes_fsm_ps <= AES_IDLE;
            aes_init_done <= '0;
            aes_to_axi_last_transfer <= '0;
        end else begin
            aes_fsm_ps    <= aes_fsm_ns;
            aes_init_done <= aes_init_done_next;
            aes_to_axi_last_transfer <= aes_to_axi_last_transfer_next;
        end
    end
    
    // AES FSM next-state logic
    always_comb begin
        aes_fsm_ns = aes_fsm_ps;
        aes_init_done_next = aes_init_done;
        aes_to_axi_last_transfer_next = aes_to_axi_last_transfer;
        case (aes_fsm_ps)
            AES_IDLE: begin
                // Start condition (add your own trigger)
                if (start_aes_fsm) begin
                    aes_fsm_ns = AES_WAIT_INPUT_READY;
                end
                aes_init_done_next = 1'b0;
                aes_to_axi_last_transfer_next = 1'b0;
            end
            AES_WAIT_INPUT_READY: begin
                if (aes_input_ready) begin
                    if((!aes_init_done || bytes_remaining < 16) && hwif_out.ctrl.aes_gcm_mode.value) begin
                        aes_fsm_ns = AES_WAIT_IDLE;
                    end
                    else begin
                        aes_fsm_ns = AES_WRITE_BLOCK;
                    end
                end
            end
            AES_WAIT_IDLE: begin
                if(aes_status_idle) begin
                    aes_fsm_ns = AES_UPDATE_BYTE_COUNT;
                end
            end
            AES_UPDATE_BYTE_COUNT: begin
                // After writing CCM_SHAOWED register twice
                if (aes_cif_update_byte_count_done) begin
                    aes_fsm_ns = AES_WRITE_BLOCK;
                end
            end
            AES_WRITE_BLOCK: begin
                // After writing 4 words
                if (aes_cif_write_block_done) begin
                    aes_init_done_next = 1'b1;
                    // If transfer is > 4 DWORDs we need to push 
                    // more content into AES before we start
                    // reading data out.
                    if (!aes_init_done && (bytes_remaining > 0)) begin
                        aes_fsm_ns = AES_WAIT_INPUT_READY;
                    end else begin
                        // If the transfer is =< 4DWORDs the "init" transfer
                        // is the last transfer and we need to indicate
                        // to AES_READ_OUTPUT this is the last transfer.
                        if(!aes_init_done && (bytes_remaining == 0)) begin
                            aes_to_axi_last_transfer_next = 1'b1;
                        end
                        aes_fsm_ns = AES_WAIT_OUTPUT_VALID;
                    end
                end
            end
            AES_WAIT_OUTPUT_VALID: begin
                if (aes_output_valid) begin
                    aes_fsm_ns = AES_READ_OUTPUT;
                end
            end
            AES_READ_OUTPUT: begin
                if (aes_cif_read_block_done) begin
                    // Final transfer and read out of AES is done so go into
                    // AES_ERROR or AES_DONE state
                    if (aes_to_axi_last_transfer) begin
                        if(aes_error) begin
                            aes_fsm_ns = AES_ERROR;
                        end else begin
                            aes_fsm_ns = AES_DONE;
                        end
                    end
                    // At this point we have transerted all data into 
                    // AES but we still have one more block to read out of 
                    // AES that we "buffered" into the AES on the first set of 
                    // writes into AES. This allows us to read that last bit
                    // of data out of AES and the next time around we will
                    // transition into AES_ERROR or AES_DONE. This only
                    // happens when the size of the transfer is > 4 DWORDs
                    // anything smaller and there is not buffering of data
                    // since the payload is too small.
                    else if(bytes_remaining == '0) begin 
                        aes_to_axi_last_transfer_next = 1'b1;
                        aes_fsm_ns = AES_WAIT_OUTPUT_VALID;
                    end
                    // When we are at the last block of data transfered into
                    // the AES we need to update the byte count in the AES if
                    // we are in GCM mode. 
                    else if(bytes_remaining > 0 && bytes_remaining < 16 && hwif_out.ctrl.aes_gcm_mode.value) begin
                        aes_fsm_ns = AES_WAIT_IDLE;
                    end
                    // Typical transfer into AES is done and we are streaming
                    // another 4 DWORDs into the AES.
                    else begin
                        aes_fsm_ns = AES_WRITE_BLOCK;
                    end
                end
            end
            AES_DONE: begin
                aes_fsm_ns = AES_IDLE;
            end
            AES_ERROR: begin
                if (hwif_out.ctrl.flush.value) begin
                    aes_fsm_ns = AES_IDLE;
                end
            end
            default: aes_fsm_ns = AES_IDLE;
        endcase
    end

    // --------------------------------------- //
    // AES Control Logic                       //
    // --------------------------------------- //
    
    // AES CIF read counter and done logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            aes_cif_read_cnt <= '0;
        end else begin
            aes_cif_read_cnt  <= aes_cif_read_cnt_next;
        end
    end
    
    // Count when detecting a CIF read
    assign aes_cif_read_cnt_incr = !aes_req_hold && aes_req_dv & !aes_req_data.write; 

    always_comb begin
        aes_cif_read_cnt_next = aes_cif_read_cnt;
        if (aes_cif_read_cnt_incr) begin
            aes_cif_read_cnt_next = aes_cif_read_cnt + 1;
        end
        else if (aes_fsm_ps != AES_READ_OUTPUT) begin
            aes_cif_read_cnt_next = '0;
        end
    end

    // Once we have read all 4 output rgisters indicate reading is done 
    // If not all 4 DWORDs contain data the data is blocked from going 
    // into the FIFO, but we always read 4 DWORDS from the AES
    assign aes_cif_read_block_done = (aes_cif_read_cnt == 2'd3) && aes_cif_read_cnt_incr;
    


    // AES write block counter
    assign aes_cif_write_cnt_incr = aes_req_dv & !aes_req_hold & aes_req_data.write;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            aes_cif_write_cnt        <= '0;
        end else begin
            aes_cif_write_cnt        <= aes_cif_write_cnt_next;
        end
    end


    // When switching states reset or when we are not in a known writing state
    // reset the write counter 
    assign aes_cif_write_cnt_reset = (aes_fsm_ps != aes_fsm_ns) || 
                                        ((aes_fsm_ps != AES_WRITE_BLOCK) && (aes_fsm_ps != AES_UPDATE_BYTE_COUNT));

    always_comb begin
        aes_cif_write_cnt_next        = aes_cif_write_cnt;
        if (aes_cif_write_cnt_reset) begin
            aes_cif_write_cnt_next = '0;
        end else if (aes_cif_write_cnt_incr) begin
            aes_cif_write_cnt_next = aes_cif_write_cnt + 1'b1;
        end
    end
    
    // AES Byte update is just a single write. Once write is done we are done in this phase
    assign aes_cif_update_byte_count_done = (aes_cif_write_cnt == 2'd1) && aes_cif_write_cnt_incr;

    // AES CIF write block done logic
    assign aes_cif_write_block_done = (aes_cif_write_cnt == 2'd3) && aes_cif_write_cnt_incr;


    // Latch AES request signals if aes_req_hold is asserted
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            aes_req_dv_q             <= 1'b0;
        end else begin
            aes_req_dv_q             <= aes_req_dv;
        end
    end
    // AES CIF DV Control
    always_comb begin
        aes_req_dv = aes_req_dv_q;
        if (aes_fsm_ps == AES_WRITE_BLOCK) begin
            if (bytes_remaining > 0) begin
                if(fifo_r_valid) begin
                    aes_req_dv = 1'b1;
                end
                else if (!fifo_r_valid && !aes_req_wait) begin
                    aes_req_dv = 1'b0; // No data available, do not assert request
                end
            end
            else begin
                aes_req_dv = 1'b1;
            end
        end else if(aes_fsm_ps == AES_UPDATE_BYTE_COUNT) begin
            aes_req_dv = 1'b1;
        end else if(aes_fsm_ps == AES_READ_OUTPUT && !aes_fifo_full) begin
            aes_req_dv = 1'b1;
        end
        else begin
            aes_req_dv = 1'b0; // Not in write block state, do not assert request
        end
    end
    
    // AES CIF Data Control
    always_comb begin
        aes_req_data = '0; // Default to zero

        // AES CIF same on read/write non-zero values
        aes_req_data.id      = '1;
        
        if (aes_fsm_ps == AES_WRITE_BLOCK) begin
            // AES CIF Write Assignments
            aes_req_data.addr    = 19'((`AES_REG_DATA_IN_0 + (aes_cif_write_cnt * BC))) ;
            aes_req_data.wstrb   = '1;
            aes_req_data.write   = 1'b1;
            aes_req_data.wdata   = (bytes_remaining > 32'h0) ? fifo_r_data : '0; // Default to 0s
        end else if(aes_fsm_ps == AES_UPDATE_BYTE_COUNT) begin
            // AES CIF Update Byte Count Assignments
            aes_req_data.addr    = `AES_REG_CTRL_GCM_SHADOWED;
            aes_req_data.wstrb   = '1;
            aes_req_data.write   = 1'b1;
            aes_req_data.wdata = (((bytes_remaining > 32'd16 ? 32'd16 : bytes_remaining ) << `AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_LOW) & `AES_REG_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_MASK) |
                     ((6'h8 << `AES_REG_CTRL_GCM_SHADOWED_PHASE_LOW) & `AES_REG_CTRL_GCM_SHADOWED_PHASE_MASK);
        end else if(aes_fsm_ps == AES_READ_OUTPUT) begin
            // AES CIF Read Assignments
            aes_req_data.addr    = 19'((`AES_REG_DATA_OUT_0 + (aes_cif_read_cnt * BC)));
            aes_req_data.write   = 1'b0;
            aes_req_data.wdata   = '0; // Default to 0s
        end
    end


    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            aes_req_wait <= 1'b0;
        end else begin
            aes_req_wait <= aes_req_wait_next;
        end
    end
    always_comb begin
        // Track if we are waiting for hold to clear
        aes_req_wait_next = (aes_req_dv && aes_req_hold);
    end
    
    // Pulling data off main fifo when we initiate the CIF transaction.
    // Assumption is that AES has their aes_req_hold asserted when DMA asserts
    // aes_req_dv first clock cycle of a transaction to AES
    assign aes_fsm_rd_route_ready = (fifo_r_valid && aes_req_dv && !aes_req_wait && aes_fsm_ps == AES_WRITE_BLOCK);


    assign start_aes_fsm = (ctrl_fsm_ps == DMA_IDLE) && (hwif_out.ctrl.go.value) && !cmd_parse_error && hwif_out.ctrl.aes_mode_en.value;


    
    
    // AES error detect logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            aes_error <= 1'b0;
        end
        else if (ctrl_fsm_ps == DMA_IDLE || hwif_out.ctrl.flush.value) begin
            aes_error <= 1'b0;
        end
        else if (aes_err && aes_req_dv) begin
            aes_error <= 1'b1;
        end
    end

    // --------------------------------------- //
    // KeyVault Read Client                    //
    // --------------------------------------- //
    always_comb begin
        kv_read_metrics.ocp_lock_in_progress = ocp_lock_in_progress;
        kv_read_metrics.kv_read_dest         = KV_NUM_READ'(1<<KV_DEST_IDX_DMA_DATA);
        kv_read_metrics.kv_key_entry         = kv_read_ctrl_reg.read_entry;
    end

    //Read Key (as data)
    kv_read_client #(
        .DATA_WIDTH(OCP_LOCK_MEK_NUM_DWORDS*32), // NOTE: key_release_size does not override this! But we only transfer FIFO contents in specified DW count to endpoint. This is a static size for KV reads.
        .PAD(0)
    )
    dma_data_kv_read
    (
        .clk    (clk        ),
        .rst_b  (rst_n      ),
        .zeroize(ctrl_fsm_ps == DMA_IDLE || hwif_out.ctrl.flush.value || debugUnlock_or_scan_mode_switch),

        //client control register
        .read_ctrl_reg(kv_read_ctrl_reg),

        //access filtering rule metrics
        .read_metrics(kv_read_metrics),

        //interface with kv
        .kv_read(kv_read),
        .kv_resp(kv_rd_resp),

        //interface with client
        .write_en    (kv_data_write_en    ),
        .write_offset(/*kv_data_write_offset*/), // TODO use this?
        .write_data  (kv_data_write_data  ),

        .error_code(kv_data_error_code),
        .kv_ready  (kv_data_kv_ready  ),
        .read_done (kv_data_read_done )
    );

    // --------------------------------------- //
    // Data FIFO                               //
    // --------------------------------------- //
    caliptra_prim_fifo_sync #(
      .Width            (DW  ),
      .Pass             (1'b0), // if == 1 allow requests to pass through empty FIFO
      .Depth            (FIFO_BC/BC),
      .OutputZeroIfEmpty(1'b1), // if == 1 always output 0 when FIFO is empty
      .resetOnClear     (1), // Reset FIFO when clr_i set
      .Secure           (1'b0)  // use prim count for pointers; no secret data transmitted via DMA on AXI, no hardened counters
    ) i_fifo (
      .clk_i   (clk     ),
      .rst_ni  (rst_n   ),
      // synchronous clear / flush port
      .clr_i   (ctrl_fsm_ps == DMA_IDLE), // TODO clear with debugUnlock_or_scan_mode_switch while allowing AXI to end gracefully?
      // write port
      .wvalid_i(fifo_w_valid  ),
      .wready_o(fifo_w_ready  ),
      .wdata_i (fifo_w_data   ),
      // read port
      .rvalid_o(fifo_r_valid),
      .rready_i(fifo_r_ready),
      .rdata_o (fifo_r_data ),
      // occupancy
      .full_o  (fifo_full ),
      .depth_o (fifo_depth),
      .err_o   (          )
    );

    always_comb fifo_empty = fifo_depth == 0;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            fifo_full_r  <= 1'b0;
            fifo_empty_r <= 1'b1;
        end
        else begin
            fifo_full_r  <= fifo_full;
            fifo_empty_r <= fifo_empty;
        end
    end
    
    // --------------------------------------- //
    // AES FIFO                                //
    // --------------------------------------- //
    caliptra_prim_fifo_sync #(
      .Width            (DW  ),
      .Pass             (1'b0), // if == 1 allow requests to pass through empty FIFO
      .Depth             (AES_FIFO_BC/BC),
      .OutputZeroIfEmpty(1'b1), // if == 1 always output 0 when FIFO is empty
      .resetOnClear     (1), // Reset FIFO when clr_i set
      .Secure           (1'b0)  // use prim count for pointers; no secret data transmitted via DMA on AXI, no hardened counters
    ) i_aes_fifo (
      .clk_i   (clk     ),
      .rst_ni  (rst_n   ),
      // synchronous clear / flush port
      .clr_i   (ctrl_fsm_ps == DMA_IDLE), 
      // write port
      .wvalid_i(aes_fifo_w_valid  ),
      .wready_o(aes_fifo_w_ready  ),
      .wdata_i (aes_fifo_w_data   ),
      // read port
      .rvalid_o(aes_fifo_r_valid),
      .rready_i(aes_fifo_r_ready),
      .rdata_o (aes_fifo_r_data ),
      // occupancy
      .full_o  (aes_fifo_full ),
      .depth_o (aes_fifo_depth),
      .err_o   (          )
    );
    logic [31:0] aes_fifo_bytes_written;

    assign aes_fifo_empty = aes_fifo_depth == 0;
    assign aes_fifo_w_valid = aes_cif_read_cnt_incr && aes_fifo_bytes_written < hwif_out.byte_count.count;
    assign aes_fifo_w_data  = aes_rdata; 

    assign aes_fifo_r_ready = hwif_out.ctrl.aes_mode_en.value && w_ready_i;
    assign aes_fsm_rd_route_data = aes_fifo_r_data;
    assign aes_fsm_rd_route_valid = aes_fifo_r_valid;


    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            aes_fifo_bytes_written <= '0;
        end else if (aes_cif_read_cnt_incr) begin
            aes_fifo_bytes_written <= aes_fifo_bytes_written + BC;
        end else if (aes_fsm_ps == AES_IDLE) begin
            aes_fifo_bytes_written <= '0;
        end
    end

    // Requests must have valid length
    `CALIPTRA_ASSERT(AXI_DMA_VLD_RD_REQ_LEN, rd_req_hshake |-> r_req_if.byte_len < MAX_BLOCK_SIZE, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_VLD_WR_REQ_LEN, wr_req_hshake |-> w_req_if.byte_len < MAX_BLOCK_SIZE, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_VLD_FIXED_RD_REQ_LEN, rd_req_hshake && r_req_if.fixed |-> r_req_if.byte_len < MAX_FIXED_BLOCK_SIZE, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_VLD_FIXED_WR_REQ_LEN, wr_req_hshake && w_req_if.fixed |-> w_req_if.byte_len < MAX_FIXED_BLOCK_SIZE, clk, !rst_n)
    // Requests must not cross AXI boundary (4KiB)
    `CALIPTRA_ASSERT(AXI_DMA_VLD_RD_REQ_BND, rd_req_hshake && !r_req_if.fixed |-> r_req_if.addr[AW-1:AXI_LEN_BC_WIDTH] == ((r_req_if.addr + r_req_if.byte_len) >> AXI_LEN_BC_WIDTH), clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_VLD_WR_REQ_BND, wr_req_hshake && !w_req_if.fixed |-> w_req_if.addr[AW-1:AXI_LEN_BC_WIDTH] == ((w_req_if.addr + w_req_if.byte_len) >> AXI_LEN_BC_WIDTH), clk, !rst_n)
    // Proper configuration
    `CALIPTRA_ASSERT_INIT(AXI_DMA_DW_32, DW == 32)
    `CALIPTRA_ASSERT_INIT(AXI_DMA_DW_EQ_MB, DW == CPTRA_MBOX_DATA_W)
    // FIFO must have space for all requested data
    `CALIPTRA_ASSERT(AXI_DMA_LIM_RD_CRED, rd_credits <= FIFO_BC/BC, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_OFL_RD_CRED, rd_req_hshake |-> rd_req_byte_count <= FIFO_BC, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_MIN_RD_CRED, !((rd_credits < 1) && rd_req_hshake), clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_RST_RD_CRED, (ctrl_fsm_ps == DMA_DONE) |-> (rd_credits == FIFO_BC/BC), clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_LIM_WR_CRED, wr_credits <= FIFO_BC/BC, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_UFL_WR_CRED, wr_req_hshake |-> wr_credits >= wr_req_byte_count[AXI_LEN_BC_WIDTH-1:BW], clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_MIN_WR_CRED, !((wr_credits < 1) && wr_req_hshake), clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_RST_WR_CRED, (ctrl_fsm_ps == DMA_DONE) |-> (wr_credits == 0), clk, !rst_n)
    // AES FSM sync with DMA FSM
    `CALIPTRA_ASSERT(AXI_DMA_AES_FSM_DONE_SYNC,    (ctrl_fsm_ps == DMA_DONE && hwif_out.ctrl.aes_mode_en.value) |-> (aes_fsm_ps == AES_DONE || aes_fsm_ps == AES_IDLE), clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_AES_FSM_ERR_SYNC,     (ctrl_fsm_ps == DMA_ERROR && hwif_out.ctrl.aes_mode_en.value && !cmd_parse_error) |-> (aes_fsm_ps == AES_ERROR), clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_AES_FSM_IDLE_SYNC,    (aes_fsm_ps != AES_IDLE) |-> (ctrl_fsm_ps != DMA_IDLE), clk, !rst_n)
    // AES FIFO ensure no underflow/overflow
    `CALIPTRA_ASSERT(AXI_DMA_AES_FIFO_WRITE_VALID, (aes_fifo_w_valid) |-> (aes_fifo_w_ready), clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_AES_FIFO_WRITE_NOT_FULL, (aes_fifo_w_valid) |-> (!aes_fifo_full), clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_AES_FIFO_READ_VALID, (aes_fifo_r_ready) |-> (aes_fifo_r_valid), clk, !rst_n)


endmodule
