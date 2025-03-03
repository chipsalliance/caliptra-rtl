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

    // Mailbox SRAM INF
    output logic             mb_dv,
    input  logic             mb_hold,
    input  logic             mb_error,
    output var soc_ifc_req_t mb_data,
    input  logic [DW-1:0]    mb_rdata,

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

    logic rd_req_hshake, rd_req_hshake_bypass;
    logic wr_req_hshake, wr_req_hshake_bypass;
    // Count read requests that have been enqueued due to recovery_data_avail.
    // Width of signal is sufficient to track 2x the maximum number of requests
    // possible for any given "block" of data.
    // This allows the counter to schedule the next set of requests if
    // recovery_data_avail pulse is observed while there are still requests
    // that have not been issued from the prior pulse.
    // The maximum number of requests for a given "block" is calculated as:
    //   max_block_size / min_size_per_request
    // Where
    //   max_block_size = AXI_LEN_MAX_BYTES
    //   min_size_per_request = BC
    logic [AXI_LEN_BC_WIDTH-BW:0] rd_req_count_for_payload, rd_req_count_for_payload_next;
    logic rd_req_stall;
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
    logic [AXI_LEN_BC_WIDTH-1:0] wr_final_req_byte_count; // byte-count in the final request, which may be smaller than a typical request
    logic [AXI_LEN_BC_WIDTH-1:0] wr_req_byte_count;       // byte-count calculated for the current read request

    logic [31:0] bytes_remaining; // Decrements with arrival of beat at DESTINATION.
    logic axi_error;
    logic mb_lock_dropped, mb_lock_error;

    logic recovery_data_avail_d, recovery_data_avail_p;


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
                if ((bytes_remaining == 0) && (wr_resp_pending == 0) && (axi_error || mb_lock_error)) begin
                    ctrl_fsm_ns = DMA_ERROR;
                end
                else if ((bytes_remaining == 0) && (wr_resp_pending == 0)) begin
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
    always_comb hwif_in.status0.payload_available.next = recovery_data_avail;
    always_comb hwif_in.status0.image_activated.next   = recovery_image_activated;
    always_comb hwif_in.status1.bytes_remaining.next   = bytes_remaining;


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
        cmd_inv_wr_route    = 1'b0; // There are no unassigned values from the 2-bit field, all individual configs are legal
        // Some COMBINATIONS of routes are disallowed
        case({hwif_out.ctrl.rd_route.value,hwif_out.ctrl.wr_route.value}) inside
            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE)}:    cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX)}:       cmd_inv_route_combo = 0;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO)}:   cmd_inv_route_combo = 0;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD)}:     cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE)}:    cmd_inv_route_combo = 0;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX)}:       cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO)}:   cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD)}:     cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE)}:    cmd_inv_route_combo = 0;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX)}:       cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO)}:   cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD)}:     cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE)}:    cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX)}:       cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO)}:   cmd_inv_route_combo = 1;

            {2'(axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR),
             2'(axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD)}:     cmd_inv_route_combo = 0;
        endcase
        cmd_inv_byte_count  = |hwif_out.byte_count.count.value[BW-1:0] ||
                              ~|hwif_out.byte_count.count.value ||
                              (hwif_out.byte_count.count.value > DMA_MAX_XFER_SIZE) ||
                              (hwif_out.byte_count.count.value > CPTRA_MBOX_SIZE_BYTES &&
                               ((hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX) ||
                                (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX)));
        // power of 2 and word-aligned
        cmd_inv_block_size  = |(hwif_out.block_size.size.value & (hwif_out.block_size.size.value-1)) ||
                              |hwif_out.block_size.size.value[BW-1:0];
        cmd_inv_rd_fixed    = hwif_out.ctrl.rd_fixed.value && hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE;
        cmd_inv_wr_fixed    = hwif_out.ctrl.wr_fixed.value && hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE;
        cmd_inv_mbox_lock   = !mbox_lock && ((hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX) || (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX));
        cmd_inv_sha_lock    = !sha_lock && (1'b0/*addr decode? NOTE: Direct-access to sha accelerator not implemented. Disable this check.*/);
        cmd_parse_error     = cmd_inv_rd_route    ||
                              cmd_inv_wr_route    ||
                              cmd_inv_route_combo ||
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
        if (AW < 32) begin
            always_comb begin
                cmd_inv_src_addr    = |src_addr[BW-1:0] ||
                                      |hwif_out.src_addr_l.addr_l.value[31:AW] ||
                                      |hwif_out.src_addr_h.addr_h.value;
                cmd_inv_dst_addr    = |dst_addr[BW-1:0] ||
                                      |hwif_out.dst_addr_l.addr_l.value[31:AW] ||
                                      |hwif_out.dst_addr_h.addr_h.value;
            end
        end
        else if (AW < 64) begin
            always_comb begin
                cmd_inv_src_addr    = |src_addr[BW-1:0] ||
                                      |hwif_out.src_addr_h.addr_h.value[31:AW-32];
                cmd_inv_dst_addr    = |dst_addr[BW-1:0] ||
                                      |hwif_out.dst_addr_h.addr_h.value[31:AW-32];
            end
        end
        else begin
            always_comb begin
                cmd_inv_src_addr    = |src_addr[BW-1:0];
                cmd_inv_dst_addr    = |dst_addr[BW-1:0];
            end
        end
    endgenerate

    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_cmd_dec_sts       .hwset = (ctrl_fsm_ps == DMA_IDLE) && hwif_out.ctrl.go.value && cmd_parse_error;
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_axi_rd_sts        .hwset = r_req_if.resp_valid && r_req_if.resp inside {AXI_RESP_SLVERR,AXI_RESP_DECERR};
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_axi_wr_sts        .hwset = w_req_if.resp_valid && w_req_if.resp inside {AXI_RESP_SLVERR,AXI_RESP_DECERR};
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_mbox_lock_sts     .hwset = mb_lock_dropped && !mb_lock_error; // pulse to set
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_sha_lock_sts      .hwset = 1'b0; // SHA accelerator direct-mode not enabled; sha locking should be checked by API user (i.e. FW) instead of in HW
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_fifo_oflow_sts    .hwset = (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO) &&  fifo_w_valid && !fifo_w_ready;
    always_comb hwif_in.intr_block_rf.error_internal_intr_r.error_fifo_uflow_sts    .hwset = (hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO) && !fifo_r_valid &&  fifo_r_ready;

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
        wr_final_req_byte_count = wr_bytes_rem_thresh ? AXI_LEN_BC_WIDTH'(hwif_out.byte_count.count.value - wr_bytes_requested) :
                                                        {AXI_LEN_BC_WIDTH{1'b1}};
        wr_req_byte_count       = wr_final_req_byte_count < wr_align_req_byte_count ? wr_final_req_byte_count :
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
                            fifo_r_valid) ||
                           (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX &&
                            (rd_bytes_requested < hwif_out.byte_count.count) &&
                            fifo_w_ready));
        mb_data.addr    = hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX ? SOC_IFC_ADDR_W'(w_req_if.addr) :
                                                                                                          SOC_IFC_ADDR_W'(r_req_if.addr);
        mb_data.wdata   = fifo_r_data;
        mb_data.wstrb   = '1;
        mb_data.id      = '1;
        mb_data.write   = hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX;
        mb_data.soc_req = 1'b0;
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
        else if (ctrl_fsm_ps == DMA_IDLE) begin
            wr_bytes_requested  <= '0;
            wr_bytes_rem_thresh <= ~|hwif_out.byte_count.count.value[31:AXI_LEN_BC_WIDTH];
        end
    end

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

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_credits <= 0;
        end
        else if ((ctrl_fsm_ps == DMA_IDLE) || (wr_req_hshake_bypass)) begin
            wr_credits <= 0;
        end
        // Request byte count is restricted to not exceed the credit capacity
        // Assertions (below) enforce a legal byte_count for sims
        else if (wr_req_hshake && (fifo_w_valid && fifo_w_ready)) begin
            wr_credits <= wr_credits + 1 - FIFO_BW'(wr_req_byte_count[AXI_LEN_BC_WIDTH-1:BW]);
        end
        else if (wr_req_hshake) begin
            wr_credits <= wr_credits - FIFO_BW'(wr_req_byte_count[AXI_LEN_BC_WIDTH-1:BW]);
        end
        else if (fifo_w_valid && fifo_w_ready) begin
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

    always_comb begin
        if (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO) begin
            fifo_w_data  = req_data.wdata;
            fifo_w_valid = hwif_out.write_data.wdata.swmod;
        end
        else if (hwif_out.ctrl.wr_route.value == axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX) begin
            fifo_w_data  = mb_rdata;
            fifo_w_valid = mb_dv && !mb_hold;
        end
        else begin
            fifo_w_data  = r_data_i;
            fifo_w_valid = r_valid_i;
        end
        r_ready_o = fifo_w_ready;
    end

    always_comb begin
        if (hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX) begin
            fifo_r_ready = !mb_hold;
        end
        else if (hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO) begin
            fifo_r_ready = hwif_out.read_data.rdata.swacc;
        end
        else begin
            fifo_r_ready = w_ready_i;
        end
        w_valid_o = fifo_r_valid;
        w_data_o  = fifo_r_data;
    end

    always_comb r_data_mask = {DW{hwif_out.ctrl.rd_route.value == axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO}};
    always_comb hwif_in.read_data.rdata.next = fifo_r_data & r_data_mask;

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
    // Data FIFO                               //
    // --------------------------------------- //
    caliptra_prim_fifo_sync #(
      .Width            (DW  ),
      .Pass             (1'b0), // if == 1 allow requests to pass through empty FIFO
      .Depth            (FIFO_BC/BC),
      .OutputZeroIfEmpty(1'b1), // if == 1 always output 0 when FIFO is empty
      .Secure           (1'b0)  // use prim count for pointers; no secret data transmitted via DMA on AXI, no hardened counters
    ) i_fifo (
      .clk_i   (clk     ),
      .rst_ni  (rst_n   ),
      // synchronous clear / flush port
      .clr_i   (ctrl_fsm_ps == DMA_IDLE && hwif_out.ctrl.flush.value),
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

    // Requests must have valid length
    `CALIPTRA_ASSERT(AXI_DMA_VLD_RD_REQ_LEN, rd_req_hshake |-> r_req_if.byte_len < MAX_BLOCK_SIZE, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_VLD_WR_REQ_LEN, wr_req_hshake |-> w_req_if.byte_len < MAX_BLOCK_SIZE, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_VLD_FIXED_RD_REQ_LEN, rd_req_hshake && r_req_if.fixed |-> r_req_if.byte_len < MAX_FIXED_BLOCK_SIZE, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_VLD_FIXED_WR_REQ_LEN, wr_req_hshake && w_req_if.fixed |-> w_req_if.byte_len < MAX_FIXED_BLOCK_SIZE, clk, !rst_n)
    // Requests must not cross AXI boundary (4KiB)
    `CALIPTRA_ASSERT(AXI_DMA_VLD_RD_REQ_BND, rd_req_hshake |-> r_req_if.addr[AW-1:AXI_LEN_BC_WIDTH] == ((r_req_if.addr + r_req_if.byte_len) >> AXI_LEN_BC_WIDTH), clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_DMA_VLD_WR_REQ_BND, wr_req_hshake |-> w_req_if.addr[AW-1:AXI_LEN_BC_WIDTH] == ((w_req_if.addr + w_req_if.byte_len) >> AXI_LEN_BC_WIDTH), clk, !rst_n)
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

endmodule
