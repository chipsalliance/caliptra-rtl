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

`ifndef VERILATOR

interface axi_dma_top_cov_if
    import soc_ifc_pkg::*;
    import axi_dma_reg_pkg::*;
    import kv_defines_pkg::*;
    #(
        parameter AW = 64,
        parameter DW = 32,         // Data Width
                BC = DW/8,       // Byte Count
                BW = $clog2(BC), // Byte count Width
        parameter UW = 32,         // User Width
        parameter IW = 1,          // ID Width
                ID_NUM = 1 << IW // Don't override
    )(
        input logic clk,
        input logic cptra_pwrgood,
        input logic rst_n,
        
        // AXI INF
        axi_if.w_mgr m_axi_w_if,
        axi_if.r_mgr m_axi_r_if,
        
        // Component INF
        input logic dv,
        input var soc_ifc_req_t req_data,

        // Key Vault INF
        input logic ocp_lock_in_progress,
        input logic [63:0] key_release_addr,
        input logic [15:0] key_release_size,

        // Mailbox SRAM INF

        input  logic                   mb_hold,
        input  logic                   mb_error,
        input  logic [DW-1:0]          mb_rdata
    );

    localparam DMA_IDLE         = 2'h0;
    localparam DMA_WAIT_DATA    = 2'h1;
    localparam DMA_DONE         = 2'h2;
    localparam DMA_ERROR        = 2'h3;  

    // Additional signals for cmd_parse_error coverage
    logic cmd_inv_rd_route;
    logic cmd_inv_wr_route;
    logic cmd_inv_route_combo;
    logic cmd_inv_aes_route_combo;
    logic cmd_inv_aes_block_size;
    logic cmd_inv_aes_fixed;
    logic cmd_inv_src_addr;
    logic cmd_inv_dst_addr;
    logic cmd_inv_byte_count;
    logic cmd_inv_block_size;
    logic cmd_inv_rd_fixed;
    logic cmd_inv_wr_fixed;
    logic cmd_inv_mbox_lock;
    logic cmd_inv_sha_lock;
    logic cmd_parse_error;

    // Key Vault signals for coverage
    logic kv_read_en;
    kv_error_code_e kv_data_error_code;   
    logic axi_error;
    logic mb_lock_error;
    logic aes_error;
    logic all_bytes_transferred;
    

    logic w_valid;
    logic ctrl_fsm_ps;
    logic ctrl_fsm_ns;
    logic ahb_rd;
    logic mb_dv;
    logic mb_wr;
    logic [SOC_IFC_DATA_W-1:0] mb_wdata;
    logic [1:0] rd_route;
    logic [1:0] wr_route;

    logic awvalid_seen;
    logic arvalid_seen;

    logic [SOC_IFC_DATA_W-1:0] rdata;

    logic [11:0] total_expected_byte_count;
    logic [11:0] bytes_remaining;

    logic        dma_xfer_start_pulse;

    assign w_valid = axi_dma_top.w_valid;
    assign ctrl_fsm_ps = axi_dma_top.i_axi_dma_ctrl.ctrl_fsm_ps;
    assign ctrl_fsm_ns = axi_dma_top.i_axi_dma_ctrl.ctrl_fsm_ns;
    assign ahb_rd = axi_dma_top.i_axi_dma_ctrl.hwif_out.read_data;
    assign rdata = axi_dma_top.rdata;
    assign mb_dv = axi_dma_top.mb_dv;
    assign mb_wr = axi_dma_top.mb_data.write;
    assign mb_wdata = axi_dma_top.mb_data.wdata;
    assign rd_route = axi_dma_top.i_axi_dma_ctrl.hwif_out.ctrl.rd_route;
    assign wr_route = axi_dma_top.i_axi_dma_ctrl.hwif_out.ctrl.wr_route;
    assign bytes_remaining = axi_dma_top.i_axi_dma_ctrl.bytes_remaining;
    assign cmd_inv_rd_route = axi_dma_top.i_axi_dma_ctrl.cmd_inv_rd_route;
    assign cmd_inv_wr_route = axi_dma_top.i_axi_dma_ctrl.cmd_inv_wr_route;
    assign cmd_inv_route_combo = axi_dma_top.i_axi_dma_ctrl.cmd_inv_route_combo;
    assign cmd_inv_aes_route_combo = axi_dma_top.i_axi_dma_ctrl.cmd_inv_aes_route_combo;
    assign cmd_inv_aes_block_size = axi_dma_top.i_axi_dma_ctrl.cmd_inv_aes_block_size;
    assign cmd_inv_aes_fixed = axi_dma_top.i_axi_dma_ctrl.cmd_inv_aes_fixed;
    assign cmd_inv_src_addr = axi_dma_top.i_axi_dma_ctrl.cmd_inv_src_addr;
    assign cmd_inv_dst_addr = axi_dma_top.i_axi_dma_ctrl.cmd_inv_dst_addr;
    assign cmd_inv_byte_count = axi_dma_top.i_axi_dma_ctrl.cmd_inv_byte_count;
    assign cmd_inv_block_size = axi_dma_top.i_axi_dma_ctrl.cmd_inv_block_size;
    assign cmd_inv_rd_fixed = axi_dma_top.i_axi_dma_ctrl.cmd_inv_rd_fixed;
    assign cmd_inv_wr_fixed = axi_dma_top.i_axi_dma_ctrl.cmd_inv_wr_fixed;
    assign cmd_inv_mbox_lock = axi_dma_top.i_axi_dma_ctrl.cmd_inv_mbox_lock;
    assign cmd_inv_sha_lock = axi_dma_top.i_axi_dma_ctrl.cmd_inv_sha_lock;
    assign cmd_parse_error = axi_dma_top.i_axi_dma_ctrl.cmd_parse_error;

    assign kv_read_en = axi_dma_top.i_axi_dma_ctrl.kv_read_en;
    assign kv_data_error_code = kv_defines_pkg::kv_error_code_e'(axi_dma_top.i_axi_dma_ctrl.kv_data_error_code);
    assign axi_error = axi_dma_top.i_axi_dma_ctrl.axi_error;
    assign mb_lock_error = axi_dma_top.i_axi_dma_ctrl.mb_lock_error;
    assign aes_error = axi_dma_top.i_axi_dma_ctrl.aes_error;
    assign all_bytes_transferred = axi_dma_top.i_axi_dma_ctrl.all_bytes_transferred;

    // Pulse dma_xfer_start_pulse at beginning to DMA_WAIT_DATA state
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            dma_xfer_start_pulse <= 0;
        end
        else if (ctrl_fsm_ps == DMA_IDLE && ctrl_fsm_ns == DMA_WAIT_DATA) begin
            dma_xfer_start_pulse <= 1;
        end
        else begin
            dma_xfer_start_pulse <= 0;
        end
    end

    // Capture expected total byte count
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            total_expected_byte_count <= 0;
        end
        else if (dma_xfer_start_pulse) begin
            total_expected_byte_count <= bytes_remaining;
        end
        else if (bytes_remaining == 0) begin
            total_expected_byte_count <= 0;
        end
    end


    // AHB2AXI: Queue to store write data input Component INF
    logic [SOC_IFC_DATA_W-1:0] ahb2axi_rdata_queue[$];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ahb2axi_rdata_queue = {};
        end 
        else if (rd_route == axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE &&
                 wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__AHB_FIFO && 
                 ctrl_fsm_ps == DMA_WAIT_DATA && dv && req_data.write) begin 
            ahb2axi_rdata_queue.push_back(req_data.wdata);
        end
    end

    // MBOX2AXI: Queue to store read data input from MBOX
    logic [SOC_IFC_DATA_W-1:0] mbox2axi_rdata_queue[$];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mbox2axi_rdata_queue = {};
        end
        else if (rd_route == axi_dma_reg__ctrl__rd_route__rd_route_e__DISABLE &&
                 wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__MBOX && 
                 ctrl_fsm_ps == DMA_WAIT_DATA && mb_dv && !mb_hold && !mb_wr) begin 
            mbox2axi_rdata_queue.push_back(mb_rdata);
        end
    end

    // AXI2AXI: Queue to store AXI read data
    logic [SOC_IFC_DATA_W-1:0] axi2axi_rdata_queue[$];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi2axi_rdata_queue = {};
        end
        else if (rd_route == axi_dma_reg__ctrl__rd_route__rd_route_e__AXI_WR &&
                 wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__AXI_RD && 
                 ctrl_fsm_ps == DMA_WAIT_DATA && arvalid_seen && m_axi_r_if.rvalid) begin 
            axi2axi_rdata_queue.push_back(m_axi_r_if.rdata);
        end
    end

    // AXI2AHB: Queue to store AXI read data
    logic [SOC_IFC_DATA_W-1:0] axi2ahb_rdata_queue[$];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi2ahb_rdata_queue = {};
        end
        else if (rd_route == axi_dma_reg__ctrl__rd_route__rd_route_e__AHB_FIFO && 
                 wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE && 
                 ctrl_fsm_ps == DMA_WAIT_DATA && arvalid_seen && m_axi_r_if.rvalid) begin 
            axi2ahb_rdata_queue.push_back(m_axi_r_if.rdata);
        end
    end

    // AXI2MBOX: Queue to store AXI read data
    logic [SOC_IFC_DATA_W-1:0] axi2mbox_rdata_queue[$];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi2mbox_rdata_queue = {};
        end
        else if (rd_route == axi_dma_reg__ctrl__rd_route__rd_route_e__MBOX && 
                 wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__DISABLE && 
                 ctrl_fsm_ps == DMA_WAIT_DATA && arvalid_seen && m_axi_r_if.rvalid && mb_wr) begin 
            axi2mbox_rdata_queue.push_back(m_axi_r_if.rdata);
        end
    end

    // AXI MGR write in progress
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            awvalid_seen <= 0;
        end
        else if (m_axi_w_if.awvalid && m_axi_w_if.awready && m_axi_w_if.awsize == 3'b010) begin
            awvalid_seen <= 1;
        end
        else if (!m_axi_w_if.wvalid) begin
            awvalid_seen <= 0;
        end
    end

    // AXI MGR Read in progress
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin 
            arvalid_seen <= 0;
        end
        else if (m_axi_r_if.arvalid && m_axi_r_if.arready && m_axi_r_if.arsize == 3'b010) begin
            arvalid_seen <= 1;
        end
        else if (!m_axi_r_if.rready) begin
            arvalid_seen <= 0;
        end
    end

    // Capture expected write data for AHB2AXI transfer
    logic [SOC_IFC_DATA_W-1:0] expected_wdata;
    logic first_pop_done_req_data;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            expected_wdata <= 0;
            first_pop_done_req_data <= 0;
        end
        else if (ahb2axi_rdata_queue.size() > 0) begin
            if (!first_pop_done_req_data) begin
                expected_wdata <= ahb2axi_rdata_queue.pop_front();
                first_pop_done_req_data <= 1; 
            end
            else if (awvalid_seen && m_axi_w_if.wvalid && m_axi_w_if.wready) begin
                expected_wdata <= ahb2axi_rdata_queue.pop_front();
            end
        end
        else if (awvalid_seen && ahb2axi_rdata_queue.size() == 0) begin
            first_pop_done_req_data <= 0;
            expected_wdata <= 0;
        end
    end

    // Capture expected mbox read data for MBOX2AXI transfer
    logic [SOC_IFC_DATA_W-1:0] expected_mbox_rdata;
    logic first_pop_done_mbox_rdata;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            expected_mbox_rdata <= 0;
            first_pop_done_mbox_rdata <= 0;
        end 
        else if (mbox2axi_rdata_queue.size() > 0) begin
            if (!first_pop_done_mbox_rdata) begin
                expected_mbox_rdata <= mbox2axi_rdata_queue.pop_front();
                first_pop_done_mbox_rdata <= 1;
            end
            else if (awvalid_seen && m_axi_w_if.wvalid && m_axi_w_if.wready) begin
                expected_mbox_rdata <= mbox2axi_rdata_queue.pop_front();
            end
        end
        else if (awvalid_seen && mbox2axi_rdata_queue.size() == 0) begin
            first_pop_done_mbox_rdata <= 0;
            expected_mbox_rdata <= 0;
        end
    end

    
    // Capture expected AXI Read Data for AXI2AXI transfer
    logic [SOC_IFC_DATA_W-1:0] expected_axi_rdata;
    logic first_pop_done_axi_rdata;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            expected_axi_rdata <= 0;
            first_pop_done_axi_rdata <= 0;
        end
        else if (axi2axi_rdata_queue.size() > 0) begin
            if (!first_pop_done_axi_rdata) begin
                expected_axi_rdata <= axi2axi_rdata_queue.pop_front();
                first_pop_done_axi_rdata <= 1;
            end
            else if (awvalid_seen && m_axi_w_if.wvalid && m_axi_w_if.wready) begin
                expected_axi_rdata <= axi2axi_rdata_queue.pop_front();
            end
        end
        else if (awvalid_seen && axi2axi_rdata_queue.size() == 0) begin
            first_pop_done_axi_rdata <= 0;
            expected_axi_rdata <= 0;
        end
    end

    // Capture expected AXI read data for AXI2AHB transfer
    logic [SOC_IFC_DATA_W-1:0] expected_axi2ahb_rdata;
    logic first_pop_done_axi2ahb_rdata;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            expected_axi2ahb_rdata <= 0;
            first_pop_done_axi2ahb_rdata <= 0;
        end
        else if (axi2ahb_rdata_queue.size() > 0) begin
            if (!first_pop_done_axi2ahb_rdata) begin
                expected_axi2ahb_rdata <= axi2ahb_rdata_queue.pop_front();
                first_pop_done_axi2ahb_rdata <= 1;
            end
            else if (ahb_rd) begin
                expected_axi2ahb_rdata <= axi2ahb_rdata_queue.pop_front();
            end
        end
        else if (ctrl_fsm_ps == DMA_DONE && axi2ahb_rdata_queue.size() == 0) begin
            first_pop_done_axi2ahb_rdata <= 0;
            expected_axi2ahb_rdata <= 0;
        end
    end

    // Capture expected AXI read data for AXi2MBOX transfer
    logic [SOC_IFC_DATA_W-1:0] expected_axi2mbox_rdata;
    logic first_pop_done_axi2mbox_rdata;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            expected_axi2mbox_rdata <= 0;
            first_pop_done_axi2mbox_rdata <= 0;
        end
        else if (axi2mbox_rdata_queue.size() > 0) begin
            if (!first_pop_done_axi2mbox_rdata) begin
                expected_axi2mbox_rdata <= axi2mbox_rdata_queue.pop_front();
                first_pop_done_axi2mbox_rdata <= 1;
            end
            else if (mb_dv && mb_wr) begin
                expected_axi2mbox_rdata <= axi2mbox_rdata_queue.pop_front();
            end
        end
        else if (axi2mbox_rdata_queue.size() == 0) begin
            first_pop_done_axi2mbox_rdata <= 0;
            expected_axi2mbox_rdata <= 0;
        end
    end

    covergroup axi_dma_top_cov_grp @(posedge clk);
        option.per_instance = 1;

        //-------------------------------------------------------------
        // Key Vault Read Error Coverpoint
        // Covers entry into DMA_ERROR due to kv_read_en && kv_data_error_code != KV_SUCCESS
        //-------------------------------------------------------------

        kv_read_error_only_causes_dma_error: coverpoint (
            (ctrl_fsm_ps == DMA_WAIT_DATA) && 
            (ctrl_fsm_ns == DMA_ERROR) &&
            kv_read_en && 
            (kv_data_error_code != KV_SUCCESS) &&
            !axi_error &&           // Ensure AXI error is NOT active
            !mb_lock_error &&       // Ensure mailbox lock error is NOT active  
            !aes_error              // Ensure AES error is NOT active
        ) {
            bins kv_read_error_isolated = {1};
        }
        
        //-------------------------------------------------------------
        // CMD Parse Error Coverpoints - Individual Error Isolation
        // Each coverpoint only hits when that specific cmd_inv signal is the ONLY one active
        //-------------------------------------------------------------

        cmd_inv_rd_route_in_error: coverpoint (
            cmd_inv_rd_route && 
            !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins rd_route_error_only = {1};
        }

        cmd_inv_wr_route_in_error: coverpoint (
            cmd_inv_wr_route && 
            !cmd_inv_rd_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins wr_route_error_only = {1};
        }

        cmd_inv_route_combo_in_error: coverpoint (
            cmd_inv_route_combo && 
            !cmd_inv_rd_route && !cmd_inv_wr_route && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins route_combo_error_only = {1};
        }

        cmd_inv_aes_route_combo_in_error: coverpoint (
            cmd_inv_aes_route_combo && 
            !cmd_inv_rd_route && !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins aes_route_combo_error_only = {1};
        }

        cmd_inv_aes_block_size_in_error: coverpoint (
            cmd_inv_aes_block_size && 
            !cmd_inv_rd_route && !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins aes_block_size_error_only = {1};
        }

        cmd_inv_aes_fixed_in_error: coverpoint (
            cmd_inv_aes_fixed && 
            !cmd_inv_rd_route && !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins aes_fixed_error_only = {1};
        }

        cmd_inv_src_addr_in_error: coverpoint (
            cmd_inv_src_addr && 
            !cmd_inv_rd_route && !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_dst_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins src_addr_error_only = {1};
        }

        cmd_inv_dst_addr_in_error: coverpoint (
            cmd_inv_dst_addr && 
            !cmd_inv_rd_route && !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins dst_addr_error_only = {1};
        }

        cmd_inv_byte_count_in_error: coverpoint (
            cmd_inv_byte_count && 
            !cmd_inv_rd_route && !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins byte_count_error_only = {1};
        }

        cmd_inv_block_size_in_error: coverpoint (
            cmd_inv_block_size && 
            !cmd_inv_rd_route && !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_byte_count && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins block_size_error_only = {1};
        }

        cmd_inv_rd_fixed_in_error: coverpoint (
            cmd_inv_rd_fixed && 
            !cmd_inv_rd_route && !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins rd_fixed_error_only = {1};
        }

        cmd_inv_wr_fixed_in_error: coverpoint (
            cmd_inv_wr_fixed && 
            !cmd_inv_rd_route && !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins wr_fixed_error_only = {1};
        }

        cmd_inv_mbox_lock_in_error: coverpoint (
            cmd_inv_mbox_lock && 
            !cmd_inv_rd_route && !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_sha_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins mbox_lock_error_only = {1};
        }

        cmd_inv_sha_lock_in_error: coverpoint (
            cmd_inv_sha_lock && 
            !cmd_inv_rd_route && !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock
        ) iff (ctrl_fsm_ps == DMA_ERROR) {
            bins sha_lock_error_only = {1};
        }
        
        //-------------------------------------------------------------
        // Key Release Address Mismatch - Requirement 2
        // DMA_ERROR due to key_release_addr mismatch, with KEYVAULT route, no other cmd_inv active
        //-------------------------------------------------------------
        
        key_release_addr_mismatch_error: coverpoint (
            ctrl_fsm_ps == DMA_ERROR && 
            cmd_inv_dst_addr && 
            (wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT) &&
            !cmd_inv_rd_route && !cmd_inv_wr_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) {
            bins key_addr_mismatch_only = {1};
        }

        //-------------------------------------------------------------
        // OCP Lock Not In Progress - Requirement 4
        // DMA_ERROR due to !ocp_lock_in_progress with KEYVAULT route, no other cmd_inv active
        //-------------------------------------------------------------
        
        ocp_lock_not_in_progress_error: coverpoint (
            ctrl_fsm_ps == DMA_ERROR && 
            cmd_inv_wr_route && 
            (wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT) &&
            !ocp_lock_in_progress &&
            !cmd_inv_rd_route && !cmd_inv_route_combo && 
            !cmd_inv_aes_route_combo && !cmd_inv_aes_block_size && !cmd_inv_aes_fixed && 
            !cmd_inv_src_addr && !cmd_inv_dst_addr && !cmd_inv_byte_count && !cmd_inv_block_size && 
            !cmd_inv_rd_fixed && !cmd_inv_wr_fixed && !cmd_inv_mbox_lock && !cmd_inv_sha_lock
        ) {
            bins ocp_lock_not_active_only = {1};
        }

        //-------------------------------------------------------------
        // Additional Interesting Coverpoints - Requirement 5
        //-------------------------------------------------------------
        
        // Key Vault operation start when OCP lock is active
        keyvault_operation_with_ocp_lock: coverpoint (
            dma_xfer_start_pulse && 
            (wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT) &&
            ocp_lock_in_progress
        ) {
            bins keyvault_with_lock = {1};
        }

        
        // Key release address and size both match when starting KEYVAULT operation
        keyvault_perfect_match: coverpoint (
            dma_xfer_start_pulse && 
            (wr_route == axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT) &&
            ocp_lock_in_progress &&
            (axi_dma_top.i_axi_dma_ctrl.dst_addr == key_release_addr) &&
            (axi_dma_top.i_axi_dma_ctrl.hwif_out.byte_count.count.value == 32'(key_release_size))
        ) {
            bins perfect_keyvault_match = {1};
        }

        // OCP lock status during different DMA operations
        ocp_lock_status_during_operations: coverpoint ocp_lock_in_progress iff (dma_xfer_start_pulse) {
            bins lock_active = {1};
            bins lock_inactive = {0};
        }

        // Cross coverage: Route combination with OCP lock status
        route_ocp_lock_cross: cross wr_route, ocp_lock_in_progress iff (dma_xfer_start_pulse) {
            // Only interested in KEYVAULT route combinations
            bins keyvault_with_lock = binsof(wr_route) intersect {axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT} &&
                                     binsof(ocp_lock_in_progress) intersect {1};
            bins keyvault_without_lock = binsof(wr_route) intersect {axi_dma_reg__ctrl__wr_route__wr_route_e__KEYVAULT} &&
                                        binsof(ocp_lock_in_progress) intersect {0};
        }

        //-------------------------------------------------------------
        // Edge Function Coverpoints
        //-------------------------------------------------------------

        //-------------------------------------------
        // 1DW Transfers Data Check
        // ------------------------------------------

        // AHB2AXI_1DW Transfer with Data Comparison
        ahb2axi_1dw_data_compare: coverpoint (awvalid_seen && m_axi_w_if.wvalid && m_axi_w_if.wdata == expected_wdata) {
            bins single_4byte_ahb2axi_match = {1}; // Cover 4-byte write transfers with matching data
        }

        // MBOX2AXI_1DW Transfer with Data Comparison
        mbox2axi_1dw_data_compare: coverpoint (awvalid_seen && m_axi_w_if.wvalid && m_axi_w_if.wdata == expected_mbox_rdata) {
            bins single_4byte_mbox2axi_match = {1}; // Cover 4-byte write transfer with matching data
        }

        // AXI2AXI_1DW Transfer with Data Comparison
        axi2axi_1dw_data_compare: coverpoint (awvalid_seen && m_axi_w_if.wvalid && m_axi_w_if.wready && m_axi_w_if.wdata == expected_axi_rdata) {
            bins single_4byte_axi2axi_match = {1};
        }

        // AXI2AHB_1DW Transfer with Data Comparison
        axi2ahb_1dw_data_compare: coverpoint (dv && ahb_rd && rdata == expected_axi2ahb_rdata) {
            bins single_4byte_axi2ahb_match = {1};
        }

        // AXI2MBOX_1DW Transfer with Data Comparison
        axi2mbox_1dw_data_compare: coverpoint (mb_dv && mb_wr && mb_wdata == expected_axi2mbox_rdata) {
            bins single_4byte_axi2mbox_match = {1};
        }

        // -------------------------------------------------------------------
        // N-DW Transfers with total byte count check and transfer split check
        // -------------------------------------------------------------------
        //ah2axi_ndw_byte_count: coverpoint () {
        //    bins total_byte_count_ahb2axi_match = {1};
        //}
    endgroup
    

    axi_dma_top_cov_grp axi_dma_top_cov_grp1 = new();
endinterface

`endif
