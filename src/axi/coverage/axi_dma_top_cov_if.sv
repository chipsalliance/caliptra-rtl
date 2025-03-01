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

        // Mailbox SRAM INF

        input  logic                   mb_hold,
        input  logic                   mb_error,
        input  logic [DW-1:0]          mb_rdata
    );

    localparam DMA_WAIT_DATA    = 2'h1;
    localparam DMA_DONE         = 2'h2;

    logic w_valid;
    logic ctrl_fsm_ps;
    logic ahb_rd;
    logic mb_dv;
    logic mb_wr;
    logic [SOC_IFC_DATA_W-1:0] mb_wdata;
    logic [1:0] rd_route;
    logic [1:0] wr_route;

    logic awvalid_seen;
    logic arvalid_seen;

    logic [SOC_IFC_DATA_W-1:0] rdata;

    assign w_valid = axi_dma_top.w_valid;
    assign ctrl_fsm_ps = axi_dma_top.i_axi_dma_ctrl.ctrl_fsm_ps;
    assign ahb_rd = axi_dma_top.i_axi_dma_ctrl.hwif_out.read_data;
    assign rdata = axi_dma_top.rdata;
    assign mb_dv = axi_dma_top.mb_dv;
    assign mb_wr = axi_dma_top.mb_data.write;
    assign mb_wdata = axi_dma_top.mb_data.wdata;
    assign rd_route = axi_dma_top.i_axi_dma_ctrl.hwif_out.ctrl.rd_route;
    assign wr_route = axi_dma_top.i_axi_dma_ctrl.hwif_out.ctrl.wr_route;

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
        // Edge Function Coverpoints
        //-------------------------------------------------------------

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
    endgroup
    

    axi_dma_top_cov_grp axi_dma_top_cov_grp1 = new();
endinterface

`endif
