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

    logic w_valid;

    assign w_valid = axi_dma_top.w_valid;

    // Queue to store write data input Component INF
    logic [SOC_IFC_DATA_W-1:0] req_data_queue[$];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            req_data_queue = {};
        end else if (w_valid && dv && req_data.write) begin
            req_data_queue.push_back(req_data.wdata);
        end
    end

    // Capture expected wdata after awvalid has been asserted. 
    logic awvalid_seen;
    logic [SOC_IFC_DATA_W-1:0] expected_wdata;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            awvalid_seen <= 0;
            expected_wdata <= 0;
        end 
        else if (m_axi_w_if.awvalid && m_axi_w_if.awready && m_axi_w_if.awsize == 3'b010) begin
            awvalid_seen <= 1;
        end
        else if (awvalid_seen && m_axi_w_if.wvalid) begin
                expected_wdata <= req_data_queue.pop_front();
        end
        else if (!m_axi_w_if.wvalid) begin
            awvalid_seen <= 0;
        end
    end

    covergroup axi_dma_top_cov_grp @(posedge clk);
        option.per_instance = 1;

        //-------------------------------------------------------------
        // Edge Function Coverpoints
        //-------------------------------------------------------------

        // AHB2AXI_1DW Transfer with Data Comparison
        ahb2axi_1dw_data_compare: coverpoint (awvalid_seen && m_axi_w_if.wvalid && m_axi_w_if.wdata == expected_wdata) {
            bins single_4byte_wr_match = {1}; // Cover 4-byte write transfers with matching data
        }
    endgroup

    axi_dma_top_cov_grp axi_dma_top_cov_grp1 = new();
endinterface

`endif
