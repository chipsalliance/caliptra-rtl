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

// -------------------------------------------------------------
// AXI TLUL Write Shim
// -------------------------------------------------------------
// Description:
//   Shim to convert AXI protocol writes into TLUL
//
// Limitations:
//   - When multiple ID tracking is enabled, write responses are returned in the
//     same order they are received, regardless of ID.
//
// -------------------------------------------------------------

import axi_pkg::*;

module axi_mgr   
    #(
        parameter AW = 32,          // Address Width
        parameter DW = 32,          // Data Width
                  BC = DW/8,        // Byte Count
                  BW = $clog2(BC),  // Byte count Width
        parameter UW = 32,          // User Width
        parameter IW = 1,           // ID Width
                  ID_NUM = 1 << IW, // Don't override

        parameter EX_EN = 0,        // Enable exclusive access tracking w/ AxLOCK
        parameter C_LAT = 0         // Component latency in clock cycles from (dv&&!hld) -> rdata
                                    // Must be const per component
                                    // For registers, typically 0
                                    // For SRAM, 1 or more
    ) (
        input logic         clk,
        input logic         rst_n, 

        // AXI Manager INF
        axi_if.w_mgr m_axi_w_if,
        axi_if.r_mgr m_axi_r_if
    ); 

    logic [DW-1:0] rdata;

    task readSingle(input logic[AW-1:0] addr, input [2:0] size);
        m_axi_r_if.araddr    = addr;
        m_axi_r_if.arburst   = AXI_BURST_FIXED;
        m_axi_r_if.arlen     = 1; // number of beats (transfer) in the burst
        m_axi_r_if.arsize    = size; //number of bytes per beat (transter)
        m_axi_r_if.arvalid   = 1;

        // Wait for AXI device to assert ARREADY
        while (!m_axi_r_if.arrready) begin
            @(posedge clk);
        end

        //Deaasert ARVALID after ARREADY is asserted
        rdata           = m_axi_r_if.rdata;
        m_axi_r_if.arvalid   = 0;
    endtask: readSingle

    task writeSingle(input logic[AW-1:0] addr, input [DW-1:0] data, input [2:0] size);
        m_axi_w_if.awaddr    = addr;
        m_axi_w_if.awburst   = AXI_BURST_FIXED;
        m_axi_w_if.awlen     = 1; // number of beats (transfers) in the burst
        m_axi_w_if.awsize    = size;
        m_axi_w_if.awvalid   = 1;

        // Wait for AXI device to assert AWREADY
        while (!m_axi_w_if.awready) begin
            @(posedge clk);
        end

        // Data Phase
        m_axi_w_if.wdata     = data;
        m_axi_w_if.wstrb     = '1;
        m_axi_w_if.wvalid    = 1;

        // Wait for AXI device to assert WREADY
        while (!m_axi_w_if.wready) begin
            @(posedge clk);
        end

        // Deassert AWVALID after WREADY has been asserted
        m_axi_w_if.awvalid   = 0;
    endtask: writeSingle

endmodule: axi_mgr