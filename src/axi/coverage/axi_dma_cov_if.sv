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

interface axi_dma_cov_if
    import soc_ifc_pkg::*;
    (
        input logic clk,
        input logic cptra_pwrgood,
        input logic rst_n,
        
        // AXI INF
        axi_if.w_mgr m_axi_w_if,
        axi_if.r_mgr m_axi_r_if,
        
        // Component INF
        input logic dv,
        input var soc_ifc_req_t req_data,
        output logic hold,
        output logic [SOC_IFC_DATA_W-1:0] rdata,
        output logic error,

        // Mailbox SRAM INF
        output logic                   mb_dv,
        input  logic                   mb_hold,
        input  logic                   mb_error,
        output var soc_ifc_req_t       mb_data,
        input  logic [DW-1:0]          mb_rdata
    )

    
    covergroup axi_dma_cov_grp @(posedge clk);
        option.per_isntance = 1;

        //-------------------------------------------------------------
        // Edge Function Coverpoints
        //-------------------------------------------------------------

        // AHB2AXI 1DW Transfer
        ahb2axi_1dw: coverpoint (s_axi_r_if.arvalid && s_axi_r_if.arready && s_axi_r_if.arsize == 3'b010) { //ahb_htrans == 2'b10 && ahb_hsize == 3'b010 && 
            bins single_4byte_rd = {1}; // Cover 4-byte read transfers
        }
        
    endgroup

    
endinterface


`endif
