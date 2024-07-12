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
//      Top wrapper on AXI4 Manager (DMA) block
//

module axi_dma_top import axi_pkg::*; #(
    parameter AW = 64,
    parameter DW = 32,         // Data Width
              BC = DW/8,       // Byte Count
              BW = $clog2(BC), // Byte count Width
    parameter UW = 32,         // User Width
    parameter IW = 1,          // ID Width
              ID_NUM = 1 << IW // Don't override
)(
    input clk,
    input rst_n,

    // SOC_IFC Internal Signaling
    input mbox_lock,
    input sha_lock,

    // AXI INF
    axi_if.w_mgr m_axi_wr,
    axi_if.r_mgr m_axi_rd,

    // Component INF
    input dv,
    input var soc_ifc_req_t req_data,
    output hold,
    output [SOC_IFC_DATA_W-1:0] rdata,
    output error

);

    // --------------------------------------- //
    // Imports                                 //
    // --------------------------------------- //

    // --------------------------------------- //
    // Localparams/Typedefs                    //
    // --------------------------------------- //

    // --------------------------------------- //
    // Signals                                 //
    // --------------------------------------- //

    // --------------------------------------- //
    // Control State Machine                   //
    // --------------------------------------- //

    // --------------------------------------- //
    // AXI Manager Read Channel                //
    // --------------------------------------- //

    // --------------------------------------- //
    // AXI Manager Write Channel               //
    // --------------------------------------- //

    // --------------------------------------- //
    // Assertions                              //
    // --------------------------------------- //

endmodule
