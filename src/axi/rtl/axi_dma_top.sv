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

module axi_dma_top
import axi_pkg::*;
import soc_ifc_pkg::*;
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

    // Recovery INF Interrupt
    // Should only assert when a full block_size of data is available at the
    // recovery interface FIFO
    input logic recovery_data_avail,
    input logic recovery_image_activated,

    // SOC_IFC Internal Signaling
    input logic mbox_lock,
    input logic sha_lock,
    input logic debugUnlock_or_scan_mode_switch,
    input logic ocp_lock_in_progress,
    input logic [63:0] key_release_addr,
    input logic [15:0] key_release_size,

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

    // Configuration for requests
    input logic [UW-1:0] axuser,

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
    input  logic [DW-1:0]          mb_rdata,

    // Interrupt
    output logic notif_intr,
    output logic error_intr

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
    // AXI Manager Read INF
    axi_dma_req_if #(.AW(AW)) r_req_if (.clk(clk), .rst_n(rst_n));
    logic                     r_ready;
    logic                     r_valid;
    logic  [DW-1:0]           r_data;

    // AXI Manager Write INF
    axi_dma_req_if #(.AW(AW)) w_req_if (.clk(clk), .rst_n(rst_n));
    logic                     w_ready;
    logic                     w_valid;
    logic  [DW-1:0]           w_data;


    // --------------------------------------- //
    // Control State Machine                   //
    // --------------------------------------- //
    axi_dma_ctrl #(
        .AW(AW),
        .DW(DW)
    ) i_axi_dma_ctrl (
        .clk          (clk          ),
        .cptra_pwrgood(cptra_pwrgood),
        .rst_n        (rst_n        ),

        // Recovery INF Interrupt
        // Should only assert when a full block_size of data is available at the
        // recovery interface FIFO
        .recovery_data_avail(recovery_data_avail),
        .recovery_image_activated(recovery_image_activated),

        // Internal Signaling
        .mbox_lock           (mbox_lock           ),
        .sha_lock            (sha_lock            ),
        .debugUnlock_or_scan_mode_switch(debugUnlock_or_scan_mode_switch),
        .ocp_lock_in_progress(ocp_lock_in_progress),
        .key_release_addr    (key_release_addr    ),
        .key_release_size    (key_release_size    ),

        // AES Interface
        .aes_input_ready,
        .aes_output_valid,
        .aes_status_idle,
        .aes_req_dv,
        .aes_req_hold,
        .aes_req_data,
        .aes_rdata,
        .aes_err,

        // KV interface
        .kv_read   (kv_read   ),
        .kv_rd_resp(kv_rd_resp),

        // Mailbox SRAM INF
        .mb_dv   (mb_dv   ),
        .mb_hold (mb_hold ),
        .mb_error(mb_error),
        .mb_data (mb_data ),
        .mb_rdata(mb_rdata),

        // AXI Manager Read INF
        .r_req_if (r_req_if.src),
        .r_ready_o(r_ready     ),
        .r_valid_i(r_valid     ),
        .r_data_i (r_data      ),

        // AXI Manager Write INF
        .w_req_if (w_req_if.src),
        .w_ready_i(w_ready     ),
        .w_valid_o(w_valid     ),
        .w_data_o (w_data      ),

        // Register INF
        .dv      (dv      ),
        .req_data(req_data),
        .hold    (hold    ),
        .rdata   (rdata   ),
        .error   (error   ),

        // Interrupt
        .notif_intr(notif_intr),
        .error_intr(error_intr)

    );

    // --------------------------------------- //
    // AXI Manager Read Channel                //
    // --------------------------------------- //
    axi_mgr_rd #(
        .AW(AW),
        .DW(DW),
        .UW(UW),
        .IW(IW)
    ) i_axi_mgr_rd (
        .clk(clk),
        .rst_n(rst_n),

        // AXI INF
        .m_axi_if(m_axi_r_if),

        // REQ INF
        .req_if(r_req_if.snk),

        // Static req USER value
        .axuser(axuser),

        // FIFO INF
        .ready_i(r_ready),
        .valid_o(r_valid),
        .data_o (r_data )
    );

    // --------------------------------------- //
    // AXI Manager Write Channel               //
    // --------------------------------------- //
    axi_mgr_wr #(
        .AW(AW),
        .DW(DW),
        .UW(UW),
        .IW(IW)
    ) i_axi_mgr_wr (
        .clk  (clk  ),
        .rst_n(rst_n),

        // AXI INF
        .m_axi_if(m_axi_w_if),

        // REQ INF
        .req_if(w_req_if.snk),

        // Static req USER value
        .axuser(axuser),

        // FIFO INF
        .valid_i(w_valid),
        .data_i (w_data ),
        .ready_o(w_ready)
    );

    // --------------------------------------- //
    // Assertions                              //
    // --------------------------------------- //

endmodule
