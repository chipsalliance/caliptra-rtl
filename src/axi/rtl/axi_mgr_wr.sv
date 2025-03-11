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
//      Generic AXI4 manager component for write channel. Accepts requests from
//      FSM logic, converts the request to legal AXI4 handshake, and moves data
//      that is received via a FIFO interface.
//

module axi_mgr_wr import axi_pkg::*; #(
    parameter AW = 32,
    parameter DW = 32,
              BC = DW/8,       // Byte Count
              BW = $clog2(BC), // Byte count Width
    parameter UW = 32,
    parameter IW = 1,
              ID_NUM = 1 << IW
) (
    input logic clk,
    input logic rst_n,

    // AXI INF
    axi_if.w_mgr m_axi_if,

    // REQ INF
    axi_dma_req_if.snk req_if,

    // Static req USER value
    input  logic [UW-1:0] axuser,

    // FIFO INF
    input  logic          valid_i,
    input  logic [DW-1:0] data_i,
    output logic          ready_o
);

    // --------------------------------------- //
    // Imports                                 //
    // --------------------------------------- //
    `include "caliptra_prim_assert.sv"


    // --------------------------------------- //
    // Localparams/Typedefs                    //
    // --------------------------------------- //
    // Transaction context
    typedef struct packed {
        logic [AW-1:0]            addr;
        logic                     fixed;
        logic [AXI_LEN_WIDTH-1:0] len;
        logic                     lock;
    } req_ctx_t;


    // --------------------------------------- //
    // Signals                                 //
    // --------------------------------------- //
    req_ctx_t   req_ctx;
    req_ctx_t   axi_ctx;
    logic       axi_ctx_valid;
    logic       axi_ctx_ready;
    logic       axi_ctx_sent;

    logic                     txn_active;
    logic [AXI_LEN_WIDTH-1:0] txn_down_cnt;
    logic                     txn_final_beat;


    // --------------------------------------- //
    // Request Context                         //
    // --------------------------------------- //
    
    always_comb begin
        req_ctx.addr  = req_if.addr;
        req_ctx.fixed = req_if.fixed;
        req_ctx.len   = req_if.byte_len[BW+:8];
        req_ctx.lock  = req_if.lock;
    end

    // Buffer the incoming request, but send it out over Address channel immediately
    // to allow multiple in-flight transactions (reduce bubbles between bursts).
    // The contents of the skidbuffer will inform the tracker for the next data
    // burst once the address channel request is sent.
    skidbuffer #(
        .OPT_LOWPOWER   (0   ),
        .OPT_OUTREG     (0   ),
        //
        .OPT_PASSTHROUGH(0   ),
        .DW             ($bits(req_ctx_t))
    ) i_ctx_skd (
        .i_clk  (clk                ),
        .i_reset(rst_n              ),
        .i_valid(req_if.valid       ),
        .o_ready(req_if.ready       ),
        .i_data (req_ctx            ),
        .o_valid(axi_ctx_valid      ),
        .i_ready(axi_ctx_ready      ),
        .o_data (axi_ctx            )
    );

    always_ff@(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi_ctx_sent <= 1'b0;
        end
        else if (axi_ctx_valid && axi_ctx_ready) begin
            axi_ctx_sent <= 1'b0;
        end
        else if (m_axi_if.awvalid && m_axi_if.awready) begin
            axi_ctx_sent <= 1'b1;
        end
    end

    always_comb begin
        m_axi_if.awvalid = axi_ctx_valid && !axi_ctx_sent;
        m_axi_if.awaddr  = axi_ctx.addr;
        m_axi_if.awburst = axi_ctx.fixed ? AXI_BURST_FIXED : AXI_BURST_INCR;
        m_axi_if.awsize  = BW;
        m_axi_if.awlen   = axi_ctx.len;
        m_axi_if.awuser  = axuser;
        m_axi_if.awid    = IW'(0);
        m_axi_if.awlock  = axi_ctx.lock;
    end

    always_comb axi_ctx_ready = (!txn_active || txn_final_beat) &&
                                (m_axi_if.awready || axi_ctx_sent);


    // --------------------------------------- //
    // Datapath                                //
    // --------------------------------------- //
    always_ff@(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            txn_active <= 1'b0;
        end
        else if (axi_ctx_valid && axi_ctx_ready) begin
            txn_active <= 1'b1;
        end
        else if (txn_final_beat) begin
            txn_active <= 1'b0;
        end
    end

    always_ff@(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            txn_down_cnt <= '1;
        end
        else if (axi_ctx_valid && axi_ctx_ready) begin
            txn_down_cnt <= axi_ctx.len;
        end
        else if (m_axi_if.wvalid && m_axi_if.wready) begin
            txn_down_cnt <= txn_down_cnt - 1;
        end
    end

    always_comb txn_final_beat = m_axi_if.wvalid && m_axi_if.wready && m_axi_if.wlast;
    always_comb begin
        m_axi_if.wvalid = txn_active && valid_i;
        m_axi_if.wdata  = data_i;
        m_axi_if.wstrb  = '1; // TODO support this? requires significant ctrl updates
        m_axi_if.wuser  = axuser;
        m_axi_if.wlast = ~|txn_down_cnt;
    end

    always_comb ready_o = txn_active && m_axi_if.wready;

    always_comb m_axi_if.bready = 1'b1;

    always_comb begin
        req_if.resp       = m_axi_if.bresp;
        req_if.resp_valid = m_axi_if.bvalid;
    end


    // --------------------------------------- //
    // Assertions                              //
    // --------------------------------------- //
    `CALIPTRA_ASSERT(AXI_MGR_REQ_BND, req_if.valid && !req_if.fixed |-> ((req_if.addr[11:0] + req_if.byte_len) <= 4096), clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_MGR_LEGAL_LEN, req_if.valid |-> (req_if.byte_len[AXI_LEN_BC_WIDTH-1:BW]) < AXI_LEN_MAX_VALUE, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_MGR_LEGAL_FIXED_LEN, req_if.valid && req_if.fixed |-> (req_if.byte_len[AXI_LEN_BC_WIDTH-1:BW]) < AXI_FIXED_LEN_MAX_VALUE, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_MGR_DATA_WHILE_ACTIVE, ready_o |-> txn_active, clk, !rst_n)
    `CALIPTRA_ASSERT_NEVER(AXI_MGR_UFLOW, m_axi_if.wvalid && !valid_i, clk, !rst_n)

endmodule
