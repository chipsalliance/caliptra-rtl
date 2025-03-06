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
//      Generic AXI4 manager component for read channel. Accepts requests from
//      FSM logic, converts the request to legal AXI4 handshake, and forwards
//      return data via a FIFO interface.
//

module axi_mgr_rd import axi_pkg::*; #(
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
    axi_if.r_mgr m_axi_if,

    // REQ INF
    axi_dma_req_if.snk req_if,

    // Static req USER value
    input  logic [UW-1:0] axuser,

    // FIFO INF
    input  logic          ready_i,
    output logic          valid_o,
    output logic [DW-1:0] data_o
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

    logic       txn_active;
    logic       txn_final_beat;


    // --------------------------------------- //
    // Request Context                         //
    // --------------------------------------- //
    
    always_comb begin
        req_ctx.addr  = req_if.addr;
        req_ctx.fixed = req_if.fixed;
        req_ctx.len   = req_if.byte_len[BW+:AXI_LEN_WIDTH];
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
        else if (m_axi_if.arvalid && m_axi_if.arready) begin
            axi_ctx_sent <= 1'b1;
        end
    end

    always_comb begin
        m_axi_if.arvalid = axi_ctx_valid && !axi_ctx_sent;
        m_axi_if.araddr  = axi_ctx.addr;
        m_axi_if.arburst = axi_ctx.fixed ? AXI_BURST_FIXED : AXI_BURST_INCR;
        m_axi_if.arsize  = BW;
        m_axi_if.arlen   = axi_ctx.len;
        m_axi_if.aruser  = axuser;
        m_axi_if.arid    = IW'(0);
        m_axi_if.arlock  = axi_ctx.lock;
    end

    always_comb axi_ctx_ready = (!txn_active || txn_final_beat) &&
                                (m_axi_if.arready || axi_ctx_sent);


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

    always_comb txn_final_beat = m_axi_if.rvalid && m_axi_if.rready && m_axi_if.rlast;
    always_comb m_axi_if.rready = txn_active && ready_i;

    always_comb begin
        valid_o = m_axi_if.rvalid && m_axi_if.rready;
        data_o  = m_axi_if.rdata;
    end

    always_ff@(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            req_if.resp       <= AXI_RESP_OKAY;
            req_if.resp_valid <= 1'b0;
        end
        // Accumulate status codes...
        // TODO what if ERROR is interleaved with EXOKAY?
        //      That would be a mistake by the slave, since we don't use Exclusive Access feature
        else if (m_axi_if.rvalid && m_axi_if.rready) begin
            req_if.resp       <= req_if.resp | m_axi_if.rresp;
            req_if.resp_valid <= m_axi_if.rlast;
        end
        else if (axi_ctx_valid && axi_ctx_ready) begin
            req_if.resp       <= AXI_RESP_OKAY;
            req_if.resp_valid <= 1'b0;
        end
        else begin
            req_if.resp       <= req_if.resp;
            req_if.resp_valid <= 1'b0;
        end
    end

    // --------------------------------------- //
    // Assertions                              //
    // --------------------------------------- //
    `CALIPTRA_ASSERT(AXI_MGR_REQ_BND, req_if.valid && !req_if.fixed |-> ((req_if.addr[11:0] + req_if.byte_len) <= 4096), clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_MGR_LEGAL_LEN, req_if.valid |-> (req_if.byte_len[AXI_LEN_BC_WIDTH-1:BW]) < AXI_LEN_MAX_VALUE, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_MGR_LEGAL_FIXED_LEN, req_if.valid && req_if.fixed |-> (req_if.byte_len[AXI_LEN_BC_WIDTH-1:BW]) < AXI_FIXED_LEN_MAX_VALUE, clk, !rst_n)
    `CALIPTRA_ASSERT(AXI_MGR_DATA_WHILE_ACTIVE, valid_o |-> txn_active, clk, !rst_n)
    `CALIPTRA_ASSERT_NEVER(AXI_MGR_OFLOW, m_axi_if.rready && !ready_i, clk, !rst_n)


endmodule
