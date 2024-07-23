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
// AXI Write Subordinate
// -------------------------------------------------------------
// Description:
//   Subordinate to convert AXI protocol writes into internal component accesses
//
// Limitations:
//   - When multiple ID tracking is enabled, write responses are returned in the
//     same order they are received, regardless of ID.
//
// -------------------------------------------------------------

module axi_sub_wr import axi_pkg::*; #(
    parameter AW = 32,         // Address Width
    parameter DW = 32,         // Data Width
              BC = DW/8,       // Byte Count
              BW = $clog2(BC), // Byte count Width
    parameter UW = 32,         // User Width
    parameter IW = 1,          // ID Width
              ID_NUM = 1 << IW, // Don't override

    parameter EX_EN = 0         // Enable exclusive access tracking w/ AxLOCK
) (
    input clk,
    input rst_n,

    // AXI INF
    axi_if.w_sub s_axi_if,

    // Exclusive Access Signals
    output logic            [ID_NUM-1:0] ex_clr,
    input  logic            [ID_NUM-1:0] ex_active,
    input  struct packed {
        logic [AW-1:0] addr;
        logic [AW-1:0] addr_mask;
    } [ID_NUM-1:0] ex_ctx,

    //COMPONENT INF
    output logic          dv,
    output logic [AW-1:0] addr, // Byte address
    output logic [UW-1:0] user,
    output logic [IW-1:0] id,
    output logic [DW-1:0] wdata, // Requires: Component dwidth == AXI dwidth
    output logic [BC-1:0] wstrb, // Requires: Component dwidth == AXI dwidth
    output logic          last, // Asserted with final 'dv' of a burst
    input  logic          hld,
    input  logic          err

);

    // --------------------------------------- //
    // Localparams/Typedefs                    //
    // --------------------------------------- //

    // Transaction context
    typedef struct packed {
        logic [AW-1:0] addr;
        axi_burst_e    burst;
        logic [2:0]    size;
        logic [7:0]    len;
        logic [UW-1:0] user;
        logic [IW-1:0] id;
        logic          lock;
    } axi_ctx_t;


    // --------------------------------------- //
    // Signals                                 //
    // --------------------------------------- //

    genvar ex; // Exclusive contexts

    logic dv_pre;

    // Active transaction signals
    // track requests as they are sent to component
    axi_ctx_t            s_axi_if_ctx;
    axi_ctx_t            req_ctx;
    logic                req_valid;
    logic                req_ready;
    logic                req_matches_ex;
    axi_ctx_t            txn_ctx;
    logic [AW-1:0]       txn_addr_nxt;
    logic                txn_active;
    logic                txn_wvalid;
    logic                txn_wready;
    logic                txn_allow; // If an exclusive-write with no match to tracked context, don't complete write to component
    logic                txn_err;
    logic                txn_final_beat;
    logic [ID_NUM-1:0]   txn_ex_match; // Current access matches the flagged exclusive context
                                       // Possible for multiple bits to be set -- match of multiple contexts

    // Response Pipeline signals
    logic               rp_valid;
    logic               rp_ready;
    axi_resp_e          rp_resp;
    logic      [IW-1:0] rp_id;


    // --------------------------------------- //
    // Address Request I/F                     //
    // --------------------------------------- //

    always_comb begin
        s_axi_if_ctx.addr  = s_axi_if.awaddr ;
        s_axi_if_ctx.burst = axi_burst_e'(s_axi_if.awburst);
        s_axi_if_ctx.size  = s_axi_if.awsize ;
        s_axi_if_ctx.len   = s_axi_if.awlen  ;
        s_axi_if_ctx.user  = s_axi_if.awuser ;
        s_axi_if_ctx.id    = s_axi_if.awid   ;
        s_axi_if_ctx.lock  = s_axi_if.awlock && EX_EN;
    end

    // skidbuffer instance to pipeline request context from AXI.
    skidbuffer #(
        .OPT_LOWPOWER   (0   ),
        .OPT_OUTREG     (0   ),
        //
        .OPT_PASSTHROUGH(0   ),
        .DW             ($bits(axi_ctx_t)),
        .OPT_INITIAL    (1'b1)
    ) i_req_skd (
        .i_clk  (clk             ),
        .i_reset(!rst_n          ),
        .i_valid(s_axi_if.awvalid),
        .o_ready(s_axi_if.awready),
        .i_data (s_axi_if_ctx    ),
        .o_valid(req_valid       ),
        .i_ready(req_ready       ),
        .o_data (req_ctx         )
    );

    // Only accept request when we have a guaranteed slot in the response buffer
    // to put the response
    assign req_ready = (!txn_active || (txn_final_beat && !s_axi_if.bvalid)) && rp_ready;

    // Indicates there are still reqs to be issued towards component.
    // This active signal deasserts after final dv to component
    always_ff@(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            txn_active <= 1'b0;
        end
        else if (req_valid && req_ready) begin
            txn_active <= 1'b1;
        end
        else if (txn_final_beat) begin
            txn_active <= 1'b0;
        end
        else begin
            txn_active <= txn_active;
        end
    end

    always_comb req_matches_ex = (req_ctx.addr & ex_ctx[req_ctx.id].addr_mask) == ex_ctx[req_ctx.id].addr;

    always_ff@(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            txn_ctx <= '{default:0, burst:AXI_BURST_FIXED};
        end
        else if (req_valid && req_ready) begin
            txn_ctx.addr  <= req_ctx.addr;
            txn_ctx.burst <= req_ctx.burst;
            txn_ctx.size  <= req_ctx.size;
            txn_ctx.len   <= req_ctx.len ;
            txn_ctx.user  <= req_ctx.user;
            txn_ctx.id    <= req_ctx.id  ;
            txn_ctx.lock  <= req_ctx.lock;
            txn_allow     <= !EX_EN || !req_ctx.lock || (ex_active[req_ctx.id] && req_matches_ex);
            txn_err       <= 1'b0;
        end
        else if (dv && !hld) begin
            txn_ctx.addr  <= txn_addr_nxt;
            txn_ctx.burst <= txn_ctx.burst;
            txn_ctx.size  <= txn_ctx.size;
            txn_ctx.len   <= txn_ctx.len ;
            txn_ctx.user  <= txn_ctx.user;
            txn_ctx.id    <= txn_ctx.id  ;
            txn_ctx.lock  <= txn_ctx.lock;
            txn_allow     <= txn_allow;
            txn_err       <= txn_err || err;
        end
        else begin
            txn_ctx       <= txn_ctx;
            txn_allow     <= txn_allow;
            txn_err       <= txn_err;
        end
    end

    // Asserts on the final COMPONENT INF beat, which means data does not
    // arrive at endpoint until after C_LAT clocks
    always_comb txn_final_beat = dv_pre && (!txn_allow || !hld) && last;


    // --------------------------------------- //
    // Address Calculations                    //
    // --------------------------------------- //
    // Force aligned address to component
    always_comb addr = {txn_ctx.addr[AW-1:BW],BW'(0)};
    always_comb user = txn_ctx.user;
    always_comb id   = txn_ctx.id;

    // Use full address to calculate next address (in case of AxSIZE < data width)
    axi_addr #(
        .AW  (AW),
        .DW  (DW)
    ) i_axi_addr (
        .i_last_addr(txn_ctx.addr ),
        .i_size     (txn_ctx.size ), // 1b, 2b, 4b, 8b, etc
        .i_burst    (txn_ctx.burst), // fixed, incr, wrap, reserved
        .i_len      (txn_ctx.len  ),
        .o_next_addr(txn_addr_nxt )
    );


    // --------------------------------------- //
    // Exclusive Access Tracking               //
    // --------------------------------------- //
    
    generate
    for (ex=0; ex < ID_NUM; ex++) begin: EX_AXS_TRACKER
        logic [AW-1:0] addr_ex_algn;

        // Component address aligned to exclusive tracking context
        // Don't use aligned 'addr' signal, because exclusive access alignment may
        // be smaller than component inf (since single-byte exclusive access is legal)
        always_comb addr_ex_algn = txn_ctx.addr & ex_ctx[ex].addr_mask;

        // Match on each beat in case a burst transaction only overlaps
        // the exclusive context partially
        always_comb txn_ex_match[ex] = (addr_ex_algn == ex_ctx[ex].addr);

    end: EX_AXS_TRACKER
    endgenerate

    // Only clear the context when a write goes through to dest - meaining dv, not dv_pre
    always_ff@(posedge clk or negedge rst_n) begin
        if (!rst_n)
            ex_clr <= ID_NUM'(0);
        else if (EX_EN && dv && !hld)
            ex_clr <= ex_active & txn_ex_match; // Could have multiple set bits
        else
            ex_clr <= ID_NUM'(0);
    end


    // --------------------------------------- //
    // Data/Response                           //
    // --------------------------------------- //

    always_comb txn_wvalid = s_axi_if.wvalid && txn_active;
    always_comb s_axi_if.wready = txn_wready && txn_active;

    // skidbuffer instance to pipeline data payload from AXI.
    skidbuffer #(
        .OPT_LOWPOWER   (0   ),
        .OPT_OUTREG     (0   ),
        //
        .OPT_PASSTHROUGH(0   ),
        .DW             (DW + BC + 1),
        .OPT_INITIAL    (1'b1)
    ) i_dp_skd (
        .i_clk  (clk             ),
        .i_reset(!rst_n          ),
        .i_valid(txn_wvalid      ),
        .o_ready(txn_wready      ),
        .i_data ({s_axi_if.wdata,
                  s_axi_if.wstrb,
                  s_axi_if.wlast}),
        .o_valid(dv_pre          ),
        .i_ready(!hld            ),
        .o_data ({wdata,
                  wstrb,
                  last }         )
    );

    always_comb dv = dv_pre && txn_allow;

    // Registered skidbuffer to pipeline response signals.
    // Skid buffer captures any response transfer if the
    // register output is busy with a previous response and is
    // stalled.
    // There is guaranteed to be space in the skid buffer because new
    // requests are stalled (AWREADY=0) until this buffer is ready.
    always_comb begin
        rp_valid = txn_final_beat;
        rp_resp  = txn_allow && (txn_err || err) ? AXI_RESP_SLVERR :
                   txn_allow && txn_ctx.lock     ? AXI_RESP_EXOKAY :
                                                   AXI_RESP_OKAY;
        rp_id    = txn_ctx.id;
    end

    skidbuffer #(
        .OPT_LOWPOWER   (0   ),
        .OPT_OUTREG     (1   ),
        //
        .OPT_PASSTHROUGH(0   ),
        .DW             (IW + $bits(axi_resp_e)),
        .OPT_INITIAL    (1'b1)
    ) i_rsp_skd (
        .i_clk  (clk             ),
        .i_reset(!rst_n          ),
        .i_valid(rp_valid        ),
        .o_ready(rp_ready        ),
        .i_data ({rp_resp,
                  rp_id}         ),
        .o_valid(s_axi_if.bvalid ),
        .i_ready(s_axi_if.bready ),
        .o_data ({s_axi_if.bresp,
                  s_axi_if.bid}  )
    );


    // --------------------------------------- //
    // Formal Properties                       //
    // --------------------------------------- //
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_AWVALID, s_axi_if.awvalid, clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_AWREADY, s_axi_if.awready, clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_AWADDR , (s_axi_if.awvalid ? s_axi_if.awaddr  : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_AWBURST, (s_axi_if.awvalid ? s_axi_if.awburst : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_AWSIZE , (s_axi_if.awvalid ? s_axi_if.awsize  : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_AWLEN  , (s_axi_if.awvalid ? s_axi_if.awlen   : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_AWUSER , (s_axi_if.awvalid ? s_axi_if.awuser  : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_AWID   , (s_axi_if.awvalid ? s_axi_if.awid    : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_AWLOCK , (s_axi_if.awvalid ? s_axi_if.awlock  : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_WVALID , s_axi_if.wvalid , clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_WREADY , s_axi_if.wready , clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_WDATA  , (s_axi_if.wvalid ? s_axi_if.wdata : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_WSTRB  , (s_axi_if.wvalid ? s_axi_if.wstrb : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_WLAST  , (s_axi_if.wvalid ? s_axi_if.wlast : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_BVALID , s_axi_if.bvalid , clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_BREADY , s_axi_if.bready , clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_BRESP  , (s_axi_if.bvalid ? s_axi_if.bresp : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_BID    , (s_axi_if.bvalid ? s_axi_if.bid   : '0), clk, !rst_n)

    // Handshake rules
    `CALIPTRA_ASSERT      (AXI_SUB_AW_HSHAKE_ERR, (s_axi_if.awvalid && !s_axi_if.awready) |=> s_axi_if.awvalid, clk, !rst_n)
    `CALIPTRA_ASSERT      (AXI_SUB_W_HSHAKE_ERR,  (s_axi_if.wvalid  && !s_axi_if.wready ) |=> s_axi_if.wvalid,  clk, !rst_n)
    `CALIPTRA_ASSERT      (AXI_SUB_B_HSHAKE_ERR,  (s_axi_if.bvalid  && !s_axi_if.bready ) |=> s_axi_if.bvalid,  clk, !rst_n)

    // Exclusive access rules:
    //   - Must have an address that is aligned to burst byte count
    //   - Byte count must be power of 2 inside 1:128
    //   - Max burst length = 16
    `CALIPTRA_ASSERT      (ERR_AXI_EX_UNALGN  , (s_axi_if.awvalid && s_axi_if.awlock) |-> ~|(s_axi_if.awaddr & ((1 << $clog2((1<<s_axi_if.awsize)*(s_axi_if.awlen+1)))-1)), clk, !rst_n)
    `CALIPTRA_ASSERT      (ERR_AXI_EX_BYTE_CNT, (s_axi_if.awvalid && s_axi_if.awlock) |-> ((1<<s_axi_if.awsize)*(s_axi_if.awlen+1) inside {1,2,4,8,16,32,64,128}), clk, !rst_n)
    `CALIPTRA_ASSERT      (ERR_AXI_EX_MAX_LEN,  (s_axi_if.awvalid && s_axi_if.awlock) |-> (s_axi_if.awlen < 16), clk, !rst_n)


    // --------------------------------------- //
    // Coverage                                //
    // --------------------------------------- //

endmodule
