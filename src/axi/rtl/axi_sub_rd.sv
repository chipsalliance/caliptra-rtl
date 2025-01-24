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
// AXI Read Subordinate
// -------------------------------------------------------------
// Description:
//   Subordinate to convert AXI protocol reads into internal component accesses
//
// Limitations:
//   - Drives RUSER to all 0's (i.e., RUSER is unimplemented)
//   - When multiple ID tracking is enabled, read responses are returned in the
//     same order they are received, regardless of ID.
//
// -------------------------------------------------------------

module axi_sub_rd import axi_pkg::*; #(
    parameter AW = 32,         // Address Width
    parameter DW = 32,         // Data Width
              BC = DW/8,       // Byte Count
              BW = $clog2(BC), // Byte count Width
    parameter UW = 32,         // User Width
    parameter IW = 1,          // ID Width
              ID_NUM = 1 << IW, // Don't override

    parameter C_LAT = 0    // Component latency in clock cycles from (dv&&!hld) -> rdata
                           // Must be const per component
                           // For registers, typically 0
                           // For SRAM, 1 or more
) (
    input clk,
    input rst_n,

    // AXI INF
    axi_if.r_sub s_axi_if,

    // Exclusive Access Signals
    // Enable exclusive access tracking w/ AxLOCK if EX_EN is set
    `ifdef CALIPTRA_AXI_SUB_EX_EN
    input  logic            [ID_NUM-1:0] ex_clr,
    output logic            [ID_NUM-1:0] ex_active,
    output struct packed {
        logic [AW-1:0] addr;
        logic [AW-1:0] addr_mask;
    } [ID_NUM-1:0] ex_ctx,
    `endif

    //COMPONENT INF
    output logic          dv,
    output logic [AW-1:0] addr, // Byte address
    output logic [UW-1:0] user,
    output logic [IW-1:0] id,
    output logic [2:0]    size,
    output logic          last, // Asserted with final 'dv' of a burst
    input  logic          hld,
    input  logic          err,

    input  logic [DW-1:0] rdata // Requires: Component dwidth == AXI dwidth
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
        logic [AW-1:0] addr;
        axi_burst_e    burst;
        logic [2:0]    size;
        logic [7:0]    len;
        logic [UW-1:0] user;
        logic [IW-1:0] id;
        logic          lock;
    } axi_ctx_t;

    typedef struct packed {
        logic [IW-1:0] id;
        logic [UW-1:0] user;
        axi_resp_e     resp;
        logic          last;
    } xfer_ctx_t;


    // --------------------------------------- //
    // Signals                                 //
    // --------------------------------------- //

    genvar cp; // Context pipeline
    genvar dp; // Data pipeline
    `ifdef CALIPTRA_AXI_SUB_EX_EN
    genvar ex; // Exclusive contexts
    `endif

    logic axi_out_of_rst;

    // Active transaction signals
    // track requests as they are sent to component
    axi_ctx_t            txn_ctx;
    logic      [AW-1:0]  txn_addr_nxt;
    logic      [   7:0]  txn_cnt; // Internal down-counter to track txn progress
    logic                txn_active;
    logic                txn_rvalid [C_LAT+1];
    xfer_ctx_t           txn_xfer_ctx [C_LAT+1];
    logic                txn_final_beat;

    // Data pipeline signals (skid buffer)
    // track data after it is received from component
    logic      [C_LAT+1:0] [DW-1:0] dp_rdata;
    xfer_ctx_t [C_LAT+1:0]          dp_xfer_ctx;
    logic      [C_LAT+1:0]          dp_rvalid;
    logic      [C_LAT+1:0]          dp_rready;


    // --------------------------------------- //
    // Address Request I/F                     //
    // --------------------------------------- //

    assign s_axi_if.arready = axi_out_of_rst && (!txn_active || txn_final_beat);

    always_ff@(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi_out_of_rst <= 1'b0;
        end
        else begin
            axi_out_of_rst <= 1'b1;
        end
    end

    // Indicates there are still reqs to be issued towards component.
    // This active signal deasserts after final dv to component, meaning data is
    // still in flight from component->AXI for C_LAT clocks after deassertion
    always_ff@(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            txn_active <= 1'b0;
        end
        else if (s_axi_if.arvalid && s_axi_if.arready) begin
            txn_active <= 1'b1;
        end
        else if (txn_final_beat) begin
            txn_active <= 1'b0;
        end
        else begin
            txn_active <= txn_active;
        end
    end

    always_ff@(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            txn_ctx <= '{default:0, burst:AXI_BURST_FIXED};
            txn_cnt <= '0;
        end
        else if (s_axi_if.arvalid && s_axi_if.arready) begin
            txn_ctx.addr  <= s_axi_if.araddr[AW-1:0];
            txn_ctx.burst <= axi_burst_e'(s_axi_if.arburst);
            txn_ctx.size  <= s_axi_if.arsize;
            txn_ctx.len   <= s_axi_if.arlen ;
            txn_ctx.user  <= s_axi_if.aruser;
            txn_ctx.id    <= s_axi_if.arid  ;
            txn_ctx.lock  <= s_axi_if.arlock;
            txn_cnt       <= s_axi_if.arlen ;
        end
        else if (txn_rvalid[0]) begin
            txn_ctx.addr  <= txn_addr_nxt;
            txn_ctx.burst <= txn_ctx.burst;
            txn_ctx.size  <= txn_ctx.size;
            txn_ctx.len   <= txn_ctx.len ;
            txn_ctx.user  <= txn_ctx.user;
            txn_ctx.id    <= txn_ctx.id  ;
            txn_ctx.lock  <= txn_ctx.lock;
            txn_cnt       <= |txn_cnt ? txn_cnt - 1 : txn_cnt; // Prevent underflow to 255 at end to reduce switching power. Extra logic cost worth it?
        end
    end

    // Only make the request to component if we have space in the pipeline to
    // store the result (under worst-case AXI backpressure)
    // To check this, look at the 'ready' output from all stages of the
    // skidbuffer pipeline (but omit the C_LAT+1 index because that comes from
    // axi rready)
    always_comb dv = txn_active && &dp_rready[C_LAT:0];
    always_comb txn_rvalid[0] = dv && !hld;

    // Asserts on the final beat of the COMPONENT INF which means it lags the
    // final AXI beat by at least C_LAT clocks (or more depending on backpressure)
    always_comb txn_final_beat = txn_rvalid[0] && txn_xfer_ctx[0].last;


    // --------------------------------------- //
    // Address Calculations                    //
    // --------------------------------------- //
    // Force aligned address to component
    always_comb addr = {txn_ctx.addr[AW-1:BW],BW'(0)};
    always_comb user = txn_ctx.user;
    always_comb id   = txn_ctx.id;
    always_comb size = txn_ctx.size;
    always_comb last = txn_cnt == 0;

    // Use full address to calculate next address (in case of arsize < data width)
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
    // Request Context Pipeline                //
    // --------------------------------------- //
    always_comb begin
        txn_xfer_ctx[0].id   = txn_ctx.id;
        txn_xfer_ctx[0].user = txn_ctx.user;
        txn_xfer_ctx[0].last = txn_cnt == 0;
        txn_xfer_ctx[0].resp =
    `ifdef CALIPTRA_AXI_SUB_EX_EN
                               txn_ctx.lock ? AXI_RESP_EXOKAY :
    `endif
                               AXI_RESP_OKAY;
    end

    // Shift Register to track requests made to component
    generate
    if (C_LAT > 0) begin: TXN_SR
        // Context is maintained alongside request while waiting for
        // component response to arrive
        for (cp = 1; cp <= C_LAT; cp++) begin: CTX_PIPELINE
            always_ff@(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    txn_rvalid[cp] <= 1'b0;
                end
                else begin
                    txn_rvalid[cp] <= txn_rvalid[cp-1];
                end
            end

            // No reset needed on data path -- txn_rvalid (control path) is reset
            always_ff@(posedge clk) begin
                txn_xfer_ctx[cp] <= txn_xfer_ctx[cp-1];
            end
        end: CTX_PIPELINE

    end: TXN_SR
    endgenerate


    // --------------------------------------- //
    // Exclusive Access Tracking               //
    // --------------------------------------- //
    `ifdef CALIPTRA_AXI_SUB_EX_EN
        // Exclusive access requires transaction LENGTH to be a power of 2,
        // so an address mask may be prepared by assuming the AxLEN value has
        // all consecutive LSB set to 1, then all 0's in higher order bits. After
        // shifting by the width of the transaction (AxSIZE), this mask can be applied
        // to AxADDR to give the aligned address relative to an exclusive access.
        // 
        logic [AW-1:0] addr_ex_algn_mask;
        always_comb begin
            case (BC) inside
                1:       addr_ex_algn_mask =  ~(AW'(txn_ctx.len));
                2:       addr_ex_algn_mask = (~(AW'(txn_ctx.len))) << txn_ctx.size[0];
                4:       addr_ex_algn_mask = (~(AW'(txn_ctx.len))) << txn_ctx.size[1:0];
                8:       addr_ex_algn_mask = (~(AW'(txn_ctx.len))) << txn_ctx.size[1:0];
                default: addr_ex_algn_mask = (~(AW'(txn_ctx.len))) << txn_ctx.size;
            endcase
        end

        always_ff@(posedge clk or negedge rst_n) begin
            if (!rst_n) begin
                ex_active <= '0;
            end
            // give 'set' precedence over 'clr' in case of same ID
            else if ((txn_rvalid[0] && txn_ctx.lock) && |ex_clr) begin
                ex_active <= (ex_active & ~ex_clr) | (1 << txn_ctx.id);
            end
            else if (txn_rvalid[0] && txn_ctx.lock) begin
                ex_active <= ex_active | (1 << txn_ctx.id);
            end
            else if (|ex_clr) begin
                ex_active <= ex_active & ~ex_clr;
            end
            else begin
                ex_active <= ex_active;
            end
        end

        for (ex = 0; ex < ID_NUM; ex++) begin: EX_CTX_TRACKER
            // TODO: reset?
            always_ff@(posedge clk) begin
                if (txn_rvalid[0] && txn_ctx.lock && (txn_ctx.id == ex)) begin
                    ex_ctx[ex].addr      <= txn_ctx.addr;
                    ex_ctx[ex].addr_mask <= addr_ex_algn_mask;
                end
                // Ignore the clear case, as ex_active is the ctrl path
                //else if (ex_clr[ex]) begin
                //end
                else begin
                    ex_ctx[ex] <= ex_ctx[ex];
                end
            end
        end
    `endif


    // --------------------------------------- //
    // Data/Response                           //
    // --------------------------------------- //
    always_comb dp_rvalid[0]   = txn_rvalid[C_LAT];
    always_comb dp_rdata[0]    = rdata;
    always_comb begin
        dp_xfer_ctx[0].id   = txn_xfer_ctx[C_LAT].id;
        dp_xfer_ctx[0].user = txn_xfer_ctx[C_LAT].user; // NOTE: Unused after it enters data pipeline
        dp_xfer_ctx[0].resp = err   ? AXI_RESP_SLVERR :
    `ifdef CALIPTRA_AXI_SUB_EX_EN
                                      txn_xfer_ctx[C_LAT].resp;
    `else
                                      AXI_RESP_OKAY;
    `endif
        dp_xfer_ctx[0].last = txn_xfer_ctx[C_LAT].last;
    end

    generate
        for (dp = 0; dp <= C_LAT; dp++) begin: DATA_PIPELINE
            // skidbuffer instance to pipeline data payload + context to AXI,
            // after response is received from component.
            // This is necessary when there is latency from dv->rdata,
            // because AXI R channel can be stalled by dropping rready,
            // and we can't drop the data (which was requested N cycles ago)
            skidbuffer #(
                .OPT_LOWPOWER   (0   ),
                .OPT_OUTREG     (0   ),
                //
                .OPT_PASSTHROUGH(0   ),
                .DW             (DW + $bits(xfer_ctx_t))
            ) i_dp_skd (
                .i_clk  (clk                ),
                .i_reset(rst_n              ),
                .i_valid(dp_rvalid[dp]      ),
                .o_ready(dp_rready[dp]      ),
                .i_data ({dp_rdata[dp],
                          dp_xfer_ctx[dp]}  ),
                .o_valid(dp_rvalid[dp+1]    ),
                .i_ready(dp_rready[dp+1]    ),
                .o_data ({dp_rdata[dp+1],
                          dp_xfer_ctx[dp+1]})
            );

        end: DATA_PIPELINE
    endgenerate

    always_comb dp_rready[C_LAT+1] = s_axi_if.rready;
    always_comb begin
        s_axi_if.rvalid = dp_rvalid[C_LAT+1];
        s_axi_if.rlast  = dp_xfer_ctx[C_LAT+1].last;
        s_axi_if.rdata  = dp_rdata[C_LAT+1];
        s_axi_if.rid    = dp_xfer_ctx[C_LAT+1].id;
        s_axi_if.ruser  = '0;
        s_axi_if.rresp  = dp_xfer_ctx[C_LAT+1].resp;
    end


    // --------------------------------------- //
    // Formal Properties                       //
    // --------------------------------------- //
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_ARVALID, s_axi_if.arvalid, clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_ARREADY, s_axi_if.arready, clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_ARADDR , (s_axi_if.arvalid ? s_axi_if.araddr  : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_ARBURST, (s_axi_if.arvalid ? s_axi_if.arburst : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_ARSIZE , (s_axi_if.arvalid ? s_axi_if.arsize  : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_ARLEN  , (s_axi_if.arvalid ? s_axi_if.arlen   : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_ARUSER , (s_axi_if.arvalid ? s_axi_if.aruser  : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_ARID   , (s_axi_if.arvalid ? s_axi_if.arid    : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_ARLOCK , (s_axi_if.arvalid ? s_axi_if.arlock  : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_RVALID , s_axi_if.rvalid , clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_RREADY , s_axi_if.rready , clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_RDATA  , (s_axi_if.rvalid ? s_axi_if.rdata : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_RRESP  , (s_axi_if.rvalid ? s_axi_if.rresp : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_RID    , (s_axi_if.rvalid ? s_axi_if.rid   : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_RUSER  , (s_axi_if.rvalid ? s_axi_if.ruser : '0), clk, !rst_n)
    `CALIPTRA_ASSERT_KNOWN(AXI_SUB_X_RLAST  , (s_axi_if.rvalid ? s_axi_if.rlast : '0), clk, !rst_n)

    // Handshake rules
    `CALIPTRA_ASSERT      (AXI_SUB_AR_HSHAKE_ERR, (s_axi_if.arvalid && !s_axi_if.arready) |=> s_axi_if.arvalid, clk, !rst_n)
    `CALIPTRA_ASSERT      (AXI_SUB_R_HSHAKE_ERR,  (s_axi_if.rvalid  && !s_axi_if.rready ) |=> s_axi_if.rvalid,  clk, !rst_n)

    `CALIPTRA_ASSERT_NEVER(ERR_AXI_RD_DROP  , dp_rvalid[0] && !dp_rready[0], clk, !rst_n)
    `CALIPTRA_ASSERT_NEVER(ERR_AXI_RD_X     , dp_rvalid[0] && $isunknown({dp_rdata[0],dp_xfer_ctx[0]}), clk, !rst_n)
    // Exclusive access rules:
    //   - Must have an address that is aligned to burst byte count
    //   - Byte count must be power of 2 inside 1:128
    //   - Max burst length = 16
    `CALIPTRA_ASSERT      (ERR_AXI_EX_UNALGN  , (s_axi_if.arvalid && s_axi_if.arlock) |-> ~|(s_axi_if.araddr & ((1 << $clog2((1<<s_axi_if.arsize)*(s_axi_if.arlen+1)))-1)), clk, !rst_n)
    `CALIPTRA_ASSERT      (ERR_AXI_EX_BYTE_CNT, (s_axi_if.arvalid && s_axi_if.arlock) |-> ((1<<s_axi_if.arsize)*(s_axi_if.arlen+1) inside {1,2,4,8,16,32,64,128}), clk, !rst_n)
    `CALIPTRA_ASSERT      (ERR_AXI_EX_MAX_LEN,  (s_axi_if.arvalid && s_axi_if.arlock) |-> (s_axi_if.arlen < 16), clk, !rst_n)

    genvar sva_ii;
    generate
        if (C_LAT > 0) begin
            for (sva_ii = 0; sva_ii < C_LAT; sva_ii++) begin
                // Last stage should be first to fill and first to go empty
                `CALIPTRA_ASSERT_NEVER(ERR_RD_SKD_BUF_FILL,  $fell(dp_rready[sva_ii+1]) && !dp_rready[sva_ii], clk, !rst_n)
                `CALIPTRA_ASSERT_NEVER(ERR_RD_SKD_BUF_DRAIN, $rose(dp_rready[sva_ii+1]) &&  dp_rready[sva_ii], clk, !rst_n)
            end
        end
    endgenerate


    // --------------------------------------- //
    // Coverage                                //
    // --------------------------------------- //


endmodule
