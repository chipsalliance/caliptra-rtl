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
`default_nettype none

module caliptra_top_tb_axi_complex import caliptra_top_tb_pkg::*; (
    input logic core_clk,
    input logic cptra_rst_b,
    axi_if m_axi_if,
    output logic recovery_data_avail,
    input var axi_complex_ctrl_t ctrl
);

    import axi_pkg::*;
    import soc_ifc_pkg::*;

    //=========================================================================-
    // Local i/fs
    //=========================================================================-
    axi_if #(
        .AW(AXI_SRAM_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .IW(CPTRA_AXI_DMA_ID_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH)
    ) axi_sram_if (.clk(core_clk), .rst_n(cptra_rst_b));
    logic axi_sram_if_bvalid_force; // Intermediary signal that can be 'forced' without impacting axi_sub logic
    axi_if #(
        .AW(AXI_FIFO_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .IW(CPTRA_AXI_DMA_ID_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH)
    ) axi_fifo_if (.clk(core_clk), .rst_n(cptra_rst_b));
    logic axi_fifo_if_bvalid_force; // Intermediary signal that can be 'forced' without impacting axi_sub logic


    //=========================================================================-
    // AXI Protocol Checker
    //=========================================================================-
    `ifdef AXI4PC
        Axi4PC #(
            .DATA_WIDTH  (CPTRA_AXI_DMA_DATA_WIDTH    ),
            .WID_WIDTH   (CPTRA_AXI_DMA_ID_WIDTH      ),
            .RID_WIDTH   (CPTRA_AXI_DMA_ID_WIDTH      ),
            .ADDR_WIDTH  (`CALIPTRA_AXI_DMA_ADDR_WIDTH),
            .AWUSER_WIDTH(CPTRA_AXI_DMA_USER_WIDTH    ),
            .WUSER_WIDTH (CPTRA_AXI_DMA_USER_WIDTH    ),
            .BUSER_WIDTH (CPTRA_AXI_DMA_USER_WIDTH    ),
            .ARUSER_WIDTH(CPTRA_AXI_DMA_USER_WIDTH    ),
            .RUSER_WIDTH (CPTRA_AXI_DMA_USER_WIDTH    ),
//            .MAXWAITS    (256                         ),
            .RecMaxWaitOn(0                           )
        ) axi4_pc_inst (
            // Global Signals
            .ACLK   (core_clk   ),
            .ARESETn(cptra_rst_b),

            // Write Address Channel
            .AWID    (m_axi_if.awid),
            .AWADDR  (m_axi_if.awaddr),
            .AWLEN   (m_axi_if.awlen),
            .AWSIZE  (m_axi_if.awsize),
            .AWBURST (m_axi_if.awburst),
            .AWLOCK  (m_axi_if.awlock),
            .AWCACHE (4'h0),
            .AWPROT  (3'h0),
            .AWQOS   (4'h0),
            .AWREGION(4'h0),
            .AWUSER  (m_axi_if.awuser),
            .AWVALID (m_axi_if.awvalid),
            .AWREADY (m_axi_if.awready),

            // Write Channel
            .WLAST   (m_axi_if.wlast),
            .WDATA   (m_axi_if.wdata),
            .WSTRB   (m_axi_if.wstrb),
            .WUSER   (m_axi_if.wuser),
            .WVALID  (m_axi_if.wvalid),
            .WREADY  (m_axi_if.wready),

            // Write Response Channel
            .BID     (m_axi_if.bid),
            .BRESP   (m_axi_if.bresp),
            .BUSER   (m_axi_if.buser),
            .BVALID  (m_axi_if.bvalid),
            .BREADY  (m_axi_if.bready),

            // Read Address Channel
            .ARID    (m_axi_if.arid),
            .ARADDR  (m_axi_if.araddr),
            .ARLEN   (m_axi_if.arlen),
            .ARSIZE  (m_axi_if.arsize),
            .ARBURST (m_axi_if.arburst),
            .ARLOCK  (m_axi_if.arlock),
            .ARCACHE (4'h0),
            .ARPROT  (3'h0),
            .ARQOS   (4'h0),
            .ARREGION(4'h0),
            .ARUSER  (m_axi_if.aruser),
            .ARVALID (m_axi_if.arvalid),
            .ARREADY (m_axi_if.arready),

            // Read Channel
            .RID     (m_axi_if.rid),
            .RLAST   (m_axi_if.rlast),
            .RDATA   (m_axi_if.rdata),
            .RRESP   (m_axi_if.rresp),
            .RUSER   (m_axi_if.ruser),
            .RVALID  (m_axi_if.rvalid),
            .RREADY  (m_axi_if.rready),

            // Low power interface
            .CACTIVE (1'b0),
            .CSYSREQ (1'b0),
            .CSYSACK (1'b0)
        );
    `endif


    //=========================================================================-
    // Delay Injection
    //=========================================================================-
    `define GENERIC_2SIG_DLY_TEMPLATE(GEN_NAME, cnt_var, rdy_sig_path, vld_sig_path)                                                        \
        logic [11:0] cnt_var;                                                                                                               \
        bit GEN_NAME``_past_shake_stall;                                                                                                    \
        always@(posedge core_clk)                                                                                                           \
            GEN_NAME``_past_shake_stall <= vld_sig_path && !rdy_sig_path;                                                                   \
        initial begin: GEN_NAME                                                                                                             \
            `ifndef VERILATOR                                                                                                               \
            if (!std::randomize(cnt_var) with {cnt_var dist {[0:1] :/ 500, [2:7] :/ 75, [8:31] :/ 3, [32:255] :/ 1}; })                     \
                $fatal("Randomize %s failed", `"cnt_var`");                                                                                 \
            `else                                                                                                                           \
            cnt_var = $urandom_range(7,0);                                                                                                  \
            `endif                                                                                                                          \
            forever begin                                                                                                                   \
                @(negedge core_clk)                                                                                                         \
                if (ctrl.rand_delays) begin                                                                                                 \
                    if (|cnt_var && !GEN_NAME``_past_shake_stall) begin                                                                     \
                        cnt_var = cnt_var - 1;                                                                                              \
                        force rdy_sig_path = 1'b0;                                                                                          \
                        force vld_sig_path = 1'b0;                                                                                          \
                    end                                                                                                                     \
                    `ifndef VERILATOR                                                                                                       \
                    else if (!std::randomize(cnt_var) with {cnt_var dist {[0:1] :/ 500, [2:7] :/ 75, [8:31] :/ 3, [32:255] :/ 1}; }) begin  \
                        $fatal("Randomize %s failed", `"cnt_var`");                                                                         \
                    end                                                                                                                     \
                    `endif                                                                                                                  \
                    else begin                                                                                                              \
                        `ifdef VERILATOR                                                                                                    \
                        cnt_var = $urandom_range(7,0);                                                                                      \
                        `endif                                                                                                              \
                        release rdy_sig_path;                                                                                               \
                        release vld_sig_path;                                                                                               \
                    end                                                                                                                     \
                end                                                                                                                         \
                else begin                                                                                                                  \
                    release rdy_sig_path;                                                                                                   \
                    release vld_sig_path;                                                                                                   \
                end                                                                                                                         \
            end                                                                                                                             \
        end: GEN_NAME                                                                                                                       \

    // --------------------- SRAM ---------------------
    `GENERIC_2SIG_DLY_TEMPLATE (AXI_SRAM_AR_DLY, i_axi_sram_ar_dly_cnt, axi_sram_if.arready                               , axi_sram_if.arvalid                               )
    `GENERIC_2SIG_DLY_TEMPLATE (AXI_SRAM_R_DLY , i_axi_sram_r_dly_cnt,  axi_sram_if.rready                                , axi_sram_if.rvalid                                )
    `GENERIC_2SIG_DLY_TEMPLATE (AXI_SRAM_AW_DLY, i_axi_sram_aw_dly_cnt, i_axi_sram.i_axi_sub.i_axi_sub_wr.axi_awready_q   , i_axi_sram.i_axi_sub.i_axi_sub_wr.axi_awvalid_q   )
    `GENERIC_2SIG_DLY_TEMPLATE (AXI_SRAM_W_DLY , i_axi_sram_w_dly_cnt,  i_axi_sram.i_axi_sub.i_axi_sub_wr.txn_wready      , i_axi_sram.i_axi_sub.i_axi_sub_wr.txn_wvalid      )
    `GENERIC_2SIG_DLY_TEMPLATE (AXI_SRAM_B_DLY , i_axi_sram_b_dly_cnt,  axi_sram_if.bready                                , axi_sram_if_bvalid_force                          )
    // --------------------- FIFO ---------------------
    `GENERIC_2SIG_DLY_TEMPLATE (AXI_FIFO_AR_DLY, i_axi_fifo_ar_dly_cnt, axi_fifo_if.arready                               , axi_fifo_if.arvalid                               )
    `GENERIC_2SIG_DLY_TEMPLATE (AXI_FIFO_R_DLY , i_axi_fifo_r_dly_cnt,  axi_fifo_if.rready                                , axi_fifo_if.rvalid                                )
    `GENERIC_2SIG_DLY_TEMPLATE (AXI_FIFO_AW_DLY, i_axi_fifo_aw_dly_cnt, i_axi_fifo.i_axi_sub.i_axi_sub_wr.axi_awready_q   , i_axi_fifo.i_axi_sub.i_axi_sub_wr.axi_awvalid_q   )
    `GENERIC_2SIG_DLY_TEMPLATE (AXI_FIFO_W_DLY , i_axi_fifo_w_dly_cnt,  i_axi_fifo.i_axi_sub.i_axi_sub_wr.txn_wready      , i_axi_fifo.i_axi_sub.i_axi_sub_wr.txn_wvalid      )
    `GENERIC_2SIG_DLY_TEMPLATE (AXI_FIFO_B_DLY , i_axi_fifo_b_dly_cnt,  axi_fifo_if.bready                                , axi_fifo_if_bvalid_force                          )


    //=========================================================================-
    // Dummy interconnect
    //=========================================================================-
    // --------------------- Endpoint mux ---------------------
    logic [1:0] sram_r_active;
    logic       sram_ar_hshake;
    logic       sram_rlast_hshake;

    logic [2:0] sram_w_active;
    logic       sram_aw_hshake;
    logic       sram_b_hshake;

    logic [1:0] fifo_r_active;
    logic       fifo_ar_hshake;
    logic       fifo_rlast_hshake;

    logic [2:0] fifo_w_active;
    logic       fifo_aw_hshake;
    logic       fifo_b_hshake;

    logic       illegal_read_addr;
    logic       illegal_write_addr;
    
    assign illegal_read_addr = !( (m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH]) ||
                              (m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH]) );
    assign illegal_write_addr = !( (m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH]) ||
                               (m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH]) );

    // AXI SLVERR response state for illegal write address
    typedef enum logic [1:0] {IDLE, DATA, RESP} illegal_wr_state_e;
    illegal_wr_state_e illegal_wr_state = IDLE;
    logic [CPTRA_AXI_DMA_ID_WIDTH-1:0] illegal_wr_id;
    logic illegal_wr_pending;
    logic [7:0] illegal_wr_burst_cnt; // Counter for W beats
    logic [7:0] illegal_wr_burst_len; // Latched AWLEN

    // Outputs from illegal write state machine
    logic illegal_wr_bvalid;
    logic [1:0] illegal_wr_bresp;
    logic [CPTRA_AXI_DMA_ID_WIDTH-1:0] illegal_wr_bid;

    always_ff @(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            illegal_wr_bvalid    <= 1'b0;
            illegal_wr_bresp     <= 2'b00;
            illegal_wr_bid       <= '0;
            illegal_wr_state     <= IDLE;
            illegal_wr_pending   <= 1'b0;
            illegal_wr_burst_cnt <= 8'd0;
            illegal_wr_burst_len <= 8'd0;
        end else begin
            case (illegal_wr_state)
                IDLE: begin
                    illegal_wr_bvalid <= 1'b0;
                    if (illegal_write_addr && m_axi_if.awvalid && m_axi_if.awready) begin
                        illegal_wr_state   <= DATA;
                        illegal_wr_bid     <= m_axi_if.awid;
                        illegal_wr_pending <= 1'b1;
                        illegal_wr_burst_cnt <= 8'd0;
                        illegal_wr_burst_len <= m_axi_if.awlen;
                    end
                end
                DATA: begin
                    if (m_axi_if.wvalid && m_axi_if.wready) begin
                        illegal_wr_burst_cnt <= illegal_wr_burst_cnt + 1'b1;
                        if (m_axi_if.wlast) begin
                            illegal_wr_state <= RESP;
                            illegal_wr_bvalid <= 1'b1; // Assert bvalid immediately after last W beat
                            illegal_wr_bresp  <= AXI_RESP_SLVERR;
                        end
                    end
                end
                RESP: begin
                    // bvalid remains asserted until bready
                    if (m_axi_if.bready) begin
                        illegal_wr_bvalid    <= 1'b0;
                        illegal_wr_state     <= IDLE;
                        illegal_wr_pending   <= 1'b0;
                        illegal_wr_burst_cnt <= 8'd0;
                        illegal_wr_burst_len <= 8'd0;
                    end
                end
            endcase
        end
    end

    // AXI SLVERR response state for illegal read address
    typedef enum logic [1:0] {RD_IDLE, RD_RESP} illegal_rd_state_e;
    illegal_rd_state_e illegal_rd_state = RD_IDLE;
    logic [CPTRA_AXI_DMA_ID_WIDTH-1:0] illegal_rd_id;
    logic illegal_rd_pending;
    logic [7:0] illegal_rd_burst_cnt; // Counter for R beats
    logic [7:0] illegal_rd_burst_len; // Latched ARLEN (AXI: beats = arlen+1)
    logic [7:0] illegal_rd_burst_len_next; // Temporary latch for ARLEN

    // Outputs from illegal read state machine
    logic illegal_rd_rvalid;
    logic [1:0] illegal_rd_rresp;
    logic [CPTRA_AXI_DMA_ID_WIDTH-1:0] illegal_rd_rid;
    logic [CPTRA_AXI_DMA_DATA_WIDTH-1:0] illegal_rd_rdata;
    logic illegal_rd_rlast;

    always_ff @(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            illegal_rd_rvalid    <= 1'b0;
            illegal_rd_rresp     <= 2'b00;
            illegal_rd_rid       <= '0;
            illegal_rd_rdata     <= '0;
            illegal_rd_rlast     <= 1'b0;
            illegal_rd_state     <= RD_IDLE;
            illegal_rd_pending   <= 1'b0;
            illegal_rd_burst_cnt <= 8'd0;
            illegal_rd_burst_len <= 8'd0;
            illegal_rd_burst_len_next <= 8'd0;
        end else begin
            case (illegal_rd_state)
                RD_IDLE: begin
                    illegal_rd_rvalid <= 1'b0;
                    if (illegal_read_addr && m_axi_if.arvalid && m_axi_if.arready) begin
                        illegal_rd_burst_len_next = m_axi_if.arlen; // Latch ARLEN immediately
                        $display("[ILLEGAL_RD] Handshake: m_axi_if.arlen=0x%0h, assigned illegal_rd_burst_len=0x%0h", m_axi_if.arlen, illegal_rd_burst_len_next);
                        illegal_rd_state   <= RD_RESP;
                        illegal_rd_rid     <= m_axi_if.arid;
                        illegal_rd_pending <= 1'b1;
                        illegal_rd_burst_cnt <= 8'd0;
                        illegal_rd_burst_len <= illegal_rd_burst_len_next; // Use latched value for burst_len
                    end
                end
                RD_RESP: begin
                    illegal_rd_rvalid <= 1'b1;
                    illegal_rd_rresp  <= AXI_RESP_SLVERR;
                    illegal_rd_rdata  <= '0;
                    illegal_rd_rlast  <= (illegal_rd_burst_cnt == illegal_rd_burst_len);
                    if (m_axi_if.rready && illegal_rd_rvalid) begin
                        if (illegal_rd_burst_cnt == illegal_rd_burst_len) begin // last beat
                            illegal_rd_state     <= RD_IDLE;
                            illegal_rd_pending   <= 1'b0;
                            illegal_rd_rvalid    <= 1'b0;
                        end else begin
                            illegal_rd_burst_cnt <= illegal_rd_burst_cnt + 1'b1;
                        end
                    end
                end
            endcase
        end
    end

    always_comb begin
        // AXI AR 
        m_axi_if.arready = illegal_read_addr ? 1'b1 :
                            (m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH]) ? axi_sram_if.arready :
                            (m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH]) ? axi_fifo_if.arready :
                            1'b0;

        m_axi_if.rvalid = illegal_rd_pending ? illegal_rd_rvalid :
                          sram_r_active ? axi_sram_if.rvalid :
                          fifo_r_active ? axi_fifo_if.rvalid :
                          '0;
        m_axi_if.rresp  = illegal_rd_pending ? illegal_rd_rresp :
                          sram_r_active ? axi_sram_if.rresp :
                          fifo_r_active ? axi_fifo_if.rresp :
                          '0;
        m_axi_if.rid    = illegal_rd_pending ? illegal_rd_rid :
                          sram_r_active ? axi_sram_if.rid :
                          fifo_r_active ? axi_fifo_if.rid :
                          '0;
        m_axi_if.rdata  = illegal_rd_pending ? illegal_rd_rdata :
                          sram_r_active ? axi_sram_if.rdata :
                          fifo_r_active ? axi_fifo_if.rdata :
                          '0;
        m_axi_if.rlast  = illegal_rd_pending ? illegal_rd_rlast :
                          sram_r_active ? axi_sram_if.rlast :
                          fifo_r_active ? axi_fifo_if.rlast :
                          '0;
        m_axi_if.ruser  = sram_r_active ? axi_sram_if.ruser :
                          fifo_r_active ? axi_fifo_if.ruser :
                          '0;
        // AXI AW 
        m_axi_if.awready = illegal_write_addr ? 1'b1 :
                            (m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH]) ? axi_sram_if.awready :
                            (m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH]) ? axi_fifo_if.awready :
                            1'b0;
        // AXI B (legal path only)
        m_axi_if.bresp  = illegal_wr_pending ? illegal_wr_bresp :
                            sram_w_active ? axi_sram_if.bresp :
                            fifo_w_active ? axi_fifo_if.bresp :
                            '0;
        m_axi_if.bvalid = illegal_wr_pending ? illegal_wr_bvalid :
                            sram_w_active ? axi_sram_if_bvalid_force :
                            fifo_w_active ? axi_fifo_if_bvalid_force :
                            '0;
        m_axi_if.bid    = illegal_wr_pending ? illegal_wr_bid :
                            sram_w_active ? axi_sram_if.bid :
                            fifo_w_active ? axi_fifo_if.bid :
                            '0;
        m_axi_if.buser  = sram_w_active ? axi_sram_if.buser :
                          fifo_w_active ? axi_fifo_if.buser :
                          '0;
        // AXI W 
        m_axi_if.wready = illegal_wr_pending ? 1'b1 : 
                           sram_w_active ? axi_sram_if.wready :
                          fifo_w_active ? axi_fifo_if.wready :
                          1'b0;
    end

    // --------------------- AXI Complex Endpoint Decode ---------------------    
    //`CALIPTRA_ASSERT(AXI_COMPLEX_RD_DECODE, m_axi_if.arvalid |-> (m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH]) || (m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH]), core_clk, !cptra_rst_b)
    //`CALIPTRA_ASSERT(AXI_COMPLEX_WR_DECODE, m_axi_if.awvalid |-> (m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH]) || (m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH]), core_clk, !cptra_rst_b)

    // --------------------- SRAM Endpoint ---------------------
    always_comb begin
        sram_ar_hshake    = axi_sram_if.arvalid && axi_sram_if.arready;
        sram_rlast_hshake = axi_sram_if.rvalid  && axi_sram_if.rready && axi_sram_if.rlast;
    end
    always_ff@(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            sram_r_active <= 2'b0;;
        end
        else begin
            case ({sram_ar_hshake,sram_rlast_hshake}) inside
                2'b00:
                    sram_r_active <= sram_r_active;
                2'b01:
                    if (sram_r_active)
                        sram_r_active <= sram_r_active - 2'b1;
                    else
                        $fatal("Read data with last, but no reads outstanding!");
                2'b10:
                    sram_r_active <= sram_r_active + 2'b1;
                2'b11:
                    sram_r_active <= sram_r_active;
            endcase
        end
    end
    `CALIPTRA_ASSERT_NEVER(SRAM_GT2_RD_PENDING, sram_r_active > 2, core_clk, !cptra_rst_b)
    always_comb begin
        sram_aw_hshake    = axi_sram_if.awvalid      && axi_sram_if.awready;
        sram_b_hshake     = axi_sram_if_bvalid_force && axi_sram_if.bready;
    end
    always_ff@(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            sram_w_active <= 3'b0;
        end
        else begin
            case ({sram_aw_hshake,sram_b_hshake}) inside
                2'b00:
                    sram_w_active <= sram_w_active;
                2'b01:
                    if (sram_w_active)
                        sram_w_active <= sram_w_active - 3'b1;
                    else
                        $fatal("Write response, but no writes outstanding!");
                2'b10:
                    sram_w_active <= sram_w_active + 3'b1;
                2'b11:
                    sram_w_active <= sram_w_active;
            endcase
        end
    end
    // In rare cases, small write requests while generating backpressure on Write response channel can cause
    // 1 write response pending on output reg
    // 1 write response pending in response buffer
    // 1 write request active
    // 1 write request accepted and pending
    `CALIPTRA_ASSERT_NEVER(SRAM_GT4_WR_PENDING, (sram_w_active == 4) && sram_aw_hshake && !sram_b_hshake, core_clk, !cptra_rst_b)

    // AXI AR
    assign axi_sram_if.arvalid       = m_axi_if.arvalid && m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH];
    assign axi_sram_if.araddr        = m_axi_if.araddr[AXI_SRAM_ADDR_WIDTH-1:0];
    assign axi_sram_if.arburst       = m_axi_if.arburst;
    assign axi_sram_if.arsize        = m_axi_if.arsize ;
    assign axi_sram_if.arlen         = m_axi_if.arlen  ;
    assign axi_sram_if.aruser        = m_axi_if.aruser ;
    assign axi_sram_if.arid          = m_axi_if.arid   ;
    assign axi_sram_if.arlock        = m_axi_if.arlock ;

    // AXI R                                    
    assign axi_sram_if.rready        = sram_r_active ? m_axi_if.rready : '0;

    // AXI AW                                   
    assign axi_sram_if.awvalid       = m_axi_if.awvalid && m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH];
    assign axi_sram_if.awaddr        = m_axi_if.awaddr[AXI_SRAM_ADDR_WIDTH-1:0];
    assign axi_sram_if.awburst       = m_axi_if.awburst;
    assign axi_sram_if.awsize        = m_axi_if.awsize ;
    assign axi_sram_if.awlen         = m_axi_if.awlen  ;
    assign axi_sram_if.awuser        = m_axi_if.awuser ;
    assign axi_sram_if.awid          = m_axi_if.awid   ;
    assign axi_sram_if.awlock        = m_axi_if.awlock ;

    // AXI W                                    
    assign axi_sram_if.wvalid        = sram_w_active ? m_axi_if.wvalid : '0;
    assign axi_sram_if.wdata         = sram_w_active ? m_axi_if.wdata  : '0;
    assign axi_sram_if.wstrb         = sram_w_active ? m_axi_if.wstrb  : '0;
    assign axi_sram_if.wuser         = sram_w_active ? m_axi_if.wuser  : '0;
    assign axi_sram_if.wlast         = sram_w_active ? m_axi_if.wlast  : '0;

    // AXI B
    assign axi_sram_if.bready        = sram_w_active ? m_axi_if.bready : '0;
    assign axi_sram_if_bvalid_force  = axi_sram_if.bvalid;

    // Fake "MCU" SRAM block
    caliptra_axi_sram #(
        .AW   (AXI_SRAM_ADDR_WIDTH     ),
        .DW   (CPTRA_AXI_DMA_DATA_WIDTH),
        .UW   (CPTRA_AXI_DMA_USER_WIDTH),
        .IW   (CPTRA_AXI_DMA_ID_WIDTH  ),
        .EX_EN(0                       )
    ) i_axi_sram (
        .clk(core_clk),
        .rst_n(cptra_rst_b),

        // AXI INF
        .s_axi_w_if(axi_sram_if.w_sub),
        .s_axi_r_if(axi_sram_if.r_sub)
    );
    `ifdef VERILATOR
    initial i_axi_sram.i_sram.ram = '{default:'{default:8'h00}};
    `else
    initial i_axi_sram.i_sram.ram = '{default:8'h00};
    `endif

    // --------------------- FIFO Endpoint ---------------------
    always_comb begin
        fifo_ar_hshake    = axi_fifo_if.arvalid && axi_fifo_if.arready;
        fifo_rlast_hshake = axi_fifo_if.rvalid  && axi_fifo_if.rready && axi_fifo_if.rlast;
    end
    always_ff@(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            fifo_r_active <= 2'b0;;
        end
        else begin
            case ({fifo_ar_hshake,fifo_rlast_hshake}) inside
                2'b00:
                    fifo_r_active <= fifo_r_active;
                2'b01:
                    if (fifo_r_active)
                        fifo_r_active <= fifo_r_active - 2'b1;
                    else
                        $fatal("Read data with last, but no reads outstanding!");
                2'b10:
                    fifo_r_active <= fifo_r_active + 2'b1;
                2'b11:
                    fifo_r_active <= fifo_r_active;
            endcase
        end
    end
    `CALIPTRA_ASSERT_NEVER(FIFO_GT2_RD_PENDING, fifo_r_active > 2, core_clk, !cptra_rst_b)
    always_comb begin
        fifo_aw_hshake    = axi_fifo_if.awvalid      && axi_fifo_if.awready;
        fifo_b_hshake     = axi_fifo_if_bvalid_force && axi_fifo_if.bready;
    end
    always_ff@(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            fifo_w_active <= 3'b0;
        end
        else begin
            case ({fifo_aw_hshake,fifo_b_hshake}) inside
                2'b00:
                    fifo_w_active <= fifo_w_active;
                2'b01:
                    if (fifo_w_active)
                        fifo_w_active <= fifo_w_active - 3'b1;
                    else
                        $fatal("Write response, but no writes outstanding!");
                2'b10:
                    fifo_w_active <= fifo_w_active + 3'b1;
                2'b11:
                    fifo_w_active <= fifo_w_active;
            endcase
        end
    end
    // In rare cases, small write requests while generating backpressure on Write response channel can cause
    // 1 write response pending on output reg
    // 1 write response pending in response buffer
    // 1 write request active
    // 1 write request accepted and pending
    `CALIPTRA_ASSERT_NEVER(FIFO_GT4_WR_PENDING, (fifo_w_active == 4) && fifo_aw_hshake && !fifo_b_hshake, core_clk, !cptra_rst_b)

    logic [31:0] fifo_aw_hshake_count, fifo_b_hshake_count;
    logic [31:0] fifo_b_hshake_count_expected;
    logic [11:0] awlen_active;
    logic awlen_busy;
    int awlen_active_q [$];

    initial begin
        forever begin
            @(posedge core_clk);
            if (!cptra_rst_b) begin
                awlen_active = '0;
                awlen_busy = '0;
                awlen_active_q.delete();
                fifo_b_hshake_count_expected = 0;
            end
            if (fifo_aw_hshake && awlen_busy) begin
                awlen_active_q.push_front(axi_fifo_if.awlen);
            end
            else if (fifo_aw_hshake) begin
                awlen_active = axi_fifo_if.awlen;
                awlen_busy = 1;
            end
            if (axi_fifo_if.wvalid && axi_fifo_if.wready && (awlen_busy == 0)) begin
                $fatal("TB: Write data to AXI Complex FIFO while awlen_busy == 0; check TB for logic error.");
            end
            else if (axi_fifo_if.wvalid && axi_fifo_if.wready && (awlen_active == 0)) begin
                awlen_busy = 0;
                fifo_b_hshake_count_expected += 1;
            end
            else if (axi_fifo_if.wvalid && axi_fifo_if.wready) begin
                awlen_active -= 1;
            end
            if (!awlen_busy && (awlen_active_q.size() != 0)) begin
                awlen_busy = 1;
                awlen_active = awlen_active_q.pop_back();
            end
        end
    end

    always@(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            fifo_aw_hshake_count <= '0;
            fifo_b_hshake_count  <= '0;
        end
        else begin
            fifo_aw_hshake_count <= fifo_aw_hshake_count + (fifo_aw_hshake ? 32'h1 : 32'h0);
            fifo_b_hshake_count  <= fifo_b_hshake_count  + (fifo_b_hshake  ? 32'h1 : 32'h0);
        end
    end

    // AXI AR
    assign axi_fifo_if.arvalid       = m_axi_if.arvalid && m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH];
    assign axi_fifo_if.araddr        = m_axi_if.araddr[AXI_FIFO_ADDR_WIDTH-1:0];
    assign axi_fifo_if.arburst       = m_axi_if.arburst;
    assign axi_fifo_if.arsize        = m_axi_if.arsize ;
    assign axi_fifo_if.arlen         = m_axi_if.arlen  ;
    assign axi_fifo_if.aruser        = m_axi_if.aruser ;
    assign axi_fifo_if.arid          = m_axi_if.arid   ;
    assign axi_fifo_if.arlock        = m_axi_if.arlock ;

    // AXI R                                    
    assign axi_fifo_if.rready        = fifo_r_active ? m_axi_if.rready : '0;

    // AXI AW                                   
    assign axi_fifo_if.awvalid       = m_axi_if.awvalid && m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH];
    assign axi_fifo_if.awaddr        = m_axi_if.awaddr[AXI_FIFO_ADDR_WIDTH-1:0];
    assign axi_fifo_if.awburst       = m_axi_if.awburst;
    assign axi_fifo_if.awsize        = m_axi_if.awsize ;
    assign axi_fifo_if.awlen         = m_axi_if.awlen  ;
    assign axi_fifo_if.awuser        = m_axi_if.awuser ;
    assign axi_fifo_if.awid          = m_axi_if.awid   ;
    assign axi_fifo_if.awlock        = m_axi_if.awlock ;

    // AXI W                                    
    assign axi_fifo_if.wvalid        = fifo_w_active ? m_axi_if.wvalid : '0;
    assign axi_fifo_if.wdata         = fifo_w_active ? m_axi_if.wdata  : '0;
    assign axi_fifo_if.wstrb         = fifo_w_active ? m_axi_if.wstrb  : '0;
    assign axi_fifo_if.wuser         = fifo_w_active ? m_axi_if.wuser  : '0;
    assign axi_fifo_if.wlast         = fifo_w_active ? m_axi_if.wlast  : '0;
                                                    
    // AXI B                                    
    assign axi_fifo_if.bready        = fifo_w_active ? m_axi_if.bready : '0;
    assign axi_fifo_if_bvalid_force  = axi_fifo_if.bvalid;

    `CALIPTRA_ASSERT_NEVER(FIFO_RD_NOT_FIXED, fifo_ar_hshake && (axi_fifo_if.arburst != AXI_BURST_FIXED), core_clk, !cptra_rst_b)
    `CALIPTRA_ASSERT_NEVER(FIFO_WR_NOT_FIXED, fifo_aw_hshake && (axi_fifo_if.awburst != AXI_BURST_FIXED), core_clk, !cptra_rst_b)
    `CALIPTRA_ASSERT_NEVER(FIFO_1RD_FOR_RCVY_EMU, (fifo_r_active > 1) && ctrl.en_recovery_emulation, core_clk, !cptra_rst_b)

    caliptra_top_tb_axi_fifo #(
        .AW(AXI_FIFO_ADDR_WIDTH     ),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH),         // User Width
        .IW(CPTRA_AXI_DMA_ID_WIDTH  ),         // ID Width
        .DEPTH(AXI_FIFO_SIZE_BYTES  )
    ) i_axi_fifo (
        .clk  (core_clk   ),
        .rst_n(cptra_rst_b),

        // AXI INF
        .s_axi_w_if(axi_fifo_if.w_sub),
        .s_axi_r_if(axi_fifo_if.r_sub),

        // Control
        .auto_push            (ctrl.fifo_auto_push       ),
        .auto_pop             (ctrl.fifo_auto_pop        ),
        .fifo_clear           (ctrl.fifo_clear           ),
        .en_recovery_emulation(ctrl.en_recovery_emulation),
        .recovery_data_avail  (recovery_data_avail       ),
        .dma_gen_done         (ctrl.dma_gen_done         ),
        .dma_gen_block_size   (ctrl.dma_gen_block_size   )
    );

    // --------------------- REG Endpoint TODO ---------------------

    `CALIPTRA_ASSERT_MUTEX(DMA_NO_SIMULT_RD, {|sram_r_active,|fifo_r_active/*TODO*/}, core_clk, !cptra_rst_b)
    `CALIPTRA_ASSERT_MUTEX(DMA_NO_SIMULT_WR, {|sram_w_active,|fifo_w_active/*TODO*/}, core_clk, !cptra_rst_b)

    

endmodule
