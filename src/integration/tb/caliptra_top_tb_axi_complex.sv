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

module caliptra_top_tb_axi_complex (
    input logic core_clk,
    input logic cptra_rst_b,
    axi_if m_axi_if,
    output logic recovery_data_avail
);

    import axi_pkg::*;
    import soc_ifc_pkg::*;
    import caliptra_top_tb_pkg::*;

    //=========================================================================-
    // Local i/fs
    //=========================================================================-
    axi_if #(
        .AW(AXI_SRAM_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .IW(CPTRA_AXI_DMA_ID_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH)
    ) axi_sram_if (.clk(core_clk), .rst_n(cptra_rst_b));
    axi_if #(
        .AW(AXI_FIFO_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .IW(CPTRA_AXI_DMA_ID_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH)
    ) axi_fifo_if (.clk(core_clk), .rst_n(cptra_rst_b));


    //=========================================================================-
    // Dummy interconnect
    //=========================================================================-
    // --------------------- Endpoint mux ---------------------
    logic [1:0] sram_r_active;
    logic       sram_ar_hshake;
    logic       sram_rlast_hshake;

    logic [1:0] sram_w_active;
    logic       sram_aw_hshake;
    logic       sram_b_hshake;

    logic [1:0] fifo_r_active;
    logic       fifo_ar_hshake;
    logic       fifo_rlast_hshake;

    logic [1:0] fifo_w_active;
    logic       fifo_aw_hshake;
    logic       fifo_b_hshake;

    always_comb begin
        // AXI AR
        m_axi_if.arready          = (m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH]) ? axi_sram_if.arready :
                                    (m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH]) ? axi_fifo_if.arready :
                                                                                                                                                                                      1'b0;
                                                    
        // AXI R                                    
        m_axi_if.rdata            = sram_r_active ? axi_sram_if.rdata :
                                    fifo_r_active ? axi_fifo_if.rdata :
                                                    '0;
        m_axi_if.rresp            = sram_r_active ? axi_sram_if.rresp :
                                    fifo_r_active ? axi_fifo_if.rresp :
                                                    '0;
        m_axi_if.rid              = sram_r_active ? axi_sram_if.rid   :
                                    fifo_r_active ? axi_fifo_if.rid   :
                                                    '0;
        m_axi_if.ruser            = sram_r_active ? axi_sram_if.ruser :
                                    fifo_r_active ? axi_fifo_if.ruser :
                                                    '0;
        m_axi_if.rlast            = sram_r_active ? axi_sram_if.rlast :
                                    fifo_r_active ? axi_fifo_if.rlast :
                                                    '0;
        m_axi_if.ruser            = sram_r_active ? axi_sram_if.ruser :
                                    fifo_r_active ? axi_fifo_if.ruser :
                                                    '0;
        m_axi_if.rvalid           = sram_r_active ? axi_sram_if.rvalid :
                                    fifo_r_active ? axi_fifo_if.rvalid :
                                                    '0;
                                                    
        // AXI AW                                   
        m_axi_if.awready          = (m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH]) ? axi_sram_if.awready :
                                    (m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH]) ? axi_fifo_if.awready :
                                                                                                                                                                                      1'b0;
                                                    
        // AXI W                                    
        m_axi_if.wready           = sram_w_active ? axi_sram_if.wready :
                                    fifo_w_active ? axi_fifo_if.wready :
                                                    1'b0;
                                                    
        // AXI B                                    
        m_axi_if.bresp            = sram_w_active ? axi_sram_if.bresp :
                                    fifo_w_active ? axi_fifo_if.bresp :
                                                    '0;
        m_axi_if.bid              = sram_w_active ? axi_sram_if.bid :
                                    fifo_w_active ? axi_fifo_if.bid :
                                                    '0;
        m_axi_if.buser            = sram_w_active ? axi_sram_if.buser :
                                    fifo_w_active ? axi_fifo_if.buser :
                                                    '0;
        m_axi_if.bvalid           = sram_w_active ? axi_sram_if.bvalid :
                                    fifo_w_active ? axi_fifo_if.bvalid :
                                                    '0;
    end

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
        sram_aw_hshake    = axi_sram_if.awvalid && axi_sram_if.awready;
        sram_b_hshake     = axi_sram_if.bvalid  && axi_sram_if.bready;
    end
    always_ff@(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            sram_w_active <= 2'b0;;
        end
        else begin
            case ({sram_aw_hshake,sram_b_hshake}) inside
                2'b00:
                    sram_w_active <= sram_w_active;
                2'b01:
                    if (sram_w_active)
                        sram_w_active <= sram_w_active - 2'b1;
                    else
                        $fatal("Write response, but no writes outstanding!");
                2'b10:
                    sram_w_active <= sram_w_active + 2'b1;
                2'b11:
                    sram_w_active <= sram_w_active;
            endcase
        end
    end
    `CALIPTRA_ASSERT_NEVER(SRAM_GT2_WR_PENDING, sram_w_active > 2, core_clk, !cptra_rst_b)
    always_comb begin
        // AXI AR
        axi_sram_if.arvalid       = m_axi_if.arvalid && m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH];
        axi_sram_if.araddr        = m_axi_if.araddr[AXI_SRAM_ADDR_WIDTH-1:0];
        axi_sram_if.arburst       = m_axi_if.arburst;
        axi_sram_if.arsize        = m_axi_if.arsize ;
        axi_sram_if.arlen         = m_axi_if.arlen  ;
        axi_sram_if.aruser        = m_axi_if.aruser ;
        axi_sram_if.arid          = m_axi_if.arid   ;
        axi_sram_if.arlock        = m_axi_if.arlock ;
                                                    
        // AXI R                                    
        axi_sram_if.rready        = sram_r_active ? m_axi_if.rready : '0;
                                                    
        // AXI AW                                   
        axi_sram_if.awvalid       = m_axi_if.awvalid && m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH];
        axi_sram_if.awaddr        = m_axi_if.awaddr[AXI_SRAM_ADDR_WIDTH-1:0];
        axi_sram_if.awburst       = m_axi_if.awburst;
        axi_sram_if.awsize        = m_axi_if.awsize ;
        axi_sram_if.awlen         = m_axi_if.awlen  ;
        axi_sram_if.awuser        = m_axi_if.awuser ;
        axi_sram_if.awid          = m_axi_if.awid   ;
        axi_sram_if.awlock        = m_axi_if.awlock ;
                                                    
        // AXI W                                    
        axi_sram_if.wvalid        = sram_w_active ? m_axi_if.wvalid : '0;
        axi_sram_if.wdata         = sram_w_active ? m_axi_if.wdata  : '0;
        axi_sram_if.wstrb         = sram_w_active ? m_axi_if.wstrb  : '0;
        axi_sram_if.wuser         = sram_w_active ? m_axi_if.wuser  : '0;
        axi_sram_if.wlast         = sram_w_active ? m_axi_if.wlast  : '0;
        axi_sram_if.wuser         = sram_w_active ? m_axi_if.wuser  : '0;

        // AXI B
        axi_sram_if.bready        = sram_w_active ? m_axi_if.bready : '0;
    end

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
        fifo_aw_hshake    = axi_fifo_if.awvalid && axi_fifo_if.awready;
        fifo_b_hshake     = axi_fifo_if.bvalid  && axi_fifo_if.bready;
    end
    always_ff@(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            fifo_w_active <= 2'b0;;
        end
        else begin
            case ({fifo_aw_hshake,fifo_b_hshake}) inside
                2'b00:
                    fifo_w_active <= fifo_w_active;
                2'b01:
                    if (fifo_w_active)
                        fifo_w_active <= fifo_w_active - 2'b1;
                    else
                        $fatal("Write response, but no writes outstanding!");
                2'b10:
                    fifo_w_active <= fifo_w_active + 2'b1;
                2'b11:
                    fifo_w_active <= fifo_w_active;
            endcase
        end
    end
    `CALIPTRA_ASSERT_NEVER(FIFO_GT2_WR_PENDING, fifo_w_active > 2, core_clk, !cptra_rst_b)
    always_comb begin
        // AXI AR
        axi_fifo_if.arvalid       = m_axi_if.arvalid && m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH];
        axi_fifo_if.araddr        = m_axi_if.araddr[AXI_FIFO_ADDR_WIDTH-1:0];
        axi_fifo_if.arburst       = m_axi_if.arburst;
        axi_fifo_if.arsize        = m_axi_if.arsize ;
        axi_fifo_if.arlen         = m_axi_if.arlen  ;
        axi_fifo_if.aruser        = m_axi_if.aruser ;
        axi_fifo_if.arid          = m_axi_if.arid   ;
        axi_fifo_if.arlock        = m_axi_if.arlock ;
                                                    
        // AXI R                                    
        axi_fifo_if.rready        = fifo_r_active ? m_axi_if.rready : '0;
                                                    
        // AXI AW                                   
        axi_fifo_if.awvalid       = m_axi_if.awvalid && m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH] == AXI_FIFO_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_FIFO_ADDR_WIDTH];
        axi_fifo_if.awaddr        = m_axi_if.awaddr[AXI_FIFO_ADDR_WIDTH-1:0];
        axi_fifo_if.awburst       = m_axi_if.awburst;
        axi_fifo_if.awsize        = m_axi_if.awsize ;
        axi_fifo_if.awlen         = m_axi_if.awlen  ;
        axi_fifo_if.awuser        = m_axi_if.awuser ;
        axi_fifo_if.awid          = m_axi_if.awid   ;
        axi_fifo_if.awlock        = m_axi_if.awlock ;
                                                    
        // AXI W                                    
        axi_fifo_if.wvalid        = fifo_w_active ? m_axi_if.wvalid : '0;
        axi_fifo_if.wdata         = fifo_w_active ? m_axi_if.wdata  : '0;
        axi_fifo_if.wstrb         = fifo_w_active ? m_axi_if.wstrb  : '0;
        axi_fifo_if.wuser         = fifo_w_active ? m_axi_if.wuser  : '0;
        axi_fifo_if.wlast         = fifo_w_active ? m_axi_if.wlast  : '0;
        axi_fifo_if.wuser         = fifo_w_active ? m_axi_if.wuser  : '0;
                                                    
        // AXI B                                    
        axi_fifo_if.bready        = fifo_w_active ? m_axi_if.bready : '0;
    end
    `CALIPTRA_ASSERT_NEVER(FIFO_RD_NOT_FIXED, fifo_ar_hshake && (axi_fifo_if.arburst != AXI_BURST_FIXED), core_clk, !cptra_rst_b)
    `CALIPTRA_ASSERT_NEVER(FIFO_WR_NOT_FIXED, fifo_aw_hshake && (axi_fifo_if.awburst != AXI_BURST_FIXED), core_clk, !cptra_rst_b)

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
        .s_axi_r_if(axi_fifo_if.r_sub)
    );

    // --------------------- REG Endpoint TODO ---------------------

    `CALIPTRA_ASSERT_MUTEX(DMA_NO_SIMULT_RD, {|sram_r_active,|fifo_r_active/*TODO*/}, core_clk, !cptra_rst_b)
    `CALIPTRA_ASSERT_MUTEX(DMA_NO_SIMULT_WR, {|sram_w_active,|fifo_w_active/*TODO*/}, core_clk, !cptra_rst_b)

    //=========================================================================-
    // Recovery Interface Model
    //=========================================================================-
    assign recovery_data_avail = 1'b1;

endmodule
