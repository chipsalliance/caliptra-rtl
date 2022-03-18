// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
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

//********************************************************************************
// $Id$
//
// Function: Top level SWERV core file
// Comments:
//
//********************************************************************************

module el2_dma_ctrl #(
`include "el2_param.vh"
 )(
   input logic         clk,
   input logic         free_clk,
   input logic         rst_l,
   input logic         dma_bus_clk_en, // slave bus clock enable
   input logic         clk_override,
   input logic         scan_mode,

   // Debug signals
   input logic [31:0]  dbg_cmd_addr,
   input logic [31:0]  dbg_cmd_wrdata,
   input logic         dbg_cmd_valid,
   input logic         dbg_cmd_write, // 1: write command, 0: read_command
   input logic [1:0]   dbg_cmd_type, // 0:gpr 1:csr 2: memory
   input logic [1:0]   dbg_cmd_size, // size of the abstract mem access debug command

   input  logic        dbg_dma_bubble,   // Debug needs a bubble to send a valid
   output logic        dma_dbg_ready,    // DMA is ready to accept debug request

   output logic        dma_dbg_cmd_done,
   output logic        dma_dbg_cmd_fail,
   output logic [31:0] dma_dbg_rddata,

   // Core side signals
   output logic        dma_dccm_req,  // DMA dccm request (only one of dccm/iccm will be set)
   output logic        dma_iccm_req,  // DMA iccm request
   output logic [2:0]  dma_mem_tag,   // DMA Buffer entry number
   output logic [31:0] dma_mem_addr,  // DMA request address
   output logic [2:0]  dma_mem_sz,    // DMA request size
   output logic        dma_mem_write, // DMA write to dccm/iccm
   output logic [63:0] dma_mem_wdata, // DMA write data

   input logic         dccm_dma_rvalid,    // dccm data valid for DMA read
   input logic         dccm_dma_ecc_error, // ECC error on DMA read
   input logic [2:0]   dccm_dma_rtag,      // Tag of the DMA req
   input logic [63:0]  dccm_dma_rdata,     // dccm data for DMA read
   input logic         iccm_dma_rvalid,    // iccm data valid for DMA read
   input logic         iccm_dma_ecc_error, // ECC error on DMA read
   input logic [2:0]   iccm_dma_rtag,      // Tag of the DMA req
   input logic [63:0]  iccm_dma_rdata,     // iccm data for DMA read

   output logic        dma_active,         // DMA is busy
   output logic        dma_dccm_stall_any, // stall dccm pipe (bubble) so that DMA can proceed
   output logic        dma_iccm_stall_any, // stall iccm pipe (bubble) so that DMA can proceed
   input logic         dccm_ready, // dccm ready to accept DMA request
   input logic         iccm_ready, // iccm ready to accept DMA request
   input logic [2:0]   dec_tlu_dma_qos_prty,    // DMA QoS priority coming from MFDC [18:15]

   // PMU signals
   output logic        dma_pmu_dccm_read,
   output logic        dma_pmu_dccm_write,
   output logic        dma_pmu_any_read,
   output logic        dma_pmu_any_write,

   // AXI Write Channels
   input  logic                        dma_axi_awvalid,
   output logic                        dma_axi_awready,
   input  logic [pt.DMA_BUS_TAG-1:0]   dma_axi_awid,
   input  logic [31:0]                 dma_axi_awaddr,
   input  logic [2:0]                  dma_axi_awsize,


   input  logic                        dma_axi_wvalid,
   output logic                        dma_axi_wready,
   input  logic [63:0]                 dma_axi_wdata,
   input  logic [7:0]                  dma_axi_wstrb,

   output logic                        dma_axi_bvalid,
   input  logic                        dma_axi_bready,
   output logic [1:0]                  dma_axi_bresp,
   output logic [pt.DMA_BUS_TAG-1:0]   dma_axi_bid,

   // AXI Read Channels
   input  logic                        dma_axi_arvalid,
   output logic                        dma_axi_arready,
   input  logic [pt.DMA_BUS_TAG-1:0]   dma_axi_arid,
   input  logic [31:0]                 dma_axi_araddr,
   input  logic [2:0]                  dma_axi_arsize,

   output logic                        dma_axi_rvalid,
   input  logic                        dma_axi_rready,
   output logic [pt.DMA_BUS_TAG-1:0]   dma_axi_rid,
   output logic [63:0]                 dma_axi_rdata,
   output logic [1:0]                  dma_axi_rresp,
   output logic                        dma_axi_rlast
);


   localparam DEPTH = pt.DMA_BUF_DEPTH;
   localparam DEPTH_PTR = $clog2(DEPTH);
   localparam NACK_COUNT = 7;

   logic [DEPTH-1:0]        fifo_valid;
   logic [DEPTH-1:0][1:0]   fifo_error;
   logic [DEPTH-1:0]        fifo_error_bus;
   logic [DEPTH-1:0]        fifo_rpend;
   logic [DEPTH-1:0]        fifo_done;      // DMA trxn is done in core
   logic [DEPTH-1:0]        fifo_done_bus;  // DMA trxn is done in core but synced to bus clock
   logic [DEPTH-1:0][31:0]  fifo_addr;
   logic [DEPTH-1:0][2:0]   fifo_sz;
   logic [DEPTH-1:0][7:0]   fifo_byteen;
   logic [DEPTH-1:0]        fifo_write;
   logic [DEPTH-1:0]        fifo_posted_write;
   logic [DEPTH-1:0]        fifo_dbg;
   logic [DEPTH-1:0][63:0]  fifo_data;
   logic [DEPTH-1:0][pt.DMA_BUS_TAG-1:0]  fifo_tag;
   logic [DEPTH-1:0][pt.DMA_BUS_ID-1:0]   fifo_mid;
   logic [DEPTH-1:0][pt.DMA_BUS_PRTY-1:0] fifo_prty;

   logic [DEPTH-1:0]        fifo_cmd_en;
   logic [DEPTH-1:0]        fifo_data_en;
   logic [DEPTH-1:0]        fifo_pend_en;
   logic [DEPTH-1:0]        fifo_done_en;
   logic [DEPTH-1:0]        fifo_done_bus_en;
   logic [DEPTH-1:0]        fifo_error_en;
   logic [DEPTH-1:0]        fifo_error_bus_en;
   logic [DEPTH-1:0]        fifo_reset;
   logic [DEPTH-1:0][1:0]   fifo_error_in;
   logic [DEPTH-1:0][63:0]  fifo_data_in;

   logic                    fifo_write_in;
   logic                    fifo_posted_write_in;
   logic                    fifo_dbg_in;
   logic [31:0]             fifo_addr_in;
   logic [2:0]              fifo_sz_in;
   logic [7:0]              fifo_byteen_in;

   logic [DEPTH_PTR-1:0]    RspPtr, NxtRspPtr;
   logic [DEPTH_PTR-1:0]    WrPtr, NxtWrPtr;
   logic [DEPTH_PTR-1:0]    RdPtr, NxtRdPtr;
   logic                    WrPtrEn, RdPtrEn, RspPtrEn;

   logic [1:0]              dma_dbg_sz;
   logic [1:0]              dma_dbg_addr;
   logic [31:0]             dma_dbg_mem_rddata;
   logic [31:0]             dma_dbg_mem_wrdata;
   logic                    dma_dbg_cmd_error;
   logic                    dma_dbg_cmd_done_q;

   logic                    fifo_full, fifo_full_spec, fifo_empty;
   logic                    dma_address_error, dma_alignment_error;
   logic [3:0]              num_fifo_vld;
   logic                    dma_mem_req;
   logic [31:0]             dma_mem_addr_int;
   logic [2:0]              dma_mem_sz_int;
   logic [7:0]              dma_mem_byteen;
   logic                    dma_mem_addr_in_dccm;
   logic                    dma_mem_addr_in_iccm;
   logic                    dma_mem_addr_in_pic;
   logic                    dma_mem_addr_in_pic_region_nc;
   logic                    dma_mem_addr_in_dccm_region_nc;
   logic                    dma_mem_addr_in_iccm_region_nc;

   logic [2:0]              dma_nack_count, dma_nack_count_d, dma_nack_count_csr;

   logic                    dma_buffer_c1_clken;
   logic                    dma_free_clken;
   logic                    dma_buffer_c1_clk;
   logic                    dma_free_clk;
   logic                    dma_bus_clk;

   logic                    bus_rsp_valid, bus_rsp_sent;
   logic                    bus_cmd_valid, bus_cmd_sent;
   logic                    bus_cmd_write, bus_cmd_posted_write;
   logic [7:0]              bus_cmd_byteen;
   logic [2:0]              bus_cmd_sz;
   logic [31:0]             bus_cmd_addr;
   logic [63:0]             bus_cmd_wdata;
   logic [pt.DMA_BUS_TAG-1:0]  bus_cmd_tag;
   logic [pt.DMA_BUS_ID-1:0]   bus_cmd_mid;
   logic [pt.DMA_BUS_PRTY-1:0] bus_cmd_prty;
   logic                    bus_posted_write_done;

   logic                    fifo_full_spec_bus;
   logic                    dbg_dma_bubble_bus;
   logic                    stall_dma_in;
   logic                    dma_fifo_ready;

   logic                       wrbuf_en, wrbuf_data_en;
   logic                       wrbuf_cmd_sent, wrbuf_rst, wrbuf_data_rst;
   logic                       wrbuf_vld, wrbuf_data_vld;
   logic [pt.DMA_BUS_TAG-1:0]  wrbuf_tag;
   logic [2:0]                 wrbuf_sz;
   logic [31:0]                wrbuf_addr;
   logic [63:0]                wrbuf_data;
   logic [7:0]                 wrbuf_byteen;

   logic                       rdbuf_en;
   logic                       rdbuf_cmd_sent, rdbuf_rst;
   logic                       rdbuf_vld;
   logic [pt.DMA_BUS_TAG-1:0]  rdbuf_tag;
   logic [2:0]                 rdbuf_sz;
   logic [31:0]                rdbuf_addr;

   logic                       axi_mstr_prty_in, axi_mstr_prty_en;
   logic                       axi_mstr_priority;
   logic                       axi_mstr_sel;

   logic                       axi_rsp_valid, axi_rsp_sent;
   logic                       axi_rsp_write;
   logic [pt.DMA_BUS_TAG-1:0]  axi_rsp_tag;
   logic [1:0]                 axi_rsp_error;
   logic [63:0]                axi_rsp_rdata;

   //------------------------LOGIC STARTS HERE---------------------------------

   // FIFO inputs
   assign fifo_addr_in[31:0]    = dbg_cmd_valid ? dbg_cmd_addr[31:0] : bus_cmd_addr[31:0];
   assign fifo_byteen_in[7:0]   = {8{~dbg_cmd_valid}} & bus_cmd_byteen[7:0];    // Byte enable is used only for bus requests
   assign fifo_sz_in[2:0]       = dbg_cmd_valid ? {1'b0,dbg_cmd_size[1:0]} : bus_cmd_sz[2:0];
   assign fifo_write_in         = dbg_cmd_valid ? dbg_cmd_write : bus_cmd_write;
   assign fifo_posted_write_in  = ~dbg_cmd_valid & bus_cmd_posted_write;
   assign fifo_dbg_in           = dbg_cmd_valid;

   for (genvar i=0 ;i<DEPTH; i++) begin: GenFifo
      assign fifo_cmd_en[i]   = ((bus_cmd_sent & dma_bus_clk_en) | (dbg_cmd_valid & dbg_cmd_type[1])) & (i == WrPtr[DEPTH_PTR-1:0]);
      assign fifo_data_en[i] = (((bus_cmd_sent & fifo_write_in & dma_bus_clk_en) | (dbg_cmd_valid & dbg_cmd_type[1] & dbg_cmd_write))  & (i == WrPtr[DEPTH_PTR-1:0])) |
                               ((dma_address_error | dma_alignment_error) & (i == RdPtr[DEPTH_PTR-1:0])) |
                               (dccm_dma_rvalid & (i == DEPTH_PTR'(dccm_dma_rtag[2:0]))) |
                               (iccm_dma_rvalid & (i == DEPTH_PTR'(iccm_dma_rtag[2:0])));
      assign fifo_pend_en[i] = (dma_dccm_req | dma_iccm_req) & ~dma_mem_write & (i == RdPtr[DEPTH_PTR-1:0]);
      assign fifo_error_en[i] = ((dma_address_error | dma_alignment_error | dma_dbg_cmd_error) & (i == RdPtr[DEPTH_PTR-1:0])) |
                                ((dccm_dma_rvalid & dccm_dma_ecc_error) & (i == DEPTH_PTR'(dccm_dma_rtag[2:0]))) |
                                ((iccm_dma_rvalid & iccm_dma_ecc_error) & (i == DEPTH_PTR'(iccm_dma_rtag[2:0])));
      assign fifo_error_bus_en[i] = (((|fifo_error_in[i][1:0]) & fifo_error_en[i]) | (|fifo_error[i])) & dma_bus_clk_en;
      assign fifo_done_en[i] = ((|fifo_error[i] | fifo_error_en[i] | ((dma_dccm_req | dma_iccm_req) & dma_mem_write)) & (i == RdPtr[DEPTH_PTR-1:0])) |
                               (dccm_dma_rvalid & (i == DEPTH_PTR'(dccm_dma_rtag[2:0]))) |
                               (iccm_dma_rvalid & (i == DEPTH_PTR'(iccm_dma_rtag[2:0])));
      assign fifo_done_bus_en[i] = (fifo_done_en[i] | fifo_done[i]) & dma_bus_clk_en;
      assign fifo_reset[i] = (((bus_rsp_sent | bus_posted_write_done) & dma_bus_clk_en) | dma_dbg_cmd_done) & (i == RspPtr[DEPTH_PTR-1:0]);
      assign fifo_error_in[i]   = (dccm_dma_rvalid & (i == DEPTH_PTR'(dccm_dma_rtag[2:0]))) ? {1'b0,dccm_dma_ecc_error} : (iccm_dma_rvalid & (i == DEPTH_PTR'(iccm_dma_rtag[2:0]))) ? {1'b0,iccm_dma_ecc_error}  :
                                                                                                                {(dma_address_error | dma_alignment_error | dma_dbg_cmd_error), dma_alignment_error};
      assign fifo_data_in[i]   = (fifo_error_en[i] & (|fifo_error_in[i])) ? {32'b0,fifo_addr[i]} :
                                                        ((dccm_dma_rvalid & (i == DEPTH_PTR'(dccm_dma_rtag[2:0])))  ? dccm_dma_rdata[63:0] : (iccm_dma_rvalid & (i == DEPTH_PTR'(iccm_dma_rtag[2:0]))) ? iccm_dma_rdata[63:0] :
                                                                                                                                                       (dbg_cmd_valid ? {2{dma_dbg_mem_wrdata[31:0]}} : bus_cmd_wdata[63:0]));

      rvdffsc #(1) fifo_valid_dff (.din(1'b1), .dout(fifo_valid[i]), .en(fifo_cmd_en[i]), .clear(fifo_reset[i]), .clk(dma_free_clk), .*);
      rvdffsc #(2) fifo_error_dff (.din(fifo_error_in[i]), .dout(fifo_error[i]), .en(fifo_error_en[i]), .clear(fifo_reset[i]), .clk(dma_free_clk), .*);
      rvdffsc #(1) fifo_error_bus_dff (.din(1'b1), .dout(fifo_error_bus[i]), .en(fifo_error_bus_en[i]), .clear(fifo_reset[i]), .clk(dma_free_clk), .*);
      rvdffsc #(1) fifo_rpend_dff (.din(1'b1), .dout(fifo_rpend[i]), .en(fifo_pend_en[i]), .clear(fifo_reset[i]), .clk(dma_free_clk), .*);
      rvdffsc #(1) fifo_done_dff (.din(1'b1), .dout(fifo_done[i]), .en(fifo_done_en[i]), .clear(fifo_reset[i]), .clk(dma_free_clk), .*);
      rvdffsc #(1) fifo_done_bus_dff (.din(1'b1), .dout(fifo_done_bus[i]), .en(fifo_done_bus_en[i]), .clear(fifo_reset[i]), .clk(dma_free_clk), .*);
      rvdffe  #(32) fifo_addr_dff (.din(fifo_addr_in[31:0]), .dout(fifo_addr[i]), .en(fifo_cmd_en[i]), .*);
      rvdffs  #(3) fifo_sz_dff (.din(fifo_sz_in[2:0]), .dout(fifo_sz[i]), .en(fifo_cmd_en[i]), .clk(dma_buffer_c1_clk), .*);
      rvdffs  #(8) fifo_byteen_dff (.din(fifo_byteen_in[7:0]), .dout(fifo_byteen[i]), .en(fifo_cmd_en[i]), .clk(dma_buffer_c1_clk), .*);
      rvdffs  #(1) fifo_write_dff (.din(fifo_write_in), .dout(fifo_write[i]), .en(fifo_cmd_en[i]), .clk(dma_buffer_c1_clk), .*);
      rvdffs  #(1) fifo_posted_write_dff (.din(fifo_posted_write_in), .dout(fifo_posted_write[i]), .en(fifo_cmd_en[i]), .clk(dma_buffer_c1_clk), .*);
      rvdffs  #(1) fifo_dbg_dff (.din(fifo_dbg_in), .dout(fifo_dbg[i]), .en(fifo_cmd_en[i]), .clk(dma_buffer_c1_clk), .*);
      rvdffe  #(64) fifo_data_dff (.din(fifo_data_in[i]), .dout(fifo_data[i]), .en(fifo_data_en[i]), .*);
      rvdffs  #(pt.DMA_BUS_TAG) fifo_tag_dff(.din(bus_cmd_tag[pt.DMA_BUS_TAG-1:0]), .dout(fifo_tag[i][pt.DMA_BUS_TAG-1:0]), .en(fifo_cmd_en[i]), .clk(dma_buffer_c1_clk), .*);
      rvdffs  #(pt.DMA_BUS_ID) fifo_mid_dff(.din(bus_cmd_mid[pt.DMA_BUS_ID-1:0]), .dout(fifo_mid[i][pt.DMA_BUS_ID-1:0]), .en(fifo_cmd_en[i]), .clk(dma_buffer_c1_clk), .*);
      rvdffs  #(pt.DMA_BUS_PRTY) fifo_prty_dff(.din(bus_cmd_prty[pt.DMA_BUS_PRTY-1:0]), .dout(fifo_prty[i][pt.DMA_BUS_PRTY-1:0]), .en(fifo_cmd_en[i]), .clk(dma_buffer_c1_clk), .*);
   end

   // Pointer logic
   assign NxtWrPtr[DEPTH_PTR-1:0] = (WrPtr[DEPTH_PTR-1:0] == (DEPTH-1)) ? '0 : WrPtr[DEPTH_PTR-1:0] + 1'b1;
   assign NxtRdPtr[DEPTH_PTR-1:0] = (RdPtr[DEPTH_PTR-1:0] == (DEPTH-1)) ? '0 : RdPtr[DEPTH_PTR-1:0] + 1'b1;
   assign NxtRspPtr[DEPTH_PTR-1:0] = (RspPtr[DEPTH_PTR-1:0] == (DEPTH-1)) ? '0 : RspPtr[DEPTH_PTR-1:0] + 1'b1;

   assign WrPtrEn = |fifo_cmd_en[DEPTH-1:0];
   assign RdPtrEn = dma_dccm_req | dma_iccm_req | (dma_address_error | dma_alignment_error | dma_dbg_cmd_error);
   assign RspPtrEn = (dma_dbg_cmd_done | (bus_rsp_sent | bus_posted_write_done) & dma_bus_clk_en);

   rvdffs #(DEPTH_PTR) WrPtr_dff(.din(NxtWrPtr[DEPTH_PTR-1:0]), .dout(WrPtr[DEPTH_PTR-1:0]), .en(WrPtrEn), .clk(dma_free_clk), .*);
   rvdffs #(DEPTH_PTR) RdPtr_dff(.din(NxtRdPtr[DEPTH_PTR-1:0]), .dout(RdPtr[DEPTH_PTR-1:0]), .en(RdPtrEn), .clk(dma_free_clk), .*);
   rvdffs #(DEPTH_PTR) RspPtr_dff(.din(NxtRspPtr[DEPTH_PTR-1:0]), .dout(RspPtr[DEPTH_PTR-1:0]), .en(RspPtrEn), .clk(dma_free_clk), .*);

   // Miscellaneous signals
   assign fifo_full = fifo_full_spec_bus;

   always_comb begin
      num_fifo_vld[3:0] = {3'b0,bus_cmd_sent} - {3'b0,bus_rsp_sent};
      for (int i=0; i<DEPTH; i++) begin
         num_fifo_vld[3:0] += {3'b0,fifo_valid[i]};
      end
   end
   assign fifo_full_spec          = (num_fifo_vld[3:0] >= DEPTH);

   assign dma_fifo_ready = ~(fifo_full | dbg_dma_bubble_bus);

   // Error logic
   assign dma_address_error = fifo_valid[RdPtr] & ~fifo_done[RdPtr] & ~fifo_dbg[RdPtr] & (~(dma_mem_addr_in_dccm | dma_mem_addr_in_iccm));    // request not for ICCM or DCCM
   assign dma_alignment_error = fifo_valid[RdPtr] & ~fifo_done[RdPtr] & ~fifo_dbg[RdPtr] & ~dma_address_error &
                                (((dma_mem_sz_int[2:0] == 3'h1) & dma_mem_addr_int[0])                                                       |    // HW size but unaligned
                                 ((dma_mem_sz_int[2:0] == 3'h2) & (|dma_mem_addr_int[1:0]))                                                  |    // W size but unaligned
                                 ((dma_mem_sz_int[2:0] == 3'h3) & (|dma_mem_addr_int[2:0]))                                                  |    // DW size but unaligned
                                 (dma_mem_addr_in_iccm & ~((dma_mem_sz_int[1:0] == 2'b10) | (dma_mem_sz_int[1:0] == 2'b11)))                 |    // ICCM access not word size
                                 (dma_mem_addr_in_dccm & dma_mem_write & ~((dma_mem_sz_int[1:0] == 2'b10) | (dma_mem_sz_int[1:0] == 2'b11))) |    // DCCM write not word size
                                 (dma_mem_write & (dma_mem_sz_int[2:0] == 3'h2) & (dma_mem_byteen[dma_mem_addr_int[2:0]+:4] != 4'hf))        |    // Write byte enables not aligned for word store
                                 (dma_mem_write & (dma_mem_sz_int[2:0] == 3'h3) & ~((dma_mem_byteen[7:0] == 8'h0f) | (dma_mem_byteen[7:0] == 8'hf0) | (dma_mem_byteen[7:0] == 8'hff)))); // Write byte enables not aligned for dword store


   //Dbg outputs
   assign dma_dbg_ready    = fifo_empty & dbg_dma_bubble;
   assign dma_dbg_cmd_done = (fifo_valid[RspPtr] & fifo_dbg[RspPtr] & fifo_done[RspPtr]);
   assign dma_dbg_cmd_fail     = (|fifo_error[RspPtr] & dma_dbg_cmd_done) ;

   assign dma_dbg_sz[1:0]          = fifo_sz[RspPtr][1:0];
   assign dma_dbg_addr[1:0]        = fifo_addr[RspPtr][1:0];
   assign dma_dbg_mem_rddata[31:0] = fifo_addr[RspPtr][2] ? fifo_data[RspPtr][63:32] : fifo_data[RspPtr][31:0];
   assign dma_dbg_rddata[31:0]     = ({32{(dma_dbg_sz[1:0] == 2'h0)}} & ((dma_dbg_mem_rddata[31:0] >> 8*dma_dbg_addr[1:0]) & 32'hff)) |
                                     ({32{(dma_dbg_sz[1:0] == 2'h1)}} & ((dma_dbg_mem_rddata[31:0] >> 16*dma_dbg_addr[1]) & 32'hffff)) |
                                     ({32{(dma_dbg_sz[1:0] == 2'h2)}} & dma_dbg_mem_rddata[31:0]);

   assign dma_dbg_cmd_error = fifo_valid[RdPtr] & ~fifo_done[RdPtr] & fifo_dbg[RdPtr] &
                                 ((~(dma_mem_addr_in_dccm | dma_mem_addr_in_iccm | dma_mem_addr_in_pic)) |             // Address outside of ICCM/DCCM/PIC
                                  ((dma_mem_addr_in_iccm | dma_mem_addr_in_pic) & (dma_mem_sz_int[1:0] != 2'b10)));    // Only word accesses allowed for ICCM/PIC

   assign dma_dbg_mem_wrdata[31:0] = ({32{dbg_cmd_size[1:0] == 2'h0}} & {4{dbg_cmd_wrdata[7:0]}}) |
                                     ({32{dbg_cmd_size[1:0] == 2'h1}} & {2{dbg_cmd_wrdata[15:0]}}) |
                                     ({32{dbg_cmd_size[1:0] == 2'h2}} & dbg_cmd_wrdata[31:0]);

   // Block the decode if fifo full
   assign dma_dccm_stall_any = dma_mem_req & (dma_mem_addr_in_dccm | dma_mem_addr_in_pic) & (dma_nack_count >= dma_nack_count_csr);
   assign dma_iccm_stall_any = dma_mem_req & dma_mem_addr_in_iccm & (dma_nack_count >= dma_nack_count_csr);

   // Used to indicate ready to debug
   assign fifo_empty     = ~((|(fifo_valid[DEPTH-1:0])) | bus_cmd_sent);

   // Nack counter, stall the lsu pipe if 7 nacks
   assign dma_nack_count_csr[2:0] = dec_tlu_dma_qos_prty[2:0];
   assign dma_nack_count_d[2:0] = (dma_nack_count[2:0] >= dma_nack_count_csr[2:0]) ? ({3{~(dma_dccm_req | dma_iccm_req)}} & dma_nack_count[2:0]) :
                                                                                    (dma_mem_req & ~(dma_dccm_req | dma_iccm_req)) ? (dma_nack_count[2:0] + 1'b1) : 3'b0;

   rvdffs #(3) nack_count_dff(.din(dma_nack_count_d[2:0]), .dout(dma_nack_count[2:0]), .en(dma_mem_req), .clk(dma_free_clk), .*);

   // Core outputs
   assign dma_mem_req         = fifo_valid[RdPtr] & ~fifo_rpend[RdPtr] & ~fifo_done[RdPtr] & ~(dma_address_error | dma_alignment_error | dma_dbg_cmd_error);
   assign dma_dccm_req        = dma_mem_req & (dma_mem_addr_in_dccm | dma_mem_addr_in_pic) & dccm_ready;
   assign dma_iccm_req        = dma_mem_req & dma_mem_addr_in_iccm & iccm_ready;
   assign dma_mem_tag[2:0]    = 3'(RdPtr);
   assign dma_mem_addr_int[31:0] = fifo_addr[RdPtr];
   assign dma_mem_sz_int[2:0] = fifo_sz[RdPtr];
   assign dma_mem_addr[31:0]  = (dma_mem_write & ~fifo_dbg[RdPtr] & (dma_mem_byteen[7:0] == 8'hf0)) ? {dma_mem_addr_int[31:3],1'b1,dma_mem_addr_int[1:0]} : dma_mem_addr_int[31:0];
   assign dma_mem_sz[2:0]     = (dma_mem_write & ~fifo_dbg[RdPtr] & ((dma_mem_byteen[7:0] == 8'h0f) | (dma_mem_byteen[7:0] == 8'hf0))) ? 3'h2 : dma_mem_sz_int[2:0];
   assign dma_mem_byteen[7:0] = fifo_byteen[RdPtr];
   assign dma_mem_write       = fifo_write[RdPtr];
   assign dma_mem_wdata[63:0] = fifo_data[RdPtr];

   // PMU outputs
   assign dma_pmu_dccm_read   = dma_dccm_req & ~dma_mem_write;
   assign dma_pmu_dccm_write  = dma_dccm_req & dma_mem_write;
   assign dma_pmu_any_read    = (dma_dccm_req | dma_iccm_req) & ~dma_mem_write;
   assign dma_pmu_any_write   = (dma_dccm_req | dma_iccm_req) & dma_mem_write;

   // Address check  dccm
   if (pt.DCCM_ENABLE) begin: Gen_dccm_enable
      rvrangecheck #(.CCM_SADR(pt.DCCM_SADR),
                     .CCM_SIZE(pt.DCCM_SIZE)) addr_dccm_rangecheck (
         .addr(dma_mem_addr_int[31:0]),
         .in_range(dma_mem_addr_in_dccm),
         .in_region(dma_mem_addr_in_dccm_region_nc)
      );
   end else begin: Gen_dccm_disable
      assign dma_mem_addr_in_dccm = '0;
      assign dma_mem_addr_in_dccm_region_nc = '0;
   end // else: !if(pt.ICCM_ENABLE)

   // Address check  iccm
   if (pt.ICCM_ENABLE) begin: Gen_iccm_enable
      rvrangecheck #(.CCM_SADR(pt.ICCM_SADR),
                     .CCM_SIZE(pt.ICCM_SIZE)) addr_iccm_rangecheck (
         .addr(dma_mem_addr_int[31:0]),
         .in_range(dma_mem_addr_in_iccm),
         .in_region(dma_mem_addr_in_iccm_region_nc)
      );
   end else begin: Gen_iccm_disable
      assign dma_mem_addr_in_iccm = '0;
      assign dma_mem_addr_in_iccm_region_nc = '0;
   end // else: !if(pt.ICCM_ENABLE)


   // PIC memory address check
   rvrangecheck #(.CCM_SADR(pt.PIC_BASE_ADDR),
                  .CCM_SIZE(pt.PIC_SIZE)) addr_pic_rangecheck (
      .addr(dma_mem_addr_int[31:0]),
      .in_range(dma_mem_addr_in_pic),
      .in_region(dma_mem_addr_in_pic_region_nc)
    );

   // Inputs
   rvdff_fpga #(1) fifo_full_bus_ff     (.din(fifo_full_spec),   .dout(fifo_full_spec_bus), .clk(dma_bus_clk), .clken(dma_bus_clk_en), .rawclk(clk), .*);
   rvdff_fpga #(1) dbg_dma_bubble_ff    (.din(dbg_dma_bubble),   .dout(dbg_dma_bubble_bus), .clk(dma_bus_clk), .clken(dma_bus_clk_en), .rawclk(clk), .*);
   rvdff      #(1) dma_dbg_cmd_doneff   (.din(dma_dbg_cmd_done), .dout(dma_dbg_cmd_done_q), .clk(free_clk), .*);

   // Clock Gating logic
   assign dma_buffer_c1_clken = (bus_cmd_valid & dma_bus_clk_en) | dbg_cmd_valid | clk_override;
   assign dma_free_clken = (bus_cmd_valid | bus_rsp_valid | dbg_cmd_valid | dma_dbg_cmd_done | dma_dbg_cmd_done_q | (|fifo_valid[DEPTH-1:0]) | clk_override);

   rvoclkhdr dma_buffer_c1cgc ( .en(dma_buffer_c1_clken), .l1clk(dma_buffer_c1_clk), .* );
   rvoclkhdr dma_free_cgc (.en(dma_free_clken), .l1clk(dma_free_clk), .*);

`ifdef RV_FPGA_OPTIMIZE
   assign dma_bus_clk = 1'b0;
`else
   rvclkhdr  dma_bus_cgc (.en(dma_bus_clk_en), .l1clk(dma_bus_clk), .*);
`endif

   // Write channel buffer
   assign wrbuf_en       = dma_axi_awvalid & dma_axi_awready;
   assign wrbuf_data_en  = dma_axi_wvalid & dma_axi_wready;
   assign wrbuf_cmd_sent = bus_cmd_sent & bus_cmd_write;
   assign wrbuf_rst      = wrbuf_cmd_sent & ~wrbuf_en;
   assign wrbuf_data_rst = wrbuf_cmd_sent & ~wrbuf_data_en;

   rvdffsc_fpga  #(.WIDTH(1))              wrbuf_vldff       (.din(1'b1), .dout(wrbuf_vld),      .en(wrbuf_en),      .clear(wrbuf_rst),      .clk(dma_bus_clk), .clken(dma_bus_clk_en), .rawclk(clk), .*);
   rvdffsc_fpga  #(.WIDTH(1))              wrbuf_data_vldff  (.din(1'b1), .dout(wrbuf_data_vld), .en(wrbuf_data_en), .clear(wrbuf_data_rst), .clk(dma_bus_clk), .clken(dma_bus_clk_en), .rawclk(clk), .*);
   rvdffs_fpga   #(.WIDTH(pt.DMA_BUS_TAG)) wrbuf_tagff       (.din(dma_axi_awid[pt.DMA_BUS_TAG-1:0]), .dout(wrbuf_tag[pt.DMA_BUS_TAG-1:0]), .en(wrbuf_en), .clk(dma_bus_clk), .clken(dma_bus_clk_en), .rawclk(clk), .*);
   rvdffs_fpga   #(.WIDTH(3))              wrbuf_szff        (.din(dma_axi_awsize[2:0]),  .dout(wrbuf_sz[2:0]),     .en(wrbuf_en),                  .clk(dma_bus_clk), .clken(dma_bus_clk_en), .rawclk(clk), .*);
   rvdffe        #(.WIDTH(32))             wrbuf_addrff      (.din(dma_axi_awaddr[31:0]), .dout(wrbuf_addr[31:0]),  .en(wrbuf_en & dma_bus_clk_en), .*);
   rvdffe        #(.WIDTH(64))             wrbuf_dataff      (.din(dma_axi_wdata[63:0]),  .dout(wrbuf_data[63:0]),  .en(wrbuf_data_en & dma_bus_clk_en), .*);
   rvdffs_fpga   #(.WIDTH(8))              wrbuf_byteenff    (.din(dma_axi_wstrb[7:0]),   .dout(wrbuf_byteen[7:0]), .en(wrbuf_data_en),             .clk(dma_bus_clk), .clken(dma_bus_clk_en), .rawclk(clk), .*);

   // Read channel buffer
   assign rdbuf_en    = dma_axi_arvalid & dma_axi_arready;
   assign rdbuf_cmd_sent = bus_cmd_sent & ~bus_cmd_write;
   assign rdbuf_rst   = rdbuf_cmd_sent & ~rdbuf_en;

   rvdffsc_fpga  #(.WIDTH(1))              rdbuf_vldff  (.din(1'b1), .dout(rdbuf_vld), .en(rdbuf_en), .clear(rdbuf_rst), .clk(dma_bus_clk), .clken(dma_bus_clk_en), .rawclk(clk), .*);
   rvdffs_fpga   #(.WIDTH(pt.DMA_BUS_TAG)) rdbuf_tagff  (.din(dma_axi_arid[pt.DMA_BUS_TAG-1:0]), .dout(rdbuf_tag[pt.DMA_BUS_TAG-1:0]), .en(rdbuf_en), .clk(dma_bus_clk), .clken(dma_bus_clk_en), .rawclk(clk), .*);
   rvdffs_fpga   #(.WIDTH(3))              rdbuf_szff   (.din(dma_axi_arsize[2:0]),  .dout(rdbuf_sz[2:0]),    .en(rdbuf_en), .clk(dma_bus_clk), .clken(dma_bus_clk_en), .rawclk(clk), .*);
   rvdffe       #(.WIDTH(32))              rdbuf_addrff (.din(dma_axi_araddr[31:0]), .dout(rdbuf_addr[31:0]), .en(rdbuf_en & dma_bus_clk_en), .*);

   assign dma_axi_awready = ~(wrbuf_vld & ~wrbuf_cmd_sent);
   assign dma_axi_wready  = ~(wrbuf_data_vld & ~wrbuf_cmd_sent);
   assign dma_axi_arready = ~(rdbuf_vld & ~rdbuf_cmd_sent);

   //Generate a single request from read/write channel
   assign bus_cmd_valid                     = (wrbuf_vld & wrbuf_data_vld) | rdbuf_vld;
   assign bus_cmd_sent                      = bus_cmd_valid & dma_fifo_ready;
   assign bus_cmd_write                     = axi_mstr_sel;
   assign bus_cmd_posted_write              = '0;
   assign bus_cmd_addr[31:0]                = axi_mstr_sel ? wrbuf_addr[31:0] : rdbuf_addr[31:0];
   assign bus_cmd_sz[2:0]                   = axi_mstr_sel ? wrbuf_sz[2:0] : rdbuf_sz[2:0];
   assign bus_cmd_wdata[63:0]               = wrbuf_data[63:0];
   assign bus_cmd_byteen[7:0]               = wrbuf_byteen[7:0];
   assign bus_cmd_tag[pt.DMA_BUS_TAG-1:0]   = axi_mstr_sel ? wrbuf_tag[pt.DMA_BUS_TAG-1:0] : rdbuf_tag[pt.DMA_BUS_TAG-1:0];
   assign bus_cmd_mid[pt.DMA_BUS_ID-1:0]    = '0;
   assign bus_cmd_prty[pt.DMA_BUS_PRTY-1:0] = '0;

   // Sel=1 -> write has higher priority
   assign axi_mstr_sel     = (wrbuf_vld & wrbuf_data_vld & rdbuf_vld) ? axi_mstr_priority : (wrbuf_vld & wrbuf_data_vld);
   assign axi_mstr_prty_in = ~axi_mstr_priority;
   assign axi_mstr_prty_en = bus_cmd_sent;
   rvdffs_fpga #(.WIDTH(1)) mstr_prtyff(.din(axi_mstr_prty_in), .dout(axi_mstr_priority), .en(axi_mstr_prty_en), .clk(dma_bus_clk), .clken(dma_bus_clk_en), .rawclk(clk), .*);

   assign axi_rsp_valid                   = fifo_valid[RspPtr] & ~fifo_dbg[RspPtr] & fifo_done_bus[RspPtr];
   assign axi_rsp_rdata[63:0]             = fifo_data[RspPtr];
   assign axi_rsp_write                   = fifo_write[RspPtr];
   assign axi_rsp_error[1:0]              = fifo_error[RspPtr][0] ? 2'b10 : (fifo_error[RspPtr][1] ? 2'b11 : 2'b0);
   assign axi_rsp_tag[pt.DMA_BUS_TAG-1:0] = fifo_tag[RspPtr];

   // AXI response channel signals
   assign dma_axi_bvalid                  = axi_rsp_valid & axi_rsp_write;
   assign dma_axi_bresp[1:0]              = axi_rsp_error[1:0];
   assign dma_axi_bid[pt.DMA_BUS_TAG-1:0] = axi_rsp_tag[pt.DMA_BUS_TAG-1:0];

   assign dma_axi_rvalid                  = axi_rsp_valid & ~axi_rsp_write;
   assign dma_axi_rresp[1:0]              = axi_rsp_error;
   assign dma_axi_rdata[63:0]             = axi_rsp_rdata[63:0];
   assign dma_axi_rlast                   = 1'b1;
   assign dma_axi_rid[pt.DMA_BUS_TAG-1:0] = axi_rsp_tag[pt.DMA_BUS_TAG-1:0];

   assign bus_posted_write_done = 1'b0;
   assign bus_rsp_valid      = (dma_axi_bvalid | dma_axi_rvalid);
   assign bus_rsp_sent       = (dma_axi_bvalid & dma_axi_bready) | (dma_axi_rvalid & dma_axi_rready);

   assign dma_active  = wrbuf_vld | rdbuf_vld | (|fifo_valid[DEPTH-1:0]);


`ifdef RV_ASSERT_ON

   for (genvar i=0; i<DEPTH; i++) begin
      assert_fifo_done_and_novalid: assert #0 (~fifo_done[i] | fifo_valid[i]);
   end

   // Assertion to check awvalid stays stable during entire bus clock
   property dma_axi_awvalid_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_awvalid != $past(dma_axi_awvalid)) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_awvalid_stable: assert property (dma_axi_awvalid_stable) else
      $display("DMA AXI awvalid changed in middle of bus clock");

   // Assertion to check awid stays stable during entire bus clock
   property dma_axi_awid_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_awvalid & (dma_axi_awid[pt.DMA_BUS_TAG-1:0] != $past(dma_axi_awid[pt.DMA_BUS_TAG-1:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_awid_stable: assert property (dma_axi_awid_stable) else
      $display("DMA AXI awid changed in middle of bus clock");

   // Assertion to check awaddr stays stable during entire bus clock
   property dma_axi_awaddr_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_awvalid & (dma_axi_awaddr[31:0] != $past(dma_axi_awaddr[31:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_awaddr_stable: assert property (dma_axi_awaddr_stable) else
      $display("DMA AXI awaddr changed in middle of bus clock");

   // Assertion to check awsize stays stable during entire bus clock
   property dma_axi_awsize_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_awvalid & (dma_axi_awsize[2:0] != $past(dma_axi_awsize[2:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_awsize_stable: assert property (dma_axi_awsize_stable) else
      $display("DMA AXI awsize changed in middle of bus clock");

   // Assertion to check wstrb stays stable during entire bus clock
   property dma_axi_wstrb_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_wvalid & (dma_axi_wstrb[7:0] != $past(dma_axi_wstrb[7:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_wstrb_stable: assert property (dma_axi_wstrb_stable) else
      $display("DMA AXI wstrb changed in middle of bus clock");

   // Assertion to check wdata stays stable during entire bus clock
   property dma_axi_wdata_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_wvalid & (dma_axi_wdata[63:0] != $past(dma_axi_wdata[63:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_wdata_stable: assert property (dma_axi_wdata_stable) else
      $display("DMA AXI wdata changed in middle of bus clock");

   // Assertion to check awvalid stays stable during entire bus clock
   property dma_axi_arvalid_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_arvalid != $past(dma_axi_arvalid)) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_arvalid_stable: assert property (dma_axi_arvalid_stable) else
      $display("DMA AXI awvalid changed in middle of bus clock");

   // Assertion to check awid stays stable during entire bus clock
   property dma_axi_arid_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_arvalid & (dma_axi_arid[pt.DMA_BUS_TAG-1:0] != $past(dma_axi_arid[pt.DMA_BUS_TAG-1:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_arid_stable: assert property (dma_axi_arid_stable) else
      $display("DMA AXI awid changed in middle of bus clock");

   // Assertion to check awaddr stays stable during entire bus clock
   property dma_axi_araddr_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_arvalid & (dma_axi_araddr[31:0] != $past(dma_axi_araddr[31:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_araddr_stable: assert property (dma_axi_araddr_stable) else
      $display("DMA AXI awaddr changed in middle of bus clock");

   // Assertion to check awsize stays stable during entire bus clock
   property dma_axi_arsize_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_awvalid & (dma_axi_arsize[2:0] != $past(dma_axi_arsize[2:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_arsize_stable: assert property (dma_axi_arsize_stable) else
      $display("DMA AXI awsize changed in middle of bus clock");

   // Assertion to check bvalid stays stable during entire bus clock
   property dma_axi_bvalid_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_bvalid != $past(dma_axi_bvalid)) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_bvalid_stable: assert property (dma_axi_bvalid_stable) else
      $display("DMA AXI bvalid changed in middle of bus clock");

   // Assertion to check bvalid stays stable if bready is low
   property dma_axi_bvalid_stable_till_bready;
      @(posedge clk) disable iff(~rst_l)  (~dma_axi_bvalid && $past(dma_axi_bvalid)) |-> $past(dma_axi_bready);
   endproperty
   assert_dma_axi_bvalid_stable_till_bready: assert property (dma_axi_bvalid_stable_till_bready) else
      $display("DMA AXI bvalid deasserted without bready");

   // Assertion to check bresp stays stable during entire bus clock
   property dma_axi_bresp_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_bvalid & (dma_axi_bresp[1:0] != $past(dma_axi_bresp[1:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_bresp_stable: assert property (dma_axi_bresp_stable) else
      $display("DMA AXI bresp changed in middle of bus clock");

   // Assertion to check bid stays stable during entire bus clock
   property dma_axi_bid_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_bvalid & (dma_axi_bid[pt.DMA_BUS_TAG-1:0] != $past(dma_axi_bid[pt.DMA_BUS_TAG-1:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_bid_stable: assert property (dma_axi_bid_stable) else
      $display("DMA AXI bid changed in middle of bus clock");

   // Assertion to check rvalid stays stable during entire bus clock
   property dma_axi_rvalid_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_rvalid != $past(dma_axi_rvalid)) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_rvalid_stable: assert property (dma_axi_rvalid_stable) else
      $display("DMA AXI bvalid changed in middle of bus clock");

   // Assertion to check rvalid stays stable if bready is low
   property dma_axi_rvalid_stable_till_ready;
      @(posedge clk) disable iff(~rst_l)  (~dma_axi_rvalid && $past(dma_axi_rvalid)) |-> $past(dma_axi_rready);
   endproperty
   assert_dma_axi_rvalid_stable_till_ready: assert property (dma_axi_rvalid_stable_till_ready) else
      $display("DMA AXI bvalid changed in middle of bus clock");

   // Assertion to check rresp stays stable during entire bus clock
   property dma_axi_rresp_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_rvalid & (dma_axi_rresp[1:0] != $past(dma_axi_rresp[1:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_rresp_stable: assert property (dma_axi_rresp_stable) else
      $display("DMA AXI bresp changed in middle of bus clock");

   // Assertion to check rid stays stable during entire bus clock
   property dma_axi_rid_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_rvalid & (dma_axi_rid[pt.DMA_BUS_TAG-1:0] != $past(dma_axi_rid[pt.DMA_BUS_TAG-1:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_rid_stable: assert property (dma_axi_rid_stable) else
      $display("DMA AXI bid changed in middle of bus clock");

   // Assertion to check rdata stays stable during entire bus clock
   property dma_axi_rdata_stable;
      @(posedge clk) disable iff(~rst_l)  (dma_axi_rvalid & (dma_axi_rdata[63:0] != $past(dma_axi_rdata[63:0]))) |-> $past(dma_bus_clk_en);
   endproperty
   assert_dma_axi_rdata_stable: assert property (dma_axi_rdata_stable) else
      $display("DMA AXI bid changed in middle of bus clock");

`endif

endmodule // el2_dma_ctrl
