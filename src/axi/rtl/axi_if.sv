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
//      Signals for a standard AXI4 compliant interface
//

interface axi_if #(parameter integer AW = 32, parameter integer DW = 32, parameter integer IW = 3, parameter integer UW = 32) (input logic clk, input logic rst_n);

    import axi_pkg::*;

    // AXI AR
    logic [AW-1:0]                 araddr;
    logic [$bits(axi_burst_e)-1:0] arburst;
    logic [2:0]                    arsize;
    logic [7:0]                    arlen;
    logic [UW-1:0]                 aruser;
    logic [IW-1:0]                 arid;
    logic                          arlock;
    logic                          arvalid;
    logic                          arready;

    // AXI R
    logic [DW-1:0]                 rdata;
    logic [$bits(axi_resp_e)-1:0]  rresp;
    logic [IW-1:0]                 rid;
    logic                          rlast;
    logic                          rvalid;
    logic                          rready;

    // AXI AW
    logic [AW-1:0]                 awaddr;
    logic [$bits(axi_burst_e)-1:0] awburst;
    logic [2:0]                    awsize;
    logic [7:0]                    awlen;
    logic [UW-1:0]                 awuser;
    logic [IW-1:0]                 awid;
    logic                          awlock;
    logic                          awvalid;
    logic                          awready;

    // AXI W
    logic [DW-1:0]                 wdata;
    logic [DW/8-1:0]               wstrb;
    logic                          wvalid;
    logic                          wready;
    logic                          wlast;

    // AXI B
    logic [$bits(axi_resp_e)-1:0]  bresp;
    logic [IW-1:0]                 bid;
    logic                          bvalid;
    logic                          bready;

    // Modport for read manager
    modport r_mgr (
        // AR
        output araddr,
        output arburst,
        output arsize,
        output arlen,
        output aruser,
        output arid,
        output arlock,
        output arvalid,
        input  arready,
        // R
        input  rdata,
        input  rresp,
        input  rid,
        input  rlast,
        input  rvalid,
        output rready
    );

    // Modport for write manager
    modport w_mgr (
        // AW
        output awaddr,
        output awburst,
        output awsize,
        output awlen,
        output awuser,
        output awid,
        output awlock,
        output awvalid,
        input  awready,
        // W
        output wdata,
        output wstrb,
        output wvalid,
        input  wready,
        output wlast,
        // B
        input  bresp,
        input  bid,
        input  bvalid,
        output bready
    );

    // Modport for read subordinate
    modport r_sub (
        // AR
        input  araddr,
        input  arburst,
        input  arsize,
        input  arlen,
        input  aruser,
        input  arid,
        input  arlock,
        input  arvalid,
        output arready,
        // R
        output rdata,
        output rresp,
        output rid,
        output rlast,
        output rvalid,
        input  rready
    );

    // Modport for write subordinate
    modport w_sub (
        // AW
        input  awaddr,
        input  awburst,
        input  awsize,
        input  awlen,
        input  awuser,
        input  awid,
        input  awlock,
        input  awvalid,
        output awready,
        // W
        input  wdata,
        input  wstrb,
        input  wvalid,
        output wready,
        input  wlast,
        // B
        output bresp,
        output bid,
        output bvalid,
        input  bready
    );

    // Tasks
    `ifdef VERILATOR
        `define EQ__ =
        `define TIME_ALGN #100ps
    `else
        `define EQ__ <=
        `define TIME_ALGN
    `endif
    task rst_mgr();
        araddr  `EQ__ '0;
        arburst `EQ__ AXI_BURST_FIXED;
        arsize  `EQ__ '0;
        arlen   `EQ__ '0;
        aruser  `EQ__ '0;
        arid    `EQ__ '0;
        arlock  `EQ__ '0;
        arvalid `EQ__ '0;

        rready  `EQ__ '0;

        awaddr  `EQ__ '0;
        awburst `EQ__ AXI_BURST_FIXED;
        awsize  `EQ__ '0;
        awlen   `EQ__ '0;
        awuser  `EQ__ '0;
        awid    `EQ__ '0;
        awlock  `EQ__ '0;
        awvalid `EQ__ '0;

        wdata   `EQ__ '0;
        wstrb   `EQ__ '0;
        wvalid  `EQ__ '0;
        wlast   `EQ__ '0;

        bready  `EQ__ '0;
    endtask

    // TODO: handle IDs?
    task get_read_beat(output logic [DW-1:0] data,
                       output axi_resp_e     resp);
        `TIME_ALGN
        rready `EQ__ 1;
        do
            @(posedge clk);
        while (!rvalid);
        data   `EQ__ rdata;
        resp   `EQ__ axi_resp_e'(rresp);
        `TIME_ALGN
        rready `EQ__ 0;
        wait(!rready);
    endtask

    // Read: default to single beat of native data width
    task axi_read(input  logic [AW-1:0] addr,
                  input  axi_burst_e    burst = AXI_BURST_INCR,
                  input  logic [2:0]    size  = $clog2(DW/8),
                  input  logic [7:0]    len   = 0,
                  input  logic [UW-1:0] user  = UW'(0),
                  input  logic [IW-1:0] id    = IW'(0),
                  input  logic          lock  = 1'b0,
                  output logic [DW-1:0] data [],
                  output axi_resp_e     resp []);
        axi_resp_e     beat_resp;
        logic [DW-1:0] beat_data;
        while(!rst_n) @(posedge clk);
        do begin
            `TIME_ALGN
            araddr  `EQ__ addr;
            arburst `EQ__ burst;
            arsize  `EQ__ size;
            arlen   `EQ__ len;
            aruser  `EQ__ user;
            arid    `EQ__ id;
            arlock  `EQ__ lock;
            arvalid `EQ__ 1;
            @(posedge clk);
        end while(!arready);
        `TIME_ALGN
        araddr  `EQ__ '0;
        arburst `EQ__ AXI_BURST_FIXED;
        arsize  `EQ__ '0;
        arlen   `EQ__ '0;
        aruser  `EQ__ '0;
        arid    `EQ__ '0;
        arlock  `EQ__ '0;
        arvalid `EQ__ '0;
        data = new[len+1];
        resp = new[len+1];
        for (int beat=0; beat <= len; beat++) begin
            get_read_beat(beat_data, beat_resp);
            data[beat] = beat_data;
            resp[beat] = beat_resp;
        end
    endtask

    task axi_read_single(input  logic [AW-1:0] addr,
                         input  logic [UW-1:0] user  = UW'(0),
                         input  logic [IW-1:0] id    = IW'(0),
                         input  logic          lock  = 1'b0,
                         output logic [DW-1:0] data,
                         output axi_resp_e     resp);
        automatic axi_resp_e     burst_resp[];
        automatic logic [DW-1:0] burst_data[];
        axi_read(.addr(addr),
                 .user(user),
                 .id  (id  ),
                 .lock(lock),
                 .data(burst_data),
                 .resp(burst_resp));
        data = burst_data[0];
        resp = burst_resp[0];
    endtask

    task send_write_beat(input logic last,
                         input logic [DW-1:0] data,
                         input logic [DW/8-1:0] strb);
        `TIME_ALGN
        wvalid `EQ__ 1;
        wlast  `EQ__ last;
        wdata  `EQ__ data;
        wstrb  `EQ__ strb;
        do
            @(posedge clk);
        while (!wready);
        `TIME_ALGN
        wvalid `EQ__ '0;
        wlast  `EQ__ '0;
        wdata  `EQ__ '0;
        wstrb  `EQ__ '0;
        wait(!wvalid);
    endtask

    // TODO handle ID
    task get_write_resp(output axi_resp_e resp);
        `TIME_ALGN
        bready `EQ__ 1;
        do
            @(posedge clk);
        while(!bvalid);
        resp `EQ__ axi_resp_e'(bresp);
        `TIME_ALGN
        bready `EQ__ 0;
        wait(!bready);
    endtask

    task axi_write(input  logic [AW-1:0]   addr,
                   input  axi_burst_e      burst = AXI_BURST_INCR,
                   input  logic [2:0]      size  = $clog2(DW/8),
                   input  logic [7:0]      len   = 0,
                   input  logic [UW-1:0]   user  = UW'(0),
                   input  logic [IW-1:0]   id    = IW'(0),
                   input  logic            lock  = 1'b0,
                   input  logic [DW-1:0]   data [],
                   input  logic            use_strb = 0,
                   input  logic [DW/8-1:0] strb [],
                   output axi_resp_e       resp);
        while(!rst_n) @(posedge clk);
        do begin
            `TIME_ALGN
            awaddr  `EQ__ addr;
            awburst `EQ__ burst;
            awsize  `EQ__ size;
            awlen   `EQ__ len;
            awuser  `EQ__ user;
            awid    `EQ__ id;
            awlock  `EQ__ lock;
            awvalid `EQ__ 1;
            @(posedge clk);
        end while(!awready);
        `TIME_ALGN
        awaddr  `EQ__ '0;
        awburst `EQ__ AXI_BURST_FIXED;
        awsize  `EQ__ '0;
        awlen   `EQ__ '0;
        awuser  `EQ__ '0;
        awid    `EQ__ '0;
        awlock  `EQ__ '0;
        awvalid `EQ__ '0;
        fork
            for (int beat=0; beat <= len; beat++)
                send_write_beat(beat == len, data[beat], use_strb ? strb[beat] : {DW/8{1'b1}});
            get_write_resp(resp);
        join
    endtask

    task axi_write_single(input  logic [AW-1:0] addr,
                          input  logic [UW-1:0] user  = UW'(0),
                          input  logic [IW-1:0] id    = IW'(0),
                          input  logic          lock  = 1'b0,
                          input  logic [DW-1:0] data,
                          output axi_resp_e     resp);
        automatic logic [DW/8-1:0] burst_strb[] = new[1]('{{DW/8{1'b1}}});
        automatic logic [DW  -1:0] burst_data[] = new[1]('{data});
        axi_write(.addr(addr),
                  .user(user),
                  .id  (id  ),
                  .lock(lock),
                  .data(burst_data),
                  .use_strb(0),
                  .strb(burst_strb),
                  .resp(resp));
    endtask

    `undef EQ__
    `undef TIME_ALGN

endinterface
