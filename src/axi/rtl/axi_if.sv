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
    task rst_mgr();
        araddr  = '0;
        arburst = AXI_BURST_FIXED;
        arsize  = '0;
        arlen   = '0;
        aruser  = '0;
        arid    = '0;
        arlock  = '0;
        arvalid = '0;

        rready  = '0;

        awaddr  = '0;
        awburst = AXI_BURST_FIXED;
        awsize  = '0;
        awlen   = '0;
        awuser  = '0;
        awid    = '0;
        awlock  = '0;
        awvalid = '0;

        wdata   = '0;
        wstrb   = '0;
        wvalid  = '0;
        wlast   = '0;

        bready  = '0;
    endtask

    // TODO: handle IDs?
    task get_read_beat(ref logic [DW-1:0] data,
                       ref axi_resp_e     resp);
        rready = 1;
        do
            @(posedge clk);
        while (!rvalid);
        data = rdata;
        resp = axi_resp_e'(rresp);
        rready = 0;
    endtask

    // Read: default to single beat of native data width
    task axi_read(input  logic [AW-1:0] addr,
                  input  axi_burst_e    burst = AXI_BURST_INCR,
                  input  logic [2:0]    size  = $clog2(DW/8),
                  input  logic [7:0]    len   = 0,
                  input  logic [UW-1:0] user  = UW'(0),
                  input  logic [IW-1:0] id    = IW'(0),
                  input  logic          lock  = 1'b0,
                  ref    logic [DW-1:0] data [],
                  ref    axi_resp_e     resp []);
        axi_resp_e     beat_resp;
        logic [DW-1:0] beat_data;
        while(!rst_n) @(posedge clk);
        do begin
            araddr  = addr;
            arburst = burst;
            arsize  = size;
            arlen   = len;
            aruser  = user;
            arid    = id;
            arlock  = lock;
            arvalid = 1;
            @(posedge clk);
        end while(!arready);
        for (int beat=0; beat <= len; beat++) begin
            get_read_beat(beat_data, beat_resp);
            data[beat] = beat_data;
            resp[beat] = beat_resp;
        end
    endtask

    task send_write_beat(input logic last,
                         input logic [DW-1:0] data,
                         input logic [DW/8-1:0] strb);
        wvalid = 1;
        wlast = last;
        wdata = data;
        wstrb = strb;
        do
            @(posedge clk);
        while (!wready);
    endtask

    // TODO handle ID
    task get_write_resp(output axi_resp_e resp);
        bready = 1;
        while(!bvalid) @(posedge clk);
        resp = axi_resp_e'(bresp);
    endtask

    task axi_write(      input  logic [AW-1:0]   addr,
                         input  axi_burst_e      burst = AXI_BURST_INCR,
                         input  logic [2:0]      size  = $clog2(DW/8),
                         input  logic [7:0]      len   = 0,
                         input  logic [UW-1:0]   user  = UW'(0),
                         input  logic [IW-1:0]   id    = IW'(0),
                         input  logic            lock  = 1'b0,
                   const ref    logic [DW-1:0]   data [],
                         input  logic            use_strb = 0,
                   const ref    logic [DW/8-1:0] strb [],
                         output axi_resp_e       resp);
        while(!rst_n) @(posedge clk);
        do begin
            awaddr  = addr;
            awburst = burst;
            awsize  = size;
            awlen   = len;
            awuser  = user;
            awid    = id;
            awlock  = lock;
            awvalid = 1;
            @(posedge clk);
        end while(!awready);
        fork
            for (int beat=0; beat <= len; beat++)
                send_write_beat(beat == len, data[beat], use_strb ? strb[beat] : {DW/8{1'b1}});
            get_write_resp(resp);
        join
    endtask

endinterface
