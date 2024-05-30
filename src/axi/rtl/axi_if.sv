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

interface axi_if #(parameter integer AW = 32, parameter integer DW = 32, parameter integer IW = 3, parameter integer UW = 32);

    import axi_pkg::*;

    // AXI AR
    logic [AW-1:0]         araddr;
    logic [1:0]            arburst;
    logic [2:0]            arsize;
    logic [7:0]            arlen;
    logic [UW-1:0]         aruser;
    logic [IW-1:0]         arid;
    logic                  arlock;
    logic                  arvalid;
    logic                  arready;

    // AXI R
    logic [DW-1:0]         rdata;
    logic [1:0]            rresp;
    logic [IW-1:0]         rid;
    logic                  rlast;
    logic                  rvalid;
    logic                  rready;

    // AXI AW
    logic [AW-1:0]         awaddr;
    logic [1:0]            awburst;
    logic [2:0]            awsize;
    logic [7:0]            awlen;
    logic [UW-1:0]         awuser;
    logic [IW-1:0]         awid;
    logic                  awlock;
    logic                  awvalid;
    logic                  awready;

    // AXI W
    logic [DW-1:0]         wdata;
    logic [DW/8-1:0]       wstrb;
    logic                  wvalid;
    logic                  wready;
    logic                  wlast;

    // AXI B
    logic [1:0]            bresp;
    logic [IW-1:0]         bid;
    logic                  bvalid;
    logic                  bready;

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

endinterface
