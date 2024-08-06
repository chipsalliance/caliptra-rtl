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
// AXI Subordinate Arbiter
// -------------------------------------------------------------
// Description:
//   Arbitrate between Reads and Writes coming from AXI subordinate modules.
//   Always give precedence to Writes.
//
// -------------------------------------------------------------

module axi_sub_arb import axi_pkg::*; #(
    parameter AW = 32,         // Address Width
    parameter DW = 32,         // Data Width
              BC = DW/8,       // Byte Count
              BW = $clog2(BC), // Byte count Width
    parameter UW = 32,         // User Width
    parameter IW = 1,          // ID Width
              ID_NUM = 1 << IW, // Don't override

    parameter EX_EN = 0,   // Enable exclusive access tracking w/ AxLOCK
    parameter C_LAT = 0    // Component latency in clock cycles from (dv&&!hld) -> rdata
                           // Must be const per component
                           // For registers, typically 0
                           // For SRAM, 1 or more
) (
    input clk,
    input rst_n,

    //Read Subordinate INF
    input  logic          r_dv,
    input  logic [AW-1:0] r_addr,  // Byte address
    input  logic [UW-1:0] r_user,
    input  logic [IW-1:0] r_id,
    input  logic          r_last,  // Asserted with final 'dv' of a burst
    output logic          r_hld,
    output logic          r_err,

    output logic [DW-1:0] r_rdata, // Requires: Component dwidth == AXI dwidth

    //Write Subordinate INF
    input  logic          w_dv,
    input  logic [AW-1:0] w_addr,  // Byte address
    input  logic [UW-1:0] w_user,
    input  logic [IW-1:0] w_id,
    input  logic [DW-1:0] w_wdata, // Requires: Component dwidth == AXI dwidth
    input  logic [BC-1:0] w_wstrb, // Requires: Component dwidth == AXI dwidth
    input  logic          w_last,  // Asserted with final 'dv' of a burst
    output logic          w_hld,
    output logic          w_err,

    //COMPONENT INF
    output logic          dv,
    output logic [AW-1:0] addr, // Byte address
    output logic          write,
    output logic [UW-1:0] user,
    output logic [IW-1:0] id,
    output logic [DW-1:0] wdata, // Requires: Component dwidth == AXI dwidth
    output logic [BC-1:0] wstrb, // Requires: Component dwidth == AXI dwidth
    output logic          last, // Asserted with final 'dv' of a burst
    input  logic          hld,
    input  logic          rd_err, // Asserts with rdata for reads (when C_LAT > 0)
    input  logic          wr_err, // Asserts with dv for writes

    input  logic [DW-1:0] rdata // Requires: Component dwidth == AXI dwidth
);

    logic r_pri; // Priority to reads
    logic r_win;

    // Switch priority to current arb winner so that priority persists
    // in case
    //   a) it was granted during a hold
    //   b) it was granted at start of multi-beat burst
    // Otherwise, always give priority to other channel at end of a burst
    // to arbitrate fairly
    always_ff@(posedge clk or negedge rst_n) begin
        if (!rst_n)
            r_pri <= 1'b0;
        // Toggle priority at end of burst
        else if (w_dv && !w_hld &&  w_last)
            r_pri <= 1'b1;
        else if (r_dv && !r_hld &&  r_last)
            r_pri <= 1'b0;
        // Keep priority when burst starts
        else if (w_dv && !r_win && !w_last)
            r_pri <= 1'b0;
        else if (r_dv &&  r_win && !r_last)
            r_pri <= 1'b1;
    end

    always_comb begin
//        case ({r_pri,r_dv,w_dv}) inside
//            3'b000: r_win = 0;
//            3'b001: r_win = 0;
//            3'b010: r_win = 1;
//            3'b011: r_win = 0;
//            3'b100: r_win = 1;
//            3'b101: r_win = 0;
//            3'b110: r_win = 1;
//            3'b111: r_win = 1;
//        endcase
        if (r_pri) r_win = r_dv || !w_dv;
        else       r_win = r_dv && !w_dv;
    end

    always_comb begin
        dv      = r_dv || w_dv;
        addr    = r_win ? r_addr : w_addr;
        write   = r_win ?      0 :      1;
        user    = r_win ? r_user : w_user;
        id      = r_win ? r_id   : w_id  ;
        last    = r_win ? r_last : w_last;
        r_hld   = hld || !r_win;
        w_hld   = hld ||  r_win;
        r_err   = rd_err;
        w_err   = wr_err;
        wdata   = w_wdata;
        wstrb   = w_wstrb;
        r_rdata = rdata;
    end

    `CALIPTRA_ASSERT_NEVER(AXI_SUB_ARB_CONFLICT, r_dv && !r_hld && w_dv && !w_hld, clk, !rst_n)


endmodule
