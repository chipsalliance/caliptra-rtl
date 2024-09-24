// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS;
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND; either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

// -------------------------------------------------------------
// AXI TLUL Gasket
// -------------------------------------------------------------
// Description:
//   Shim to convert AXI protocol writes into TLUL
//
// Limitations:
//   - When multiple ID tracking is enabled; write responses are returned in the
//     same order they are received; regardless of ID.
//
// -------------------------------------------------------------

module axi2tlul
    import axi_pkg::*;
    #(
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
                            // For registers; typically 0
                            // For SRAM; 1 or more
    ) (
        input clk,
        input rst_n,

        // AXI INF
        axi_if.w_sub s_axi_w_if,
        axi_if.r_sub s_axi_r_if,

        // TLUL INF
        output  tlul_pkg::tl_h2d_t tl_o,
        input   tlul_pkg::tl_d2h_t tl_i
    );

    // Subordinate INF
    logic          dv;
    logic [AW-1:0] addr;
    logic          write;
    logic [UW-1:0] user;
    logic [IW-1:0] id;
    logic [DW-1:0] wdata; // Requires: Component dwidth == AXI dwidth
    logic [BC-1:0] wstrb; // Requires: Component dwidth == AXI dwidth
    logic [2:0]    size;
    logic [DW-1:0] rdata; // Requires: Component dwidth == AXI dwidth
    logic          last; // Asserted with final 'dv' of a burst
    logic          hld;
    logic          rd_err;
    logic          wr_err;

    axi_sub #(
        .AW     (AW),
        .DW     (DW),
        .UW     (UW),
        .IW     (IW),
        .EX_EN  (EX_EN)

    ) i_axi_sub (
        .clk    (clk    ),
        .rst_n  (rst_n  ),

        // AXI INF
        .s_axi_w_if     (s_axi_w_if ),
        .s_axi_r_if     (s_axi_r_if ), 

        // Subordinate INF
        .dv     (dv     ),
        .addr   (addr   ),
        .write  (write  ),
        .user   (user   ),
        .id     (id     ),
        .wdata  (wdata  ),
        .wstrb  (wstrb  ),
        .size   (size   ),
        .rdata  (rdata  ),
        .last   (last   ),
        .hld    (hld    ),
        .rd_err (rd_err ),
        .wr_err (wr_err )
    );

    sub2tlul #(
        .AW     (AW),
        .DW     (DW),
        .UW     (UW),
        .IW     (IW),
        .EX_EN  (EX_EN)
    ) i_sub2tlul (
        .clk    (clk    ),
        .rst_n  (rst_n  ),

        // Subordinate INF
        .dv     (dv     ),
        .addr   (addr   ),
        .write  (write  ),
        .user   (user   ),
        .id     (id     ),
        .wdata  (wdata  ),
        .wstrb  (wstrb  ),
        .size   (size   ),
        .rdata  (rdata  ),
        .last   (last   ),
        .hld    (hld    ),
        .rd_err (rd_err ),
        .wr_err (wr_err ),

        // TLUL INF
        .tl_o   (tl_o   ),
        .tl_i   (tl_i   )
    );

endmodule