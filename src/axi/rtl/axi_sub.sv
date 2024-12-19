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
//
// -------------------------------------------------------------
// AXI Subordinate
// -------------------------------------------------------------
// Description:
//   Subordinate to convert AXI protocol transactions into internal component accesses
//   Includes an arbiter to squash duplex AXI transactions into simplex component operations
//   May optionally include an Exclusive Access monitor (AxLOCK signal)
//
// Limitations:
//   - When multiple ID tracking is enabled, write responses are returned in the
//     same order they are received, regardless of ID.
//
// -------------------------------------------------------------

module axi_sub import axi_pkg::*; #(
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

    // AXI INF
    axi_if.w_sub s_axi_w_if,
    axi_if.r_sub s_axi_r_if,

    //COMPONENT INF
    output logic          dv,
    output logic [AW-1:0] addr, // Byte address
    output logic          write,
    output logic [UW-1:0] user,
    output logic [IW-1:0] id,
    output logic [DW-1:0] wdata, // Requires: Component dwidth == AXI dwidth
    output logic [BC-1:0] wstrb, // Requires: Component dwidth == AXI dwidth
    output logic [2:0]    size,
    input  logic [DW-1:0] rdata, // Requires: Component dwidth == AXI dwidth
    output logic          last, // Asserted with final 'dv' of a burst
    input  logic          hld,
    input  logic          rd_err,
    input  logic          wr_err

);

    // Exclusive Access Signals
    `ifdef CALIPTRA_AXI_SUB_EX_EN
    logic        [ID_NUM-1:0] ex_clr;
    logic        [ID_NUM-1:0] ex_active;
    struct packed {
        logic [AW-1:0] addr;
        logic [AW-1:0] addr_mask;
    } [ID_NUM-1:0] ex_ctx;
    `endif

    //Read Subordinate INF
    logic          r_dv;
    logic [AW-1:0] r_addr;  // Byte address
    logic [UW-1:0] r_user;
    logic [IW-1:0] r_id;
    logic [2:0]    r_size;
    logic          r_last;  // Asserted with final 'dv' of a burst
    logic          r_hld;
    logic          r_err;

    logic [DW-1:0] r_rdata; // Requires: Component dwidth == AXI dwidth

    //Write Subordinate INF
    logic          w_dv;
    logic [AW-1:0] w_addr;  // Byte address
    logic [UW-1:0] w_user;
    logic [IW-1:0] w_id;
    logic [DW-1:0] w_wdata; // Requires: Component dwidth == AXI dwidth
    logic [BC-1:0] w_wstrb; // Requires: Component dwidth == AXI dwidth
    logic [2:0]    w_size; 
    logic          w_last;  // Asserted with final 'dv' of a burst
    logic          w_hld;
    logic          w_err;


    axi_sub_wr #(
        .AW   (AW   ),
        .DW   (DW   ),
        .UW   (UW   ),
        .IW   (IW   )

    ) i_axi_sub_wr (
        .clk  (clk  ),
        .rst_n(rst_n),

        // AXI INF
        .s_axi_if(s_axi_w_if),

        // Exclusive Access Signals
        `ifdef CALIPTRA_AXI_SUB_EX_EN
        .ex_clr   (ex_clr   ),
        .ex_active(ex_active),
        .ex_ctx   (ex_ctx   ),
        `endif

        //COMPONENT INF
        .dv   (w_dv   ),
        .addr (w_addr ),
        .user (w_user ),
        .id   (w_id   ),
        .wdata(w_wdata),
        .wstrb(w_wstrb),
        .wsize(w_size ),
        .last (w_last ),
        .hld  (w_hld  ),
        .err  (w_err  )

    );

    axi_sub_rd #(
        .AW(AW),
        .DW(DW),
        .UW(UW),
        .IW(IW),

        .C_LAT(C_LAT)
    ) i_axi_sub_rd (
        .clk  (clk  ),
        .rst_n(rst_n),

        // AXI INF
        .s_axi_if(s_axi_r_if),

        // Exclusive Access Signals
        `ifdef CALIPTRA_AXI_SUB_EX_EN
        .ex_clr   (ex_clr   ),
        .ex_active(ex_active),
        .ex_ctx   (ex_ctx   ),
        `endif

        //COMPONENT INF
        .dv   (r_dv   ),
        .addr (r_addr ),
        .user (r_user ),
        .id   (r_id   ),
        .size (r_size ),
        .last (r_last ),
        .hld  (r_hld  ),
        .err  (r_err  ),

        .rdata(r_rdata)
    );

    axi_sub_arb #(
        .AW(AW),
        .DW(DW),
        .UW(UW),
        .IW(IW),

        .C_LAT(C_LAT)
    ) i_axi_sub_arb (
        .clk    (clk    ),
        .rst_n  (rst_n  ),

        //Read Subordinate INF
        .r_dv   (r_dv   ),
        .r_addr (r_addr ),
        .r_user (r_user ),
        .r_id   (r_id   ),
        .r_last (r_last ),
        .r_size (r_size ),
        .r_hld  (r_hld  ),
        .r_err  (r_err  ),
        .r_rdata(r_rdata),

        //Write Subordinate INF
        .w_dv   (w_dv   ),
        .w_addr (w_addr ),
        .w_user (w_user ),
        .w_id   (w_id   ),
        .w_wdata(w_wdata),
        .w_wstrb(w_wstrb),
        .w_size (w_size ),
        .w_last (w_last ),
        .w_hld  (w_hld  ),
        .w_err  (w_err  ),

        //COMPONENT INF
        .dv     (dv     ),
        .addr   (addr   ),
        .write  (write  ),
        .user   (user   ),
        .id     (id     ),
        .wdata  (wdata  ),
        .wstrb  (wstrb  ),
        .size   (size   ),
        .last   (last   ),
        .hld    (hld    ),
        .rd_err (rd_err ),
        .wr_err (wr_err ),
        .rdata  (rdata  ) 
    );

endmodule
