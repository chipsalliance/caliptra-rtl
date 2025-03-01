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


module caliptra_top_tb_axi_fifo #(
    parameter AW = 32,
    parameter DW = 64,
              BC = DW/8,       // Byte Count
              BW = $clog2(BC), // Byte count Width
    parameter UW = 32,         // User Width
    parameter IW = 1,          // ID Width
              ID_NUM = 1 << IW,// Don't override
    parameter DEPTH = 16
)
(
    input clk,
    input rst_n,

    // AXI INF
    axi_if.w_sub s_axi_w_if,
    axi_if.r_sub s_axi_r_if
);

    // --------------------------------------- //
    // Localparams/Typedefs                    //
    // --------------------------------------- //
    
    localparam FIFO_BC = DEPTH; // depth in bytes
    localparam FIFO_BW = caliptra_prim_util_pkg::vbits((FIFO_BC/BC)+1); // width of a signal that reports FIFO slot consumption

    //COMPONENT INF
    logic          dv;
    logic [AW-1:0] addr; // Byte address
    logic          write;
    logic [DW-1:0] wdata; // Requires: Component dwidth == AXI dwidth
    logic [DW-1:0] rdata; // Requires: Component dwidth == AXI dwidth
    logic          hold;
    logic          rd_error;
    logic          wr_error;

    // FIFO signals
    logic               fifo_w_ready;
    logic               fifo_w_valid;
    logic [DW-1:0]      fifo_w_data;
    logic               fifo_r_ready;
    logic               fifo_r_valid;
    logic [DW-1:0]      fifo_r_data;
    logic [FIFO_BW-1:0] fifo_depth;
    logic               fifo_full, fifo_full_r;
    logic               fifo_empty, fifo_empty_r;


    axi_sub #(
        .AW   (AW),
        .DW   (DW),
        .UW   (UW),
        .IW   (IW),
        .EX_EN(0 ),
        .C_LAT(0 )
    ) i_axi_sub (
        .clk  (clk     ),
        .rst_n(rst_n   ),

        // AXI INF
        .s_axi_w_if(s_axi_w_if),
        .s_axi_r_if(s_axi_r_if),

        //COMPONENT INF
        .dv      (dv      ),
        .addr    (addr    ), // Byte address
        .write   (write   ),
        .user    (        ),
        .id      (        ),
        .wdata   (wdata   ),
        .wstrb   (        ),
        .rdata   (rdata   ),
        .last    (        ),
        .size    (        ),
        .hld     (hold    ),
        .rd_err  (rd_error),
        .wr_err  (wr_error)
    );

    assign rd_error = 1'b0;
    assign wr_error = 1'b0;

    // --------------------------------------- //
    // Data FIFO                               //
    // --------------------------------------- //
    caliptra_prim_fifo_sync #(
      .Width            (DW  ),
      .Pass             (1'b0), // if == 1 allow requests to pass through empty FIFO
      .Depth            (FIFO_BC/BC),
      .OutputZeroIfEmpty(1'b1), // if == 1 always output 0 when FIFO is empty
      .Secure           (1'b0)  // use prim count for pointers TODO review if this is needed
    ) i_fifo (
      .clk_i   (clk     ),
      .rst_ni  (rst_n   ),
      // synchronous clear / flush port
      .clr_i   (),
      // write port
      .wvalid_i(fifo_w_valid  ),
      .wready_o(fifo_w_ready  ),
      .wdata_i (fifo_w_data   ),
      // read port
      .rvalid_o(fifo_r_valid),
      .rready_i(fifo_r_ready),
      .rdata_o (fifo_r_data ),
      // occupancy
      .full_o  (fifo_full ),
      .depth_o (fifo_depth),
      .err_o   (          )
    );

    always_comb fifo_empty = fifo_depth == 0;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            fifo_full_r  <= 1'b0;
            fifo_empty_r <= 1'b1;
        end
        else begin
            fifo_full_r  <= fifo_full;
            fifo_empty_r <= fifo_empty;
        end
    end

    always_comb begin
        fifo_w_valid = dv &&  write;
        fifo_r_ready = dv && !write;
        hold = write ? !fifo_w_ready : !fifo_r_valid;
        rdata = fifo_r_data;
        fifo_w_data = wdata;
    end

endmodule
