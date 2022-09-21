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

module caliptra_ahb_srom #(
    parameter AHB_DATA_WIDTH    = 64 ,
    parameter AHB_ADDR_WIDTH    = 32

)(

    //AMBA AHB Lite INF
    input logic                       hclk,
    input logic                       hreset_n,
    input logic [AHB_ADDR_WIDTH-1:0]  haddr_i,
    input logic [AHB_DATA_WIDTH-1:0]  hwdata_i,
    input logic                       hsel_i,
    input logic                       hwrite_i,

    input logic                       hready_i,
    input logic [1:0]                 htrans_i,
    input logic [2:0]                 hsize_i,
    input logic [2:0]                 hburst_i,

    input logic                       hmastlock_i, // FIXME
    input logic [3:0]                 hprot_i, // FIXME

    output logic                      hresp_o,
    output logic                      hreadyout_o,
    output logic [AHB_DATA_WIDTH-1:0] hrdata_o

);


/////////////////////////////////
// Localparams
localparam SRAM_ADDR_WIDTH = AHB_ADDR_WIDTH-$clog2(AHB_DATA_WIDTH/8);
localparam SRAM_DEPTH      = 1 << SRAM_ADDR_WIDTH;


/////////////////////////////////
// Signals
wire                       sram_dv;
wire                       sram_hold;
wire                       sram_error;
wire                       sram_write;
wire [AHB_DATA_WIDTH-1:0]  sram_wdata;
wire [SRAM_ADDR_WIDTH-1:0] sram_addr;
wire [AHB_DATA_WIDTH-1:0]  sram_rdata;

wire [AHB_ADDR_WIDTH-1:0]  byte_addr;


/////////////////////////////////
// Assignments/Shim logic
assign sram_hold = 1'b0;  // TODO
assign sram_error = sram_dv && sram_write; // FIXME


/////////////////////////////////
// Module Instances
ahb_slv_sif #(
    .AHB_DATA_WIDTH   (AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(AHB_DATA_WIDTH),
    .ADDR_WIDTH       (AHB_ADDR_WIDTH)

) ahb_slv_inst (
    //AMBA AHB Lite INF
    .hclk       (hclk       ),
    .hreset_n   (hreset_n   ),
    .haddr_i    (haddr_i    ),
    .hwdata_i   (hwdata_i   ),
    .hsel_i     (hsel_i     ),
    .hwrite_i   (hwrite_i   ),

    .hready_i   (hready_i   ),
    .htrans_i   (htrans_i   ),
    .hsize_i    (hsize_i    ),
    .hburst_i   (hburst_i   ),

    .hresp_o    (hresp_o    ),
    .hreadyout_o(hreadyout_o),
    .hrdata_o   (hrdata_o   ),

    .hmastlock_i(hmastlock_i),
    .hprot_i    (hprot_i    ),

    //COMPONENT INF
    .dv         (sram_dv         ),
    .hold       (sram_hold       ),
    .error      (sram_error      ),
    .write      (sram_write      ),
    .wdata      (sram_wdata      ),
    .addr       (byte_addr       ),

    .rdata      (sram_rdata      )
);

assign sram_addr = byte_addr >> $clog2(AHB_DATA_WIDTH/8);

caliptra_sram #(
    .DEPTH     (SRAM_DEPTH     ), // Depth in WORDS
    .DATA_WIDTH(AHB_DATA_WIDTH ),
    .ADDR_WIDTH(SRAM_ADDR_WIDTH)
) sram_inst (
    .clk_i   (hclk   ),

    .we_i    (1'b0/*sram_write && sram_dv*/      ),
    .waddr_i (sram_addr                          ),
    .wdata_i (AHB_DATA_WIDTH'(0)/*sram_wdata   */),
    .rdaddr_i(sram_addr                          ),
    .rdata_o (sram_rdata                         )
);

endmodule
