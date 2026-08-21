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
//======================================================================
//
// hmac256_ctrl.sv
// --------
// HMAC256 controller for the AHB-Lite interface.
//
//======================================================================


`include "caliptra_macros.svh"

module hmac256_ctrl
    #(
    parameter AHB_DATA_WIDTH = 32,
    parameter AHB_ADDR_WIDTH = 32
)
(
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,
    input wire           cptra_pwrgood,

    // from SLAVES PORT
    input logic [AHB_ADDR_WIDTH-1:0] haddr_i,
    input logic [AHB_DATA_WIDTH-1:0] hwdata_i,
    input logic hsel_i,
    input logic hwrite_i,
    input logic hready_i,
    input logic [1:0] htrans_i,
    input logic [2:0] hsize_i,

    output logic hresp_o,
    output logic hreadyout_o,
    output logic [AHB_DATA_WIDTH-1:0] hrdata_o,

    output logic busy_o,

    // Interrupt
    output logic error_intr,
    output logic notif_intr,
    input  logic debugUnlock_or_scan_mode_switch
);

    //----------------------------------------------------------------
    // hmac256
    //----------------------------------------------------------------
    logic           hmac256_cs;
    logic           hmac256_we;
    logic  [AHB_ADDR_WIDTH-1 : 0] hmac256_address;
    logic  [31 : 0] hmac256_write_data;
    logic  [31 : 0] hmac256_read_data;

    hmac256 #(
        .ADDR_WIDTH (AHB_ADDR_WIDTH),
        .DATA_WIDTH (32)
        ) hmac256_inst
        (
        .clk(clk),
        .reset_n(reset_n),
        .cptra_pwrgood(cptra_pwrgood),
        .cs(hmac256_cs),
        .we(hmac256_we),
        .address(hmac256_address),
        .write_data(hmac256_write_data),
        .read_data(hmac256_read_data),
        .error_intr(error_intr),
        .notif_intr(notif_intr),
        .busy_o(busy_o),
        .debugUnlock_or_scan_mode_switch(debugUnlock_or_scan_mode_switch)
    );

    //instantiate ahb lite module
ahb_slv_sif #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(32)
) ahb_slv_sif_uut
(
    //AMBA AHB Lite INF
    .hclk(clk),
    .hreset_n(reset_n),
    .haddr_i(haddr_i),
    .hwdata_i(hwdata_i),
    .hsel_i(hsel_i),
    .hwrite_i(hwrite_i),
    .hready_i(hready_i),
    .htrans_i(htrans_i),
    .hsize_i(hsize_i),

    .hresp_o(hresp_o),
    .hreadyout_o(hreadyout_o),
    .hrdata_o(hrdata_o),


    //COMPONENT INF
    .dv(hmac256_cs),
    .hld(1'b0), //no holes from hmac256
    .err(1'b0), //no errors from hmac256
    .write(hmac256_we),
    .wdata(hmac256_write_data),
    .addr(hmac256_address),

    .rdata(hmac256_read_data)
);


endmodule
