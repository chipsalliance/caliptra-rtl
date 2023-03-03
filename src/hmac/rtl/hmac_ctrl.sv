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
// hmac_ctrl.sv
// --------
// HMAC controller for the AHb_lite interface.
//
// 
// 
//======================================================================


`include "kv_macros.svh"

module hmac_ctrl 
    import kv_defines_pkg::*;
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

    // kv interface
    output kv_read_t [1:0] kv_read,
    output kv_write_t kv_write,
    input kv_rd_resp_t [1:0] kv_rd_resp,
    input kv_wr_resp_t kv_wr_resp,

    // Interrupt
    output logic error_intr,
    output logic notif_intr
);

    //----------------------------------------------------------------
    // hmac
    //----------------------------------------------------------------
    reg           hmac_cs;
    reg           hmac_we;
    reg  [AHB_ADDR_WIDTH-1 : 0] hmac_address;
    reg  [31 : 0] hmac_write_data;
    reg  [31 : 0] hmac_read_data;

    hmac #(
        .ADDR_WIDTH (AHB_ADDR_WIDTH),
        .DATA_WIDTH (32)
        ) hmac_inst
        (
        .clk(clk),
        .reset_n(reset_n),
        .cptra_pwrgood(cptra_pwrgood),
        .cs(hmac_cs),
        .we(hmac_we),
        .address(hmac_address),
        .write_data(hmac_write_data),
        .read_data(hmac_read_data),
        .kv_read(kv_read),
        .kv_write(kv_write),
        .kv_rd_resp(kv_rd_resp),
        .kv_wr_resp(kv_wr_resp),
        .error_intr(error_intr),
        .notif_intr(notif_intr)
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
    .dv(hmac_cs),
    .hld(1'b0), //no holes from hmac
    .err(1'b0), //no errors from hmac
    .write(hmac_we),
    .wdata(hmac_write_data),
    .addr(hmac_address),

    .rdata(hmac_read_data)
);

    


endmodule
