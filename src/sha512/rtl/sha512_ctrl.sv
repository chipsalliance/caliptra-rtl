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
// sha512_ctrl.sv
// --------
// SHA512 controller for the AHb_lite interface.
//
//
//======================================================================

`include "kv_macros.svh"

module sha512_ctrl 
    import kv_defines_pkg::*;
    import pv_defines_pkg::*;
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

    // pcr vault interface
    output pv_read_t pv_read,
    output pv_write_t pv_write,
    input pv_rd_resp_t pv_rd_resp,
    input pv_wr_resp_t pv_wr_resp,
    output logic [PCR_HASH_NUM_DWORDS-1:0][31:0] pcr_signing_hash,

    // Interrupt
    output logic error_intr,
    output logic notif_intr,
    input  logic debugUnlock_or_scan_mode_switch
);

    //----------------------------------------------------------------
    // sha512
    //----------------------------------------------------------------
    logic           sha512_cs;
    logic           sha512_we;
    logic  [AHB_ADDR_WIDTH - 1 : 0] sha512_address;
    logic  [31 : 0] sha512_write_data;
    logic  [31 : 0] sha512_read_data;
    logic           sha512_err;

    sha512 #(
        .ADDR_WIDTH(AHB_ADDR_WIDTH),
        .DATA_WIDTH(32)
        )
        sha512_inst(
        .clk(clk),
        .reset_n(reset_n),
        .cptra_pwrgood(cptra_pwrgood),
        .cs(sha512_cs),
        .we(sha512_we),
        .address(sha512_address),
        .write_data(sha512_write_data),
        .read_data(sha512_read_data),
        .err(sha512_err),
        .pv_read(pv_read),
        .pv_write(pv_write),
        .pv_rd_resp(pv_rd_resp),
        .pv_wr_resp(pv_wr_resp),
        .pcr_signing_hash(pcr_signing_hash),
        .error_intr(error_intr),
        .notif_intr(notif_intr),
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
        .dv(sha512_cs),
        .hld(1'b0), //no holds from sha512
        .err(1'b0),
        .write(sha512_we),
        .wdata(sha512_write_data),
        .addr(sha512_address),

        .rdata(sha512_read_data)
    );


endmodule  // sha512_ctrl

//======================================================================
// EOF sha512_ctrl.sv
//======================================================================
