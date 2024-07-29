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
// sha256_ctrl.sv
// --------
// SHA256 controller for the AHb_lite interface.
//
//
//======================================================================

module sha256_ctrl #(
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

    // Interrupt
    output logic error_intr,
    output logic notif_intr,
    input  logic debugUnlock_or_scan_mode_switch
);

    //----------------------------------------------------------------
    // sha256
    //----------------------------------------------------------------
    logic           sha256_cs;
    logic           sha256_we;
    logic  [AHB_ADDR_WIDTH-1 : 0] sha256_address;
    logic  [31 : 0] sha256_write_data;
    logic  [31 : 0] sha256_read_data;
    logic           sha256_err;

    sha256 #(
        .ADDR_WIDTH(AHB_ADDR_WIDTH),
        .DATA_WIDTH(32)
        ) sha256_inst(
        .clk(clk),
        .reset_n(reset_n),
        .cptra_pwrgood(cptra_pwrgood),
        .cs(sha256_cs),
        .we(sha256_we),
        .address(sha256_address),
        .write_data(sha256_write_data),
        .read_data(sha256_read_data),
        .err(sha256_err),
        .error_intr(error_intr),
        .notif_intr(notif_intr),
        .debugUnlock_or_scan_mode_switch(debugUnlock_or_scan_mode_switch)
    );


    //----------------------------------------------------------------
    // AHB Slave node
    //----------------------------------------------------------------
        
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
        .dv(sha256_cs),
        .hld(1'b0), //no holds from sha256
        .err(1'b0),
        .write(sha256_we),
        .wdata(sha256_write_data),
        .addr(sha256_address),

        .rdata(sha256_read_data)
    );

endmodule //sha256_ctrl

//======================================================================
// EOF sha256_ctrl.sv
//======================================================================
