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
// aes_ctrl.sv
// --------
// AES controller for the AHb_lite interface.
//
//
//======================================================================

module aes_ctrl 
    import aes_param_pkg::*;
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

    input logic [255:0] cptra_obf_key,

    //Obfuscated UDS and FE
    input logic [31:0][31:0] obf_field_entropy,
    input logic [11:0][31:0] obf_uds_seed,

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
    output kv_write_t kv_write,

    // Interrupt
    output error_intr,
    output notif_intr
);

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  //`include "aes_param.sv"

    //----------------------------------------------------------------
    // aes
    //----------------------------------------------------------------
    logic aes_cs;
    logic aes_we;
    logic [AHB_ADDR_WIDTH-1:0] aes_address;
    logic [AHB_DATA_WIDTH-1:0] aes_write_data;
    logic [AHB_DATA_WIDTH-1:0] aes_read_data;

    `ifdef AES_CBC_MODE
        aes_cbc #(
        .ADDR_WIDTH(AHB_ADDR_WIDTH),
        .DATA_WIDTH(32)
        ) aes_inst(
        .clk(clk),
        .reset_n(reset_n),
        .cptra_pwrgood(cptra_pwrgood),
        .cptra_obf_key(cptra_obf_key),
        .obf_uds_seed(obf_uds_seed),
        .obf_field_entropy(obf_field_entropy),
        .cs(aes_cs),
        .we(aes_we),
        .address(aes_address),
        .write_data(aes_write_data[31:0]),
        .read_data(aes_read_data[31:0]),
        .error_intr(error_intr),
        .notif_intr(notif_intr),
        .kv_write(kv_write)
        );
    `else
        aes #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32)
        )
        aes_inst(
        .clk(clk),
        .reset_n(reset_n),
        .cs(aes_cs),
        .we(aes_we),
        .address(aes_address),
        .write_data(aes_write_data),
        .read_data(aes_read_data)
        );
        always_comb begin
            error_intr = 1'b0; // TODO
            notif_intr = 1'b0; // TODO
        end
    `endif

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
    .dv(aes_cs),
    .hld(1'b0), //no holds from aes
    .err(1'b0), //no errors from aes
    .write(aes_we),
    .wdata(aes_write_data[31:0]),
    .addr(aes_address),

    .rdata(aes_read_data[31:0])
);

endmodule
