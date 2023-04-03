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


module caliptra_ahb_srom 
 import ahb_defines_pkg::*;
 #(
    parameter AHB_DATA_WIDTH    = 64,
    parameter AHB_ADDR_WIDTH    = 32,
    parameter CLIENT_ADDR_WIDTH = 32
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


    //response to uC
    output logic                      hresp_o,
    output logic                      hreadyout_o,
    output logic [AHB_DATA_WIDTH-1:0] hrdata_o,

    //SROM Inf
    output logic cs,
    output logic [CLIENT_ADDR_WIDTH-1:0] addr,
    input logic [AHB_DATA_WIDTH-1:0] rdata

);

//`define H_OKAY 1'b0;
//`define H_ERROR 1'b1;

/////////////////////////////////
// Signals
logic                       sram_error, sram_error_data_ph, sram_error_data_ph_f;

/////////////////////////////////
// Assignments/Shim logic
assign cs = hready_i & hsel_i & htrans_i inside {2'b10, 2'b11};
assign addr = haddr_i >> $clog2(AHB_DATA_WIDTH/8);

assign sram_error = cs & hwrite_i; // Error if trying to write to ROM

assign hrdata_o = rdata;

always_comb begin : response_block
    hreadyout_o = 1'b1;
    hresp_o = H_OKAY;
    //first error cycle, de-assert ready and drive error
    if (sram_error_data_ph & ~sram_error_data_ph_f) begin
        hreadyout_o = 1'b0;
        hresp_o = H_ERROR;
    end else if (sram_error_data_ph_f) begin
        hreadyout_o = 1'b1;
        hresp_o = H_ERROR;
    end
end

//flop error to indicate second cycle of error
always_ff @(posedge hclk or negedge hreset_n) begin
    if (~hreset_n) begin
        sram_error_data_ph <= '0;
        sram_error_data_ph_f <= '0;
    end else begin
        sram_error_data_ph <= sram_error;
        sram_error_data_ph_f <= sram_error_data_ph;
    end
end

endmodule
