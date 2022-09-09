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

`include "ecc_defines.svh"


module ecc_top #(
    parameter AHB_ADDR_WIDTH = 32,
    parameter AHB_DATA_WIDTH = 32
    )
    (
    input logic                       clk,
    input logic                       reset_n,

    //AHB Lite Interface
    input logic [AHB_ADDR_WIDTH-1:0]  haddr_i,
    input logic [AHB_DATA_WIDTH-1:0]  hwdata_i,
    input logic                       hsel_i,
    input logic                       hwrite_i,
    input logic                       hmastlock_i,
    input logic                       hready_i,
    input logic [1:0]                 htrans_i,
    input logic [3:0]                 hprot_i,
    input logic [2:0]                 hburst_i,
    input logic [2:0]                 hsize_i,

    output logic                      hresp_o,
    output logic                      hreadyout_o,
    output logic [AHB_DATA_WIDTH-1:0] hrdata_o
);

    //gasket to assemble ecc request
    logic ecc_cs;
    logic [AHB_DATA_WIDTH-1:0] uc_req_rdata;
    ecc_req_t uc_req;

    logic ecc_reg_error, ecc_reg_read_error, ecc_reg_write_error;

    ecc_reg_pkg::ecc_reg__in_t ecc_reg_hwif_in;
    ecc_reg_pkg::ecc_reg__out_t ecc_reg_hwif_out;

    //AHB-Lite Interface
    //This module contains the logic for interfacing with the Caliptra uC over the AHB-Lite Interface
    //The Caliptra uC sends read and write requests using AHB-Lite Protocol
    //This wrapper decodes that protocol and issues requests to the arbitration block
    ahb_slv_sif #(
        .ADDR_WIDTH(AHB_ADDR_WIDTH),
        .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
        .CLIENT_DATA_WIDTH(32)
    )
    ecc_ahb_slv_i (
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
        .dv(ecc_cs),
        .hold('0),
        .error(ecc_reg_error),
        .write(uc_req.write),
        .wdata(uc_req.wdata),
        .addr(uc_req.addr),

        .rdata(uc_req_rdata)
    );

    //Functional Registers
    //This module contains the functional registers maintained by the Caliptra ECC
    //These registers are memory mapped per the Caliptra Specification
    //Read and Write permissions are controlled within this block
    always_comb ecc_reg_error = ecc_reg_read_error | ecc_reg_write_error;

    ecc_reg ecc_reg1 (
        .clk(clk),
        .rst('0),

        .s_cpuif_req(ecc_cs),
        .s_cpuif_req_is_wr(uc_req.write),
        .s_cpuif_addr(uc_req.addr),
        .s_cpuif_wr_data(uc_req.wdata),
        .s_cpuif_req_stall_wr(),
        .s_cpuif_req_stall_rd(),
        .s_cpuif_rd_ack(),
        .s_cpuif_rd_err(ecc_reg_read_error),
        .s_cpuif_rd_data(uc_req_rdata),
        .s_cpuif_wr_ack(),
        .s_cpuif_wr_err(ecc_reg_write_error),

        .hwif_in(ecc_reg_hwif_in),
        .hwif_out(ecc_reg_hwif_out)
    );

    ecc_dsa_ctrl ecc_dsa_ctrl_i(
        .clk(clk),
        .reset_n(reset_n),

        .hwif_in(ecc_reg_hwif_out),
        .hwif_out(ecc_reg_hwif_in)
    );

endmodule