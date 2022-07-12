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

`include "mbox_defines.svh"

module mbox_top #(
     parameter APB_ADDR_WIDTH = 32
    ,parameter APB_DATA_WIDTH = 32
    ,parameter APB_USER_WIDTH = 32
    ,parameter AHB_ADDR_WIDTH = 32
    ,parameter AHB_DATA_WIDTH = 32
    )
    (
    input logic clk,

    //SoC boot signals
    input logic cptra_pwrgood,
    input logic cptra_rst_b,

    //SoC APB Interface
    input logic [APB_ADDR_WIDTH-1:0]     paddr_i,
    input logic                          psel_i,
    input logic                          penable_i,
    input logic                          pwrite_i,
    input logic [APB_DATA_WIDTH-1:0]     pwdata_i,
    input logic [APB_USER_WIDTH-1:0]     pauser_i,
    output logic                         pready_o,
    output logic [APB_DATA_WIDTH-1:0]    prdata_o,
    output logic                         pslverr_o,

    //uC AHB Lite Interface
    // from SLAVES PORT
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
    output logic [AHB_DATA_WIDTH-1:0] hrdata_o,

    //SoC Interrupts

    //uC Interrupts

    //uC reset
    output logic cptra_uc_rst_b
);

//gasket to assemble mailbox request
logic soc_req_dv, soc_req_hold;
logic soc_req_error;
logic [APB_DATA_WIDTH-1:0] soc_req_rdata;
mbox_req_t soc_req;

//gasket to assemble mailbox request
logic uc_req_dv, uc_req_hold;
logic uc_req_error;
logic [AHB_DATA_WIDTH-1:0] uc_req_rdata;
mbox_req_t uc_req;

//mbox req inf
logic mbox_req_dv;
logic mbox_req_hold;
mbox_req_t mbox_req_data;
logic [MBOX_DATA_W-1:0] mbox_rdata;
logic mbox_error;

//Boot FSM
//This module contains the logic required to control the Caliptra Boot Flow
//Once the SoC has powered on Caliptra and de-asserted RESET, we can request fuses
//This FSM will de-assert reset and allow the Caliptra uC to boot after fuses are downloaded
mbox_boot_fsm mbox_boot_fsm1 (
    .clk(clk),
    .cptra_pwrgood(cptra_pwrgood),
    .cptra_rst_b (cptra_rst_b),

    .fuse_done('1), //FIXME TIE-OFF

    .cptra_uc_rst_b(cptra_uc_rst_b)
);

//APB Interface
//This module contains the logic for interfacing with the SoC over the APB Interface
//The SoC sends read and write requests using APB Protocol
//This wrapper decodes that protocol and issues requests to the arbitration block
apb_slv_sif #(
    .ADDR_WIDTH(APB_ADDR_WIDTH),
    .DATA_WIDTH(APB_DATA_WIDTH),
    .USER_WIDTH(APB_USER_WIDTH)
)
mailbox_apb_slv1 (
    //AMBA APB INF
    .PCLK(clk),
    .PRESETn(cptra_uc_rst_b),
    .PADDR(paddr_i),
    .PPROT('x),
    .PSEL(psel_i),
    .PENABLE(penable_i),
    .PWRITE(pwrite_i),
    .PWDATA(pwdata_i),
    .PAUSER(pauser_i),

    .PREADY(pready_o),
    .PSLVERR(pslverr_o),
    .PRDATA(prdata_o),

    //COMPONENT INF
    .dv(soc_req_dv),
    .hold(soc_req_hold),
    .write(soc_req.write),
    .user(soc_req.user),
    .wdata(soc_req.wdata),
    .addr(soc_req.addr),
    .slverr(soc_req_error),
    .rdata(soc_req_rdata)
);
//req from apb is for soc always
always_comb soc_req.soc_req = 1'b1;

//AHB-Lite Interface
//This module contains the logic for interfacing with the Caliptra uC over the AHB-Lite Interface
//The Caliptra uC sends read and write requests using AHB-Lite Protocol
//This wrapper decodes that protocol and issues requests to the arbitration block
ahb_slv_sif #(
    .ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(32)
)
mailbox_ahb_slv1 (
    //AMBA AHB Lite INF
    .hclk(clk),
    .hreset_n(cptra_uc_rst_b),
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
    .dv(uc_req_dv),
    .hold(uc_req_hold),
    .error(uc_req_error),
    .write(uc_req.write),
    .wdata(uc_req.wdata),
    .addr(uc_req.addr),

    .rdata(uc_req_rdata)
);

always_comb uc_req.user = '1;
always_comb uc_req.soc_req = 1'b0;

//mailbox_arb
//This module contains the arbitration logic between SoC and Caliptra uC requests
//Requests are serviced using round robin arbitration

mbox_arb mbox_arb1 (
    .clk(clk),
    .rst_b(cptra_uc_rst_b),
    //UC inf
    .uc_req_dv(uc_req_dv), //FIXME TIE-OFF
    .uc_req_hold(uc_req_hold), //FIXME DANGLE
    .uc_req_data(uc_req), //FIXME TIE-OFF
    .uc_rdata(uc_req_rdata), //FIXME DANGLE
    .uc_error(uc_req_error),
    //SOC inf
    .soc_req_dv(soc_req_dv),
    .soc_req_hold(soc_req_hold),
    .soc_req_data(soc_req),
    .soc_rdata(soc_req_rdata),
    .soc_error(soc_req_error),
    //MBOX inf
    .mbox_req_dv(mbox_req_dv),
    .mbox_req_hold(1'b0), //FIXME TIE-OFF
    .mbox_req_data(mbox_req_data),
    .mbox_rdata(mbox_rdata),
    .mbox_error(mbox_error),
    //FUNC reg inf
    .func_reg_req_dv(), //FIXME DANGLE
    .func_reg_req_hold('1),//FIXME TIE-OFF
    .func_reg_req_data(), //FIXME DANGLE
    .func_reg_rdata('1),//FIXME TIE-OFF
    .func_reg_error('1),//FIXME TIE-OFF
    //FUSE reg inf
    .fuse_reg_req_dv(), //FIXME DANGLE
    .fuse_reg_req_hold('1),//FIXME TIE-OFF
    .fuse_reg_req_data(), //FIXME DANGLE
    .fuse_reg_rdata('1),//FIXME TIE-OFF
    .fuse_reg_error('1)//FIXME TIE-OFF

);

//Functional Registers
//This module contains the functional registers maintained by the Caliptra Mailbox
//These registers are memory mapped per the Caliptra Specification
//Read and Write permissions are controlled within this block

//TODO: mbox_func_reg

//Fuses
//This module contains the fuse registers maintained by the Caliptra Mailbox
//These fuses are memory mapped per the Caliptra Specification
//Read and Write permissions are controlled within this block

//TODO: mbox_fuse_reg

//Mailbox
//This module contains the Caliptra Mailbox and associated control logic
//The SoC and uC can read and write to the mailbox by following the Caliptra Mailbox Protocol

mbox #(
    .DATA_W(APB_DATA_WIDTH),
    .SIZE_KB(128),
    .BASE_ADDR(32'h3000_0000)
    )
mbox1 (
    .clk(clk),
    .rst_b(cptra_uc_rst_b),
    .req_dv(mbox_req_dv), 
    .req_data(mbox_req_data),
    .mbox_error(mbox_error),
    .rdata(mbox_rdata),
    .soc_mbox_data_avail(), //FIXME DANGLE
    .uc_mbox_data_avail() //FIXME DANGLE
);

`ASSERT_KNOWN(ERR_AHB_INF_X, {hreadyout_o,hresp_o}, clk, cptra_rst_b)

endmodule