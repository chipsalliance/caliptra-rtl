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
//======================================================================
//
// ecc_top.sv
// --------
// top-level wrapper for ecc architecture including:
// 1- ecc_dsa_ctrl module as ecc engin
// 2- ecc_reg module as register memory of ecc to interface with external
// 3- ahb_slv_sif module to handle AHB-lite interface
//======================================================================

module ecc_top
    import ecc_defines_pkg::*;
    import ecc_reg_pkg::*;
    import kv_defines_pkg::*;
    #(
    parameter AHB_ADDR_WIDTH = 32,
    parameter AHB_DATA_WIDTH = 32,
    parameter CLIENT_DATA_WIDTH = 32
    )
    (
    input wire                        clk,
    input wire                        reset_n,
    input wire                        cptra_pwrgood,

    //AHB Lite Interface
    input wire  [AHB_ADDR_WIDTH-1:0]  haddr_i,
    input wire  [AHB_DATA_WIDTH-1:0]  hwdata_i,
    input wire                        hsel_i,
    input wire                        hwrite_i,
    input wire                        hready_i,
    input wire  [1:0]                 htrans_i,
    input wire  [2:0]                 hsize_i,

    output logic                      hresp_o,
    output logic                      hreadyout_o,
    output logic [AHB_DATA_WIDTH-1:0] hrdata_o,

    // KV interface
    output kv_read_t [1:0] kv_read,
    output kv_write_t kv_write,
    input kv_rd_resp_t [1:0] kv_rd_resp,
    input kv_wr_resp_t kv_wr_resp,   
    //PCR Signing
    input pcr_signing_t pcr_signing_data,

    input  logic ocp_lock_in_progress,
    output logic busy_o,

    output logic error_intr,
    output logic notif_intr,
    input  logic debugUnlock_or_scan_mode_switch
);

    //gasket to assemble ecc request
    logic ecc_cs;
    logic [CLIENT_DATA_WIDTH-1:0] uc_req_rdata;
    ecc_req_t uc_req;

    logic ecc_reg_err, ecc_reg_read_err, ecc_reg_write_err;

    ecc_reg__in_t ecc_reg_hwif_in;
    ecc_reg__out_t ecc_reg_hwif_out;

    //AHB-Lite Interface
    //This module contains the logic for interfacing with the Caliptra uC over the AHB-Lite Interface
    //The Caliptra uC sends read and write requests using AHB-Lite Protocol
    //This wrapper decodes that protocol and issues requests to the arbitration block
    ahb_slv_sif #(
        .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
        .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
        .CLIENT_DATA_WIDTH(CLIENT_DATA_WIDTH)
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
        .hld('0),
        .err(ecc_reg_err),
        .write(uc_req.write),
        .wdata(uc_req.wdata),
        .addr(uc_req.addr[AHB_ADDR_WIDTH-1:0]),

        .rdata(uc_req_rdata)
    );

    //Functional Registers
    //This module contains the functional registers maintained by the Caliptra ECC
    //These registers are memory mapped per the Caliptra Specification
    //Read and Write permissions are controlled within this block
    always_comb ecc_reg_err = ecc_reg_read_err | ecc_reg_write_err;

    ecc_reg ecc_reg1 (
        .clk(clk),
        .rst(reset_n),

        .s_cpuif_req(ecc_cs),
        .s_cpuif_req_is_wr(uc_req.write),
        .s_cpuif_addr(uc_req.addr[ECC_REG_ADDR_WIDTH-1:0]),
        .s_cpuif_wr_data(uc_req.wdata),
        .s_cpuif_wr_biten('1),
        .s_cpuif_req_stall_wr(),
        .s_cpuif_req_stall_rd(),
        .s_cpuif_rd_ack(),
        .s_cpuif_rd_err(ecc_reg_read_err),
        .s_cpuif_rd_data(uc_req_rdata),
        .s_cpuif_wr_ack(),
        .s_cpuif_wr_err(ecc_reg_write_err),

        .hwif_in(ecc_reg_hwif_in),
        .hwif_out(ecc_reg_hwif_out)
    );

    ecc_dsa_ctrl ecc_dsa_ctrl_i(
        .clk(clk),
        .reset_n(reset_n),
        .cptra_pwrgood(cptra_pwrgood),

        .hwif_out(ecc_reg_hwif_out),
        .hwif_in(ecc_reg_hwif_in),

        .kv_read(kv_read),
        .kv_rd_resp(kv_rd_resp),
        .kv_write(kv_write),
        .kv_wr_resp(kv_wr_resp),
        .pcr_signing_data(pcr_signing_data),
        
        .ocp_lock_in_progress(ocp_lock_in_progress),
        .busy_o(busy_o),

        .error_intr(error_intr),
        .notif_intr(notif_intr),
        .debugUnlock_or_scan_mode_switch(debugUnlock_or_scan_mode_switch)
    );

endmodule
