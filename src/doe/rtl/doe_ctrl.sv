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
// doe_ctrl.sv
// --------
// DOE controller for the AHb_lite interface.
// DOE is the de-obfuscation engine, used to de-obfuscate the device secrets
//
//======================================================================
`include "caliptra_macros.svh"

module doe_ctrl 
    import doe_defines_pkg::*;
    import kv_defines_pkg::*;
    #(
    parameter AHB_DATA_WIDTH = 32,
    parameter AHB_ADDR_WIDTH = 32,
    localparam TOTAL_OBF_KEY_BITS = `CLP_OBF_KEY_DWORDS * 32
)
(
    // Clock and reset.
    input wire          clk,
    input wire          reset_n,
    input wire          cptra_pwrgood,

    input logic [TOTAL_OBF_KEY_BITS-1:0] cptra_obf_key,

    //Obfuscated UDS and FE
    input logic [`CLP_OBF_FE_DWORDS-1 :0][31:0] obf_field_entropy,
    input logic [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed,

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
    input  kv_wr_resp_t kv_wr_resp,

    output logic clear_obf_secrets,

    // Interrupt
    output logic error_intr,
    output logic notif_intr,
    input  logic debugUnlock_or_scan_mode_switch
);

    //----------------------------------------------------------------
    // doe
    //----------------------------------------------------------------
    logic doe_cs;
    logic doe_we;
    logic [AHB_ADDR_WIDTH-1:0] doe_address;
    logic [AHB_DATA_WIDTH-1:0] doe_write_data;
    logic [AHB_DATA_WIDTH-1:0] doe_read_data;

    doe_cbc #(
        .ADDR_WIDTH(AHB_ADDR_WIDTH),
        .DATA_WIDTH(32)
    ) doe_inst(
        .clk(clk),
        .reset_n(reset_n),
        .cptra_pwrgood(cptra_pwrgood),
        .cptra_obf_key(cptra_obf_key),
        .obf_uds_seed(obf_uds_seed),
        .obf_field_entropy(obf_field_entropy),
        .cs(doe_cs),
        .we(doe_we),
        .address(doe_address),
        .write_data(doe_write_data[31:0]),
        .read_data(doe_read_data[31:0]),
        .error_intr(error_intr),
        .notif_intr(notif_intr),
        .clear_obf_secrets(clear_obf_secrets),
        .kv_write(kv_write),
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
        .dv(doe_cs),
        .hld(1'b0), //no holds from doe
        .err(1'b0), //no errors from doe
        .write(doe_we),
        .wdata(doe_write_data[31:0]),
        .addr(doe_address),

        .rdata(doe_read_data[31:0])
    );

endmodule
