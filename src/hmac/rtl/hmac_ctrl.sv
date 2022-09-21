//======================================================================
//
// hmac_ctrl.sv
// --------
// HMAC controller for the AHb_lite interface.
//
//
// Author: Mojtaba Bisheh-Niasar
// Updated by: Emre Karabulut 07/22/2022
// 
// I integrated the HMAC unit into the AHB bus port and so all signals go
// through the AHB bus. I converted the data bus from 64 to a parametric one.
// 
// 
//======================================================================

`include "kv_defines.svh"

module hmac_ctrl #(
    parameter AHB_DATA_WIDTH = 32,
    parameter AHB_ADDR_WIDTH = 32,
    parameter BYPASS_HSEL = 0
)
(
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // from SLAVES PORT
    input logic [AHB_ADDR_WIDTH-1:0] hadrr_i,
    input logic [AHB_DATA_WIDTH-1:0] hwdata_i,
    input logic hsel_i,
    input logic hwrite_i,
    input logic hmastlock_i,
    input logic hready_i,
    input logic [1:0] htrans_i,
    input logic [3:0] hprot_i,
    input logic [2:0] hburst_i,
    input logic [2:0] hsize_i,

    output logic hresp_o,
    output logic hreadyout_o,
    output logic [AHB_DATA_WIDTH-1:0] hrdata_o,

    // kv interface
    output kv_read_t kv_read,
    output kv_write_t kv_write,
    input kv_resp_t kv_resp
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
        .ADDR_WIDTH (AHB_ADDR_WIDTH)
        ) hmac_inst
        (
        .clk(clk),
        .reset_n(reset_n),
        .cs(hmac_cs),
        .we(hmac_we),
        .address(hmac_address),
        .write_data(hmac_write_data),
        .read_data(hmac_read_data),
        .kv_read(kv_read),
        .kv_write(kv_write),
        .kv_resp(kv_resp)
    );

    //instantiate ahb lite module
ahb_slv_sif #(
    .ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(32)
) ahb_slv_sif_uut
(
    //AMBA AHB Lite INF
    .hclk(clk),
    .hreset_n(reset_n),
    .haddr_i(hadrr_i),
    .hwdata_i(hwdata_i),
    .hsel_i(hsel_i),
    .hwrite_i(hwrite_i),
    .hready_i(hready_i),
    .htrans_i(htrans_i),
    .hsize_i(hsize_i),
    .hburst_i(hburst_i),

    .hresp_o(hresp_o),
    .hreadyout_o(hreadyout_o),
    .hrdata_o(hrdata_o),

    .hmastlock_i(hmastlock_i),
    .hprot_i(hprot_i),

    //COMPONENT INF
    .dv(hmac_cs),
    .hold('0), //no holes from hmac
    .error('0), //no errors from hmac
    .write(hmac_we),
    .wdata(hmac_write_data),
    .addr(hmac_address),

    .rdata(hmac_read_data)
);

    


endmodule