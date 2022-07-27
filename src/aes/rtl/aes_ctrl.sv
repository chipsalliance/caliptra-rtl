//======================================================================
//
// aes_ctrl.sv
// --------
// AES controller for the AHb_lite interface.
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module aes_ctrl #(
    parameter AHB_DATA_WIDTH = 32,
    parameter AHB_ADDR_WIDTH = 32,
    parameter BYPASS_HSEL = 0
)
(
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // from SLAVES PORT
    input logic [AHB_ADDR_WIDTH-1:0] haddr_i,
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
    output logic [AHB_DATA_WIDTH-1:0] hrdata_o
);

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  `include "aes_param.sv"

    //----------------------------------------------------------------
    // aes
    //----------------------------------------------------------------
    logic aes_cs;
    logic aes_we;
    logic [AHB_ADDR_WIDTH-1:0] aes_address;
    logic [31:0] aes_write_data;
    logic [31:0] aes_read_data;

    `ifdef AES_CBC_MODE
        aes_cbc #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32)
        ) aes_inst(
        .clk(clk),
        .reset_n(reset_n),
        .cs(aes_cs),
        .we(aes_we),
        .address(aes_address),
        .write_data(aes_write_data),
        .read_data(aes_read_data)
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
    `endif

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
    .hold('0), //no holds from aes
    .error('0), //no errors from aes
    .write(aes_we),
    .wdata(aes_write_data),
    .addr(aes_address),

    .rdata(aes_read_data)
);

endmodule
