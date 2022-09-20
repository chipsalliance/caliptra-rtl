//======================================================================
//
// sha512_ctrl.sv
// --------
// SHA512 controller for the AHb_lite interface.
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module sha512_ctrl #(
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
    // sha512
    //----------------------------------------------------------------
    reg           sha512_cs;
    reg           sha512_we;
    reg  [AHB_ADDR_WIDTH : 0] sha512_address;
    reg  [31 : 0] sha512_write_data;
    reg  [31 : 0] sha512_read_data;
    reg           sha512_error;

    sha512 #(
        .ADDR_WIDTH(AHB_ADDR_WIDTH),
        .DATA_WIDTH(32)
        )
        sha512_inst(
        .clk(clk),
        .reset_n(reset_n),
        .cs(sha512_cs),
        .we(sha512_we),
        .address(sha512_address),
        .write_data(sha512_write_data),
        .read_data(sha512_read_data),
        .error(sha512_error)
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
        .hold('0), //no holds from sha512
        .error('0),
        .write(sha512_we),
        .wdata(sha512_write_data),
        .addr(sha512_address),

        .rdata(sha512_read_data)
    );


endmodule  // sha512_ctrl

//======================================================================
// EOF sha512_ctrl.sv
//======================================================================
