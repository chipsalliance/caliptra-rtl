//======================================================================
//
// sha256_ctrl.sv
// --------
// SHA256 controller for the AHb_lite interface.
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module sha256_ctrl #(
    parameter AHB_DATA_WIDTH = 64,
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
    // sha256
    //----------------------------------------------------------------
    reg           sha256_cs;
    reg           sha256_we;
    reg  [31 : 0] sha256_address;
    reg  [63 : 0] sha256_write_data;
    reg  [63 : 0] sha256_read_data;
    reg           sha256_error;

    sha256 sha256_inst(
        .clk(clk),
        .reset_n(reset_n),
        .cs(sha256_cs),
        .we(sha256_we),
        .address(sha256_address),
        .write_data(sha256_write_data),
        .read_data(sha256_read_data),
        .error(sha256_error)
    );


    //----------------------------------------------------------------
    // AHB Slave node
    //----------------------------------------------------------------
        
    //instantiate ahb lite module
    ahb_slv_sif #(
        .ADDR_WIDTH(AHB_ADDR_WIDTH),
        .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
        .CLIENT_DATA_WIDTH(64)
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
        .hold('0), //no holds from sha256
        .error('0),
        .write(sha256_we),
        .wdata(sha256_write_data),
        .addr(sha256_address),

        .rdata(sha256_read_data)
    );

endmodule
