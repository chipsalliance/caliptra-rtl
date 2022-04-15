//======================================================================
//
// sha512_ctrl.sv
// --------
// AES controller for the AES block cipher core.
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module sha512_ctrl #(
    parameter AHB_DATA_WIDTH = 64,
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
    output logic [AHB_DATA_WIDTH-1:0] hrdata_o
);

    //----------------------------------------------------------------
    // Internal constant and parameter definitions.
    //----------------------------------------------------------------

    // The sha512 address map.
    parameter ADDR_NAME0           = 8'h00;
    parameter ADDR_NAME1           = 8'h01;
    parameter ADDR_VERSION         = 8'h02;

    parameter ADDR_CTRL            = 8'h08;
    parameter ADDR_STATUS          = 8'h09;
    parameter ADDR_WORK_FACTOR_NUM = 8'h0a;

    parameter ADDR_BLOCK0          = 8'h10;
    parameter ADDR_BLOCK1          = 8'h11;
    parameter ADDR_BLOCK2          = 8'h12;
    parameter ADDR_BLOCK3          = 8'h13;
    parameter ADDR_BLOCK4          = 8'h14;
    parameter ADDR_BLOCK5          = 8'h15;
    parameter ADDR_BLOCK6          = 8'h16;
    parameter ADDR_BLOCK7          = 8'h17;
    parameter ADDR_BLOCK8          = 8'h18;
    parameter ADDR_BLOCK9          = 8'h19;
    parameter ADDR_BLOCK10         = 8'h1a;
    parameter ADDR_BLOCK11         = 8'h1b;
    parameter ADDR_BLOCK12         = 8'h1c;
    parameter ADDR_BLOCK13         = 8'h1d;
    parameter ADDR_BLOCK14         = 8'h1e;
    parameter ADDR_BLOCK15         = 8'h1f;

    parameter ADDR_DIGEST0         = 8'h40;
    parameter ADDR_DIGEST1         = 8'h41;
    parameter ADDR_DIGEST2         = 8'h42;
    parameter ADDR_DIGEST3         = 8'h43;
    parameter ADDR_DIGEST4         = 8'h44;
    parameter ADDR_DIGEST5         = 8'h45;
    parameter ADDR_DIGEST6         = 8'h46;
    parameter ADDR_DIGEST7         = 8'h47;

    parameter MODE_SHA_512_224     = 2'h0;
    parameter MODE_SHA_512_256     = 2'h1;
    parameter MODE_SHA_384         = 2'h2;
    parameter MODE_SHA_512         = 2'h3;

    //----------------------------------------------------------------
    // AHB Slave node
    //----------------------------------------------------------------
    logic cs;
    logic write;
    logic [31:0] addr;
    logic [63:0] hrdata;
    
    logic [63:0] hwdata;
    logic [63:0] rdata;

    always @ (posedge clk) begin
        cs = (hsel_i & hready_i)? 1 : 0;
        if(hsel_i & hready_i)
            addr = hadrr_i;
        if (write & hready_i) begin
            case (hsize_i)
                3'b000: 
                    hwdata = {56'h00000000000000, hwdata_i[7:0]};
                3'b001: 
                    hwdata = {48'h000000000000, hwdata_i[15:0]};
                3'b010: 
                    hwdata = {32'h00000000, hwdata_i[31:0]};
                default:  // 3'b011: 
                    hwdata = hwdata_i[63:0];
            endcase;
        end
    end

    assign hrdata_o = hready_i ? hrdata : ~hrdata;
    assign hreadyout_o = 1; //wscnt == 0;
    assign hresp_o = 0;

    always @(posedge clk or negedge reset_n) begin
        if(!reset_n) begin
            write <= 1'b0;
            hrdata <= '0;
        end
        else begin
            if(hready_i & hsel_i) begin
                write <= hwrite_i & |htrans_i;
                if(|htrans_i & ~hwrite_i)
                    hrdata <= rdata;
            end
        end
    end

    /*
    //----------------------------------------------------------------
    // fifo_in
    //----------------------------------------------------------------
    reg                     fifo_in_we,
    reg                     fifo_in_rd,
    reg                     fifo_in_full,
    reg                     fifo_in_empty,
    reg [DATA_WIDTH-1 : 0]  fifo_in_write_data,
    reg [DATA_WIDTH-1 : 0]  fifo_in_read_data

    fifo  fifo_in #(
        RAM_ADDR_WIDTH = 5,
        DATA_WIDTH = 64
    )
    (
        .clk(clk),
        .reset_n(reset_n),
        .we(fifo_in_we),
        .rd(fifo_in_rd),
        .fifo_full(fifo_in_full),
        .fifo_empty(fifo_in_empty),
        .write_data(fifo_in_write_data),
        .read_data(fifo_in_read_data)
    );
    */

    //----------------------------------------------------------------
    // sha512
    //----------------------------------------------------------------
    reg           sha512_cs;
    reg           sha512_we;
    reg  [7 : 0]  sha512_address;
    reg  [63 : 0] sha512_write_data;
    reg  [63 : 0] sha512_read_data;
    reg           sha512_error;

    sha512 sha512_inst(
        .clk(clk),
        .reset_n(reset_n),
        .cs(sha512_cs),
        .we(sha512_we),
        .address(sha512_address),
        .write_data(sha512_write_data),
        .read_data(sha512_read_data),
        .error(sha512_error)
    );

    //----------------------------------------------------------------
    // aes_ctrl state machine
    //----------------------------------------------------------------

    always_ff @ (posedge clk) begin
        sha512_cs = cs;
        sha512_we = write;
        sha512_address = addr[7 : 0];
    end

    always_comb begin
        sha512_write_data = hwdata;
        rdata = sha512_read_data;
    end

endmodule