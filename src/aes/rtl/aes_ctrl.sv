//======================================================================
//
// aes_ctrl.sv
// --------
// AES controller for the AES block cipher core.
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module aes_ctrl #(
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

    // AES address map.
    parameter ADDR_CTRL        = 8'h08;
    parameter CTRL_INIT_BIT    = 0;
    parameter CTRL_NEXT_BIT    = 1;
    parameter CTRL_ENCDEC_BIT  = 2;
    parameter CTRL_KEYLEN_BIT  = 3;

    parameter ADDR_STATUS      = 8'h09;
    parameter STATUS_READY_BIT = 0;
    parameter STATUS_VALID_BIT = 1;

    parameter ADDR_CONFIG      = 8'h0a;

    parameter ADDR_KEY0        = 8'h10;
    parameter ADDR_KEY1        = 8'h11;
    parameter ADDR_KEY2        = 8'h12;
    parameter ADDR_KEY3        = 8'h13;
    parameter ADDR_KEY4        = 8'h14;
    parameter ADDR_KEY5        = 8'h15;
    parameter ADDR_KEY6        = 8'h16;
    parameter ADDR_KEY7        = 8'h17;

    parameter ADDR_BLOCK0      = 8'h20;
    parameter ADDR_BLOCK1      = 8'h21;
    parameter ADDR_BLOCK2      = 8'h22;
    parameter ADDR_BLOCK3      = 8'h23;

    parameter ADDR_RESULT0     = 8'h30;
    parameter ADDR_RESULT1     = 8'h31;
    parameter ADDR_RESULT2     = 8'h32;
    parameter ADDR_RESULT3     = 8'h33;


    //----------------------------------------------------------------
    // AHB Slave node
    //----------------------------------------------------------------
    logic write;
    logic [31:0] addr;
    logic [63:0] rdata;
    
    logic [63:0] hwdata;

    always @ (negedge clk) begin
        if(hready_i & hsel_i)
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

    assign hrdata_o = hready_i ? rdata : ~rdata;
    assign hreadyout_o = wscnt == 0;
    assign hresp_o = 0;

    always @(posedge clk or negedge reset_n) begin
        if(!reset_n) begin
            write <= 1'b0;
            rdata <= '0;
        end
        else begin
            if(hready_i & hsel_i) begin
                write <= hwrite_i & |htrans_i;
                if(|htrans_i & ~hwrite_i)
                    rdata <= {mem[1], mem[0]};
            end
        end
    end


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

    //----------------------------------------------------------------
    // aes
    //----------------------------------------------------------------
    reg           aes_cs,
    reg           aes_we,
    reg  [7 : 0]  aes_address,
    reg  [31 : 0] aes_write_data,
    reg  [31 : 0] aes_read_data

    aes aes_inst(
        .clk(clk),
        .reset_n(reset_n),
        .cs(aes_cs),
        .we(aes_we),
        .address(aes_address),
        .write_data(aes_write_data),
        .read_data(aes_read_data)
    );

    //----------------------------------------------------------------
    // aes_ctrl state machine
    //----------------------------------------------------------------

    enum {idle, aes_config, set_key, set_input, get_output} currstate, nextstate;

    always_ff @(posedge CLK) begin
        if (!reset_n)
            currstate <= idle;
        else
            currstate <= nextstate;
    end

    always_comb begin
        nextstate = currstate; // default is to stay in current state
        unique case (currstate)
            idle   : nextstate = (configaddr & fifo_in_empty) ? set_config :  
                                 (keyaddr & fifo_in_empty)? set_key : 
                                 (datainaddr & !fifo_in_full)? set_input : 
                                 (dataoutaddr & !fifo_out_empty)? get_output : idle;

            aes_config : if (config_ready) nextstate = idle;
            set_key : if (key_ready) nextstate = idle;
            set_input : if (datain_ready) nextstate = idle;
            get_output: if (dataout_ready) nextstate = idle;
        endcase
    end

    logic configaddr, keyaddr, datainaddr, dataoutaddr;
    always_comb begin
        configaddr = (addr == ADDR_CONFIG) ? 1 : 0;
        keyaddr = (addr >= ADDR_KEY0) && (addr <= ADDR_KEY7) ? 1 : 0;
        datainaddr = (addr >= ADDR_BLOCK0) && (addr <= ADDR_BLOCK3) ? 1 : 0;
        dataoutaddr = (addr >= ADDR_RESULT0) && (addr <= ADDR_RESULT3) ? 1 : 0;
    end

    always_ff @(posedge CLK or negedge reset_n) begin
        unique case (currstate)
            idle : 
                begin
                    aes_cs = 0;
                    aes_we = 0;
                    aes_write_data = '0;
                    aes_address = '0;
                end
            aes_config : 
                begin
                    aes_cs = 1;
                    aes_we = write;
                    aes_write_data = addr;
                    aes_address = hwdata[31:0];
                end 
            set_key :
                begin
                    aes_cs = 1;
                    aes_we = write;
                    aes_write_data = addr;
                    aes_address = hwdata[31:0];
                end 
            set_input :
                begin
                    aes_cs = 1;
                    aes_we = write;
                    aes_write_data = addr;
                    aes_address = hwdata[31:0];
                end 
            set_input : if (!dataaddr) nextstate = idle; : if (!dataaddr) nextstate = idle;
        endcase
    end


endmodule