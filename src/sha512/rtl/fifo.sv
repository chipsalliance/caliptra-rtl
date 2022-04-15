//======================================================================
//
// fifo.sv
// --------
// FIFO for the AES block cipher core.
//
//
// Author: Mojtaba Bisheh-Niasar
//======================================================================

module fifo #(
  parameter RAM_ADDR_WIDTH = 5;
  parameter DATA_WIDTH = 32;
)
(
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,

    // Control.
    input wire           we,
    input wire           rd,
    output wire          fifo_full,
    output wire          fifo_empty,

    // Data ports.
    input wire  [DATA_WIDTH-1 : 0] write_data,
    output wire [DATA_WIDTH-1 : 0] read_data
);


    parameter RAM_DEPTH = 2**RAM_ADDR_WIDTH

    logic [RAM_ADDR_WIDTH-1:0] wr_addr, rd_addr;
    logic [RAM_DEPTH-1:0] ram[DATA_WIDTH-1:0];

    //----------------------------------------------------------------
    // write address pointer
    // 
    // All registers are positive edge triggered with asynchronous
    // active low reset.
    //----------------------------------------------------------------

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            wr_addr_ff <= 0;
        else if (we)
            wr_addr_ff <=  wr_addr;
        else
            wr_addr_ff <= wr_addr_ff;
    end

    always_comb begin
        if (!fifo_full & we)
            wr_addr = wr_addr + 1;
        else
            wr_addr = wr_addr_ff;
    end

    //----------------------------------------------------------------
    // Read address pointer
    // 
    // All registers are positive edge triggered with asynchronous
    // active low reset.
    //----------------------------------------------------------------

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            rd_addr_ff <= 0;
        else if (rd)
            rd_addr_ff <=  rd_addr;
        else
            rd_addr_ff <= rd_addr_ff;
    end

    always_comb begin
        if (!fifo_empty & rd)
            rd_addr = rd_addr + 1;
        else
            rd_addr = rd_addr_ff;
    end

    //----------------------------------------------------------------
    // Set full and empty control signal
    //----------------------------------------------------------------

    logic [RAM_ADDR_WIDTH-1:0] fifo_count, fifo_count_ff;

    always_comb begin
        unique casez ({rd, wr})
            2'b00 : fifo_count = fifo_count_ff;
            2'b01 : fifo_count = (fifo_count_ff == RAM_DEPTH-1) ? RAM_DEPTH
                                : (fifo_count_ff + 1);
            2'b10 : fifo_count = (fifo_count_ff == 0) ? 0
                                : (fifo_count_ff - 1);
            2'b11 : fifo_count = fifo_count_ff;
        endcase
    end

    always_ff @(posedge clk or negedge reset) begin
        if(!reset_n)
            fifo_count_ff <= 0;
        else
            fifo_count_ff <= fifo_count;
    end

    assign fifo_full  = (fifo_count == RAM_DEPTH-1);
    assign fifo_empty = (fifo_count == 0);

    //----------------------------------------------------------------
    // handle fifo ram based on write/read address pointers
    //----------------------------------------------------------------

    always @(posedge clk)begin
        if (!fifo_full & we)
            ram[wr_addr_ff] = write_data;
    end

    always @(posedge clk)begin
        if (!fifo_empty & rd)
            read_data = ram[rd_addr_ff];
    end

endmodule