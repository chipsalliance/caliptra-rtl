module mem_sram #(
  parameter MEM_DEPTH = 2048, 					// SIZE = 8192 Bytes = 2048 Words
  parameter DATA_WIDTH  = 32
)(
 	input clk,
  input reset_n,
  input write_en,
  input read_en,
  input [3:0] mask,
  input [$clog2(MEM_DEPTH)-1:0] address,
  input [DATA_WIDTH-1:0]  write_data,
  output  reg [DATA_WIDTH-1:0]  read_data
);
  localparam  BIT_WIDTH_ADDR = $clog2(MEM_DEPTH);

  logic [7:0]  sram  [MEM_DEPTH-1:0] [DATA_WIDTH/8-1:0];

  genvar byt;
  generate
    for (byt=0;byt<DATA_WIDTH/8;byt++) begin
      always @ (*)
      begin
        if (read_en) begin
          read_data[8*byt+:byt] = sram[address][byt];
        end else
        begin
          read_data[8*byt+:byt] = '0;
        end
      end
    end // for
  endgenerate

  always @ (posedge clk)
  begin
    if (write_en) begin
      if (mask[3]) sram[address][31:24] <= write_data[31:24];
      if (mask[2]) sram[address][23:16] <= write_data[23:16];
      if (mask[1]) sram[address][15:8]  <= write_data[15:8];
      if (mask[0]) sram[address][7:0]   <= write_data[7:0];
    end
  end

  `ifdef SIMULATION
  initial begin
    integer i;
    reg [DATA_WIDTH-1:0]  temp  [MEM_DEPTH-1:0];
    $readmemh(`PROG_TEST, temp);
    for (int i=0; i<MEM_DEPTH; i++) begin
      if (^temp[i] === 1'bx) begin
        sram[i] = 32'd0;
      end else begin
        sram[i] = temp[i];
        $display ("Memory AHB lite: mem[%D] = %H",i,sram[i]);
      end
    end
  end
  `endif
endmodule
