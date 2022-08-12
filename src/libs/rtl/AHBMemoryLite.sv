module AHBMemoryLite #(
  parameter MEM_DEPTH = 2048, 					// SIZE = 8192 Bytes = 2048 Words
  parameter AHB_ADDR_WIDTH  = 32,
  parameter AHB_DATA_WIDTH  = 32
)(
 	input logic HCLK,
	input logic HRESETn,
  input logic HSEL,
  input logic [AHB_ADDR_WIDTH-1:0] HADDR,
	input logic [AHB_DATA_WIDTH-1:0] HWDATA,
	input logic HWRITE,
	input logic [2:0] HSIZE,
	input logic [2:0] HBURST,
	input logic [3:0] HPROT,
	input logic [1:0] HTRANS,
	input logic HMASTLOCK,
	input logic HREADY,

  output logic  [AHB_DATA_WIDTH-1:0] HRDATA,
	output logic  HREADYOUT,
	output logic  HRESP
);
  localparam  BIT_WIDTH_ADDR = $clog2(MEM_DEPTH);

  logic [BIT_WIDTH_ADDR-1:0]  address_sram;
  logic [1:0] byte_select;
  logic [2:0] reg_size;
  logic [3:0] mask_sram;
  logic write_en;
  logic read_en;

  always @ (posedge HCLK)
  begin
    if (HRESETn == 1'b0) begin
      address_sram  <=  '0;
      mask_sram     <=  '0;
      reg_size      <=  '0;
      write_en      <=  '0;
      read_en       <=  '0;
      byte_select   <=  '0;
      HRESP         <=  '0;
      HREADYOUT     <=  '0;
    end
    else begin
      if (HSEL) begin
        HREADYOUT     <=  1'b1;
        HRESP         <=  1'b0;
        address_sram  <=  HADDR[BIT_WIDTH_ADDR-1:2];
        byte_select   <=  HADDR[1:0];
        reg_size      <=  HSIZE;
        write_en      <=  HWRITE;
        read_en       <=  ~HWRITE;
      end else begin
        write_en      <=  '0;
        read_en       <=  '0;
      end
    end
  end

  // Defines which bytes we should set in the memory
  // with a bitmask
  always @ (*)
  begin
    case (reg_size)
      3'b000:
        case(byte_select)
          2'b00:  mask_sram = 4'b0001;
          2'b01:  mask_sram = 4'b0010;
          2'b10:  mask_sram = 4'b0100;
          2'b11:  mask_sram = 4'b1000;
          default:  mask_sram = 4'b1111;
        endcase
      3'b001: mask_sram = 4'b0011;
      3'b010: mask_sram = 4'b1111;
      default:mask_sram = 4'b1111;
    endcase
  end

  mem_sram #(
    .MEM_DEPTH(MEM_DEPTH),
    .DATA_WIDTH(AHB_DATA_WIDTH)
  )
  sram(
    .clk(HCLK),
    .reset_n(HRESETn),
    .write_en(write_en),
    .read_en(read_en),
    .mask(mask_sram),
    .address(address_sram),
    .write_data(HWDATA),
    .read_data(HRDATA)
  );
endmodule
