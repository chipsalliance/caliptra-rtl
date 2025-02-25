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

module ahb_slv_sif 
  import ahb_defines_pkg::*; 
  #(
    parameter AHB_DATA_WIDTH = 64
   ,parameter CLIENT_DATA_WIDTH = 32
   ,parameter AHB_ADDR_WIDTH = 32
   ,parameter CLIENT_ADDR_WIDTH = AHB_ADDR_WIDTH

   )
   (
    //AMBA AHB Lite INF
    input logic hclk,
    input logic hreset_n,
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

    //COMPONENT INF
    output logic                         dv,
    input  logic                         hld,
    input  logic                         err,
    output logic                         write,
    output logic [CLIENT_DATA_WIDTH-1:0] wdata,
    output logic [CLIENT_ADDR_WIDTH-1:0] addr,

    input  logic [CLIENT_DATA_WIDTH-1:0] rdata
   );

logic err_f;
logic [2:0] size;

localparam BITS_WDATA = $bits(wdata);

//support bus widths:
//64b ahb, 32b client
//64b ahb, 64b client
generate 
    if ((AHB_DATA_WIDTH == 32) & (CLIENT_DATA_WIDTH == 32)) begin
        always_comb begin
            unique case (size) inside
                3'b000:  //byte
                    //wdata = {{$bits(wdata)-8{1'b0}},hwdata_i[7:0]};
                    wdata = {{BITS_WDATA-8{1'b0}},hwdata_i[7:0]};
                3'b001:  //halfword
                    //wdata = {{$bits(wdata)-16{1'b0}},hwdata_i[15:0]};
                    wdata = {{BITS_WDATA-16{1'b0}},hwdata_i[15:0]};
                3'b010:  //word
                    wdata = hwdata_i[31:0];
                default: //word
                wdata = hwdata_i[31:0];
            endcase
        end
        always_comb hrdata_o = rdata;
    end else if ((AHB_DATA_WIDTH == 64) & (CLIENT_DATA_WIDTH == 32)) begin
        always_comb begin
            unique case (size) inside
                3'b000:  //byte
                    //wdata = addr[2] ? {{$bits(wdata)-8{1'b0}},hwdata_i[39:32]} : {{$bits(wdata)-8{1'b0}},hwdata_i[7:0]};
                    wdata = addr[2] ? {{BITS_WDATA-8{1'b0}},hwdata_i[39:32]} : {{BITS_WDATA-8{1'b0}},hwdata_i[7:0]};
                3'b001:  //halfword
                    //wdata = addr[2] ? {{$bits(wdata)-16{1'b0}},hwdata_i[47:32]} : {{$bits(wdata)-16{1'b0}},hwdata_i[15:0]};
                    wdata = addr[2] ? {{BITS_WDATA-16{1'b0}},hwdata_i[47:32]} : {{BITS_WDATA-16{1'b0}},hwdata_i[15:0]};
                3'b010:  //word
                    wdata = addr[2] ? hwdata_i[63:32] : hwdata_i[31:0];
                default: //word
                wdata = addr[2] ? hwdata_i[63:32] : hwdata_i[31:0];
            endcase
        end
        always_comb hrdata_o = addr[2] ? {rdata, 32'b0} : {32'b0, rdata};
    end else if ((AHB_DATA_WIDTH == 64) & (CLIENT_DATA_WIDTH == 64)) begin
        always_comb begin
            unique case (size) inside
                3'b000:  //byte
                    //wdata = {{$bits(wdata)-8{1'b0}},hwdata_i[7:0]};
                    wdata = {{BITS_WDATA-8{1'b0}},hwdata_i[7:0]};
                3'b001:  //halfword
                    //wdata = {{$bits(wdata)-16{1'b0}},hwdata_i[15:0]};
                    wdata = {{BITS_WDATA-16{1'b0}},hwdata_i[15:0]};
                3'b010:  //word
                    wdata = addr[2]? hwdata_i[63:32] : hwdata_i[31:0];
                3'b011: //dword
                    wdata = hwdata_i;
                default: //dword
                    wdata = hwdata_i;
            endcase
        end
        always_comb hrdata_o = rdata;
    end 

endgenerate

    always_ff @(posedge hclk or negedge hreset_n) begin
        if(!hreset_n) begin
            dv <= 1'b0;
            write <= 1'b0;
            addr <= '0;
            err_f <= '0;
            size <= '0;
        end
        else begin
            err_f <= err;
            if (hready_i) begin
                dv <= hsel_i & htrans_i inside {2'b10, 2'b11};
            end
            // Clear dv as soon as the component responds
            // (in case of error, hready_i will still be 0 due to hreadyout_o == 0)
            else if (dv && !hld) begin
                dv <= 1'b0;
            end
            if(hready_i & hsel_i) begin
                addr <= haddr_i[CLIENT_ADDR_WIDTH-1:0];
                write <= hwrite_i & |htrans_i;
                size <= hsize_i;
            end
        end
    end

always_comb begin : response_block
    hreadyout_o = 1'b1;
    hresp_o = H_OKAY;
    //first err cycle, de-assert ready and drive err
    if (err & ~err_f) begin
        hreadyout_o = 1'b0;
        hresp_o = H_ERROR;
    end else if (dv & hld) begin
        hreadyout_o = 1'b0;
        hresp_o = H_OKAY;
    end else if (err_f) begin
        hreadyout_o = 1'b1;
        hresp_o = H_ERROR;
    end
end

//Coverage
`ifndef VERILATOR
`ifdef FCOV

covergroup ahb_slv_sif_cov_grp @(posedge hclk);
    option.per_instance = 1;

    ahb_read_cp: coverpoint (dv & ~write) {option.comment = "AHB read transaction";}
    ahb_write_cp: coverpoint (dv & write) {option.comment = "AHB write transaction";}
endgroup

ahb_slv_sif_cov_grp ahb_slv_sif_cov_grp1 = new();

`endif
`endif

endmodule
