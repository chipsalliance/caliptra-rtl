// Microsoft NOTE:
// This file is temporarily used to enable Caliptra functionality.
// This will be replaced by custom RTL before the public release of Caliptra
// ============================================================================= //
// Engineer:       Ânderson Ignacio da Silva - anderson@aignacio.com             //
//                                                                               //
// Design Name:    AHB NODE                                                      //
// Module Name:    AHB_NODE                                                      //
// Project Name:   --                                                            //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:    This component implements a configurable AHB node             //
//                                                                               //
// ============================================================================= //

module ahb_node #(
  parameter NB_SLAVES = 8,
  parameter AHB_DATA_WIDTH = 32,
  parameter AHB_ADDR_WIDTH = 32,
  parameter BYPASS_HSEL = 0
)
(
  input logic hclk,
  input logic hreset_n,
  // to SLAVES PORT
  output logic [NB_SLAVES-1:0][AHB_ADDR_WIDTH-1:0] haddr_o,
  output logic [NB_SLAVES-1:0][AHB_DATA_WIDTH-1:0] hwdata_o,
  output logic [NB_SLAVES-1:0] hsel_o,
  output logic [NB_SLAVES-1:0] hwrite_o,
  output logic [NB_SLAVES-1:0] hmastlock_o,
  output logic [NB_SLAVES-1:0] hslaveready_o,
  output logic [NB_SLAVES-1:0][1:0] htrans_o,
  output logic [NB_SLAVES-1:0][3:0] hprot_o,
  output logic [NB_SLAVES-1:0][2:0] hburst_o,
  output logic [NB_SLAVES-1:0][2:0] hsize_o,

  input logic [NB_SLAVES-1:0] hresp_i,
  input logic [NB_SLAVES-1:0] hreadyout_i,
  input logic [NB_SLAVES-1:0][AHB_DATA_WIDTH-1:0] hrdata_i,

  // from SINGLE MASTER PORT
  input logic [AHB_ADDR_WIDTH-1:0] haddr_i,
  input logic [AHB_DATA_WIDTH-1:0] hwdata_i,
  input logic hsel_i,
  input logic hwrite_i,
  input logic hmastlock_i,
  input logic [1:0] htrans_i,
  input logic [3:0] hprot_i,
  input logic [2:0] hburst_i,
  input logic [2:0] hsize_i,

  output logic hresp_o,
  output logic hmasterready_o,
  output logic [AHB_DATA_WIDTH-1:0] hrdata_o,

  // CONFIGURATION ADDRESS PORT
  input logic [NB_SLAVES-1:0][AHB_ADDR_WIDTH-1:0] START_ADDR_i,
  input logic [NB_SLAVES-1:0][AHB_ADDR_WIDTH-1:0] END_ADDR_i
);
  // ==========================================================================
  logic [NB_SLAVES-1:0] pending_hsel;

  genvar  i;

  generate
    for(i=0;i<NB_SLAVES;i++) begin
      assign hsel_o[i]  = (BYPASS_HSEL == 1 ? hsel_i && (haddr_i >= START_ADDR_i[i]) && (haddr_i <= END_ADDR_i[i]) : (haddr_i >= START_ADDR_i[i]) && (haddr_i <= END_ADDR_i[i]));
    end
  endgenerate

always @(posedge hclk, negedge hreset_n) begin
  if (~hreset_n) pending_hsel <= '0;
  else if (hmasterready_o) pending_hsel <= hsel_o;
end

//drive the address phase
  always_comb begin
    for ( int s = 0; s < NB_SLAVES; s++ ) begin
      if( hsel_i == 1'b1 ) begin
        hslaveready_o[s] = hreadyout_i;
        hwrite_o[s] = hwrite_i;
        hmastlock_o[s] = hmastlock_i;
        htrans_o[s] = htrans_i;
        hprot_o[s] = hprot_i;
        hburst_o[s] = hburst_i;
        hsize_o[s] = hsize_i;
        haddr_o[s] = haddr_i;
        hwdata_o[s] = hwdata_i;
      end
      else  begin
        hslaveready_o[s] = 1'b1;
        hwrite_o[s] = 1'b0;
        hmastlock_o[s] = 1'b0;
        htrans_o[s] =  2'b00;
        hprot_o[s] = 4'b0000;
        hburst_o[s] = 3'b000;
        hsize_o[s] = 3'b000;
        haddr_o[s] = {AHB_ADDR_WIDTH{1'b0}};
        hwdata_o[s] = {AHB_DATA_WIDTH{1'b0}};
      end
    end
  end

//use retimed select to drive response
  always_comb begin
    hrdata_o = {AHB_DATA_WIDTH{1'b0}};
    hmasterready_o = 1'b1;
    hresp_o = 1'b0;
    for (int s = 0; s < NB_SLAVES; s++ ) begin
      if( pending_hsel[s] == 1'b1 ) begin
        hrdata_o = hrdata_i[s];
        hresp_o = hresp_i[s];
        hmasterready_o = hreadyout_i[s];
      end
    end
  end

endmodule
