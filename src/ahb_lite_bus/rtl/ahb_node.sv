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
  genvar  i;
  integer loop_1,
          loop_2,
          loop_3,
          loop_4,
          loop_5,
          loop_6,
          loop_7,
          loop_8,
          loop_9,
          loop_10,
          loop_11,
          loop_12;

  generate
    for(i=0;i<NB_SLAVES;i++) begin
      assign hsel_o[i]  = (BYPASS_HSEL === 1 ? hsel_i && (haddr_i >= START_ADDR_i[i]) && (haddr_i <= END_ADDR_i[i]) : (haddr_i >= START_ADDR_i[i]) && (haddr_i <= END_ADDR_i[i]));
    end
  endgenerate

  // HREADY SLAVE GENERATION
  // If slave selected, route slave HREADYOUT to the SLAVE HREADY input
  always_comb begin
    for ( loop_1 = 0; loop_1 < NB_SLAVES; loop_1++ ) begin
      if( hsel_o[loop_1] == 1'b1 ) begin
        hslaveready_o[loop_1] = hreadyout_i;
      end
      else  begin
        hslaveready_o[loop_1] = 1'b1;
      end
    end
  end

  // HWRITE SLAVE GENERATION
  // If slave selected, route master HWRITE to the SLAVE HWRITE input
  always_comb begin
    for ( loop_2 = 0; loop_2 < NB_SLAVES; loop_2++ ) begin
      if( hsel_o[loop_2] == 1'b1 ) begin
        hwrite_o[loop_2] = hwrite_i;
      end
      else  begin
        hwrite_o[loop_2] = 1'b0;
      end
    end
  end

  // HMASTLOCK SLAVE GENERATION
  // If slave selected, route master HMASTLOCK to the SLAVE HMASTLOCK input
  always_comb begin
    for ( loop_3 = 0; loop_3 < NB_SLAVES; loop_3++ ) begin
      if( hsel_o[loop_3] == 1'b1 ) begin
        hmastlock_o[loop_3] = hmastlock_i;
      end
      else  begin
        hmastlock_o[loop_3] = 1'b0;
      end
    end
  end

  // HTRANS SLAVE GENERATION
  // If slave selected, route master HTRANS to the SLAVE HTRANS input
  always_comb begin
    for ( loop_4 = 0; loop_4 < NB_SLAVES; loop_4++ ) begin
      if( hsel_o[loop_4] == 1'b1 ) begin
        htrans_o[loop_4] = htrans_i;
      end
      else  begin
        htrans_o[loop_4] =  2'b00;
      end
    end
  end

  // HPROT SLAVE GENERATION
  // If slave selected, route master HPROT to the SLAVE HPROT input
  always_comb begin
    for ( loop_5 = 0; loop_5 < NB_SLAVES; loop_5++ ) begin
      if( hsel_o[loop_5] == 1'b1 ) begin
        hprot_o[loop_5] = hprot_i;
      end
      else  begin
        hprot_o[loop_5] = 4'b0000;
      end
    end
  end

  // HBURST SLAVE GENERATION
  // If slave selected, route master HBURST to the SLAVE HBURST input
  always_comb begin
    for ( loop_6 = 0; loop_6 < NB_SLAVES; loop_6++ ) begin
      if( hsel_o[loop_6] == 1'b1 ) begin
        hburst_o[loop_6] = hburst_i;
      end
      else  begin
        hburst_o[loop_6] = 3'b000;
      end
    end
  end

  // HSIZE SLAVE GENERATION
  // If slave selected, route master HSIZE to the SLAVE HSIZE input
  always_comb begin
    for ( loop_7 = 0; loop_7 < NB_SLAVES; loop_7++ ) begin
      if( hsel_o[loop_7] == 1'b1 ) begin
        hsize_o[loop_7] = hsize_i;
      end
      else  begin
        hsize_o[loop_7] = 3'b000;
      end
    end
  end

  // HADDR SLAVE GENERATION
  // If slave selected, route master HADDR to the SLAVE HADDR input
  always_comb begin
    for ( loop_8 = 0; loop_8 < NB_SLAVES; loop_8++ ) begin
      if( hsel_o[loop_8] == 1'b1 ) begin
        haddr_o[loop_8] = haddr_i;
      end
      else  begin
        haddr_o[loop_8] = {AHB_ADDR_WIDTH{1'b0}};
      end
    end
  end

  // HWDATA SLAVE GENERATION
  // If slave selected, route master HWDATA to the SLAVE HWDATA input
  always_comb begin
    for ( loop_9 = 0; loop_9 < NB_SLAVES; loop_9++ ) begin
      if( hsel_o[loop_9] == 1'b1 ) begin
        hwdata_o[loop_9] = hwdata_i;
      end
      else begin
        hwdata_o[loop_9] = {AHB_DATA_WIDTH{1'b0}};
      end
    end
  end

  // HRDATA MASTER GENERATION
  // If slave selected, route slave HRDATA to the MASTER HRDATA input
  // Pay attention to use this always descrip. with output attribution
  // first THEN output changing according to for loop if/else approach
  // makes simulator interpret wrong the sys. verilog construction
  always_comb begin
    hrdata_o = {AHB_DATA_WIDTH{1'b0}};
    for ( loop_10 = 0; loop_10 < NB_SLAVES; loop_10++ ) begin
      if( hsel_o[loop_10] == 1'b1 ) begin
        hrdata_o = hrdata_i[loop_10];
      end
    end
  end

  // HRESP MASTER GENERATION
  // If slave selected, route slave HRESP to the MASTER HRESP input
  always_comb begin
    hresp_o = 1'b0;
    for ( loop_11 = 0; loop_11 < NB_SLAVES; loop_11++ ) begin
      if( hsel_o[loop_11] == 1'b1 ) begin
        hresp_o = hresp_i[loop_11];
      end
    end
  end

  // HREADY MASTER GENERATION
  // If slave selected, route slave HREADYOUT to the MASTER HREADYOUT input
  always_comb begin
    hmasterready_o = 1'b1;
    for ( loop_12 = 0; loop_12 < NB_SLAVES; loop_12++ ) begin
      if( hsel_o[loop_12] == 1'b1 ) begin
        hmasterready_o = hreadyout_i[loop_12];
      end
    end
  end
endmodule
