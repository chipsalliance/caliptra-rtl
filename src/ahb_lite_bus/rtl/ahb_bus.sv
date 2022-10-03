// Microsoft NOTE:
// This file is temporarily used to enable Caliptra functionality.
// This will be replaced by custom RTL before the public release of Caliptra
// ============================================================================= //
// Engineer:       Ânderson Ignacio da Silva - anderson@aignacio.com             //
//                                                                               //
// Design Name:    AHB BUS                                                       //
// Module Name:    AHB_BUS                                                       //
// Project Name:   --                                                            //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:    This component implements set of signal used in the AHB Bus   //
//                                                                               //
// ============================================================================= //

`ifndef AHB_BUS_SV
`define AHB_BUS_SV

interface AHB_BUS
#(
  parameter AHB_ADDR_WIDTH = 32,
  parameter AHB_DATA_WIDTH = 32
);

  logic [AHB_ADDR_WIDTH-1:0]  haddr;
  logic [AHB_DATA_WIDTH-1:0]  hwdata;
  logic [AHB_DATA_WIDTH-1:0]  hrdata;
  logic hsel;
  logic hwrite;
  logic [2:0]  hsize;
  logic [1:0]  htrans;
  logic hready;
  logic hreadyout;
  logic hresp;

  // Master Side - This modport COMES from a single master
  //***************************************
  modport Master
  (
    input haddr,
          hwdata,
          hsel,
          hwrite,
          hsize,
          htrans,
    output  hresp,
            hrdata,
            hready
  );

  // Slave Side - This slave port GOES to a multiple slaves
  //***************************************
  modport Slave
  (
    output  haddr,
            hwdata,
            hsel,
            hwrite,
            hsize,
            htrans,
            hready,
    input hresp,
          hrdata,
          hreadyout
  );

endinterface
`endif
