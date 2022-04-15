// ============================================================================= //
// Engineer:       Ânderson Ignacio da Silva - anderson@aignacio.com             //
//                                                                               //
// Design Name:    AHB NODE WRAP                                                 //
// Module Name:    AHB_NODE_WRAP                                                 //
// Project Name:   --                                                            //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:    This component implements a connection of one master to       //
//                 multi slave, through an AHB node                              //
//                                                                               //
// ============================================================================= //

module ahb_node_wrap #(
  parameter NB_SLAVES = 8,
  parameter AHB_DATA_WIDTH = 32,
  parameter AHB_ADDR_WIDTH = 32,
  parameter BYPASS_HSEL = 0
)
(
  // SLAVE PORTS
  AHB_BUS.Slave ahb_slaves[NB_SLAVES-1:0],
  // MASTER PORT
  AHB_BUS.Master  ahb_master,
  // CONFIGURATION PORT
  input  logic [NB_SLAVES-1:0][AHB_ADDR_WIDTH-1:0] start_addr_i,
  input  logic [NB_SLAVES-1:0][AHB_ADDR_WIDTH-1:0] end_addr_i
);
  genvar  i;

  logic [NB_SLAVES-1:0][AHB_ADDR_WIDTH-1:0] haddr;
  logic [NB_SLAVES-1:0][AHB_DATA_WIDTH-1:0] hwdata;
  logic [NB_SLAVES-1:0] hsel;
  logic [NB_SLAVES-1:0] hwrite;
  logic [NB_SLAVES-1:0] hready;
  logic [NB_SLAVES-1:0][1:0] htrans;
  logic [NB_SLAVES-1:0][3:0] hprot;
  logic [NB_SLAVES-1:0][2:0] hburst;
  logic [NB_SLAVES-1:0][2:0] hsize;
  logic [NB_SLAVES-1:0] hresp;
  logic [NB_SLAVES-1:0] hreadyout;
  logic [NB_SLAVES-1:0] hmastlock;
  logic [NB_SLAVES-1:0][AHB_DATA_WIDTH-1:0] hrdata;

  // GENERATE SEL SIGNAL FOR SLAVE MATCHING THE ADDRESS
  generate
    for(i=0;i<NB_SLAVES;i++)  begin
      assign ahb_slaves[i].haddr = haddr[i];
      assign ahb_slaves[i].hwdata = hwdata[i];
      assign ahb_slaves[i].hsel = hsel[i];
      assign ahb_slaves[i].hwrite = hwrite[i];
      assign ahb_slaves[i].hsize = hsize[i];
      assign ahb_slaves[i].hburst = hburst[i];
      assign ahb_slaves[i].hprot = hprot[i];
      assign ahb_slaves[i].htrans = htrans[i];
      assign ahb_slaves[i].hmastlock = hmastlock[i];
      assign ahb_slaves[i].hready = hready[i];

      assign hresp[i] = ahb_slaves[i].hresp;
      assign hrdata[i] = ahb_slaves[i].hrdata;
      assign hreadyout[i] = ahb_slaves[i].hreadyout;
    end
  endgenerate


  ahb_node #(
    .NB_SLAVES(NB_SLAVES),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .BYPASS_HSEL(BYPASS_HSEL)
  ) ahb_node_u1
  (
    // to SLAVES PORT
    .haddr_o(haddr),
    .hwdata_o(hwdata),
    .hsel_o(hsel),
    .hwrite_o(hwrite),
    .hmastlock_o(hmastlock),
    .hslaveready_o(hready),
    .htrans_o(htrans),
    .hprot_o(hprot),
    .hburst_o(hburst),
    .hsize_o(hsize),
    .hresp_i(hresp),
    .hreadyout_i(hreadyout),
    .hrdata_i(hrdata),

    // from SINGLE MASTER PORT
    .haddr_i(ahb_master.haddr),
    .hwdata_i(ahb_master.hwdata),
    .hsel_i(ahb_master.hsel),
    .hwrite_i(ahb_master.hwrite),
    .hmastlock_i(ahb_master.hmastlock),
    .htrans_i(ahb_master.htrans),
    .hprot_i(ahb_master.hprot),
    .hburst_i(ahb_master.hburst),
    .hsize_i(ahb_master.hsize),
    .hresp_o(ahb_master.hresp),
    .hmasterready_o(ahb_master.hready),
    .hrdata_o(ahb_master.hrdata),

    // CONFIGURATION PORT
    .START_ADDR_i(start_addr_i),
    .END_ADDR_i(end_addr_i)
  );
endmodule
