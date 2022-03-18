`include "cfg.sv"

module integration_top(
  input clk,
  input rst_n
  //AHB_BUS.Master ahb_master
);

/*
  assign s_smaster.haddr = ahb_master.haddr;
  assign s_smaster.hwdata = ahb_master.hwdata;
  assign s_smaster.hsel = ahb_master.hsel;
  assign s_smaster.hwrite = ahb_master.hwrite;
  assign s_smaster.hsize = ahb_master.hsize;
  assign s_smaster.hburst = ahb_master.hburst;
  assign s_smaster.hprot = ahb_master.hprot;
  assign s_smaster.htrans = ahb_master.htrans;
  assign s_smaster.hmastlock = ahb_master.hmastlock;
  assign s_smaster.hreadyout = ahb_master.hreadyout;
  assign ahb_master.hresp = s_smaster.hresp;
  assign ahb_master.hrdata = s_smaster.hrdata;
  assign ahb_master.ready = s_smaster.ready;
*/

  AHB_BUS #(
    .AHB_ADDR_WIDTH(`AHB_HADDR_SIZE),
    .AHB_DATA_WIDTH(`AHB_HDATA_SIZE)
  )
  s_slave[`AHB_SLAVES_NUM-1:0]();

  AHB_BUS #(
    .AHB_ADDR_WIDTH(`AHB_HADDR_SIZE),
    .AHB_DATA_WIDTH(`AHB_HDATA_SIZE)
  )
  s_smaster();

  //********************************************************
  //**************** AHB BUS *******************************
  //********************************************************
  ahb_node_wrap #(
    .NB_SLAVES      ( `AHB_SLAVES_NUM ),
    .AHB_ADDR_WIDTH ( `AHB_HADDR_SIZE ),
    .AHB_DATA_WIDTH ( `AHB_HDATA_SIZE ),
    .BYPASS_HSEL    (               0 ) // If you change to '1' it'll route the HSEL signal to the slave according to master change's
  )
  ahb_node_wrap_i (
    .ahb_slaves   ( s_slave           ),
    .ahb_master   ( s_smaster         ),
    .start_addr_i ( `SLAVE_BASE_ADDR  ),
    .end_addr_i   ( `SLAVE_MASK_ADDR  )
  );

  AHBMemoryLite #(
    .MEM_DEPTH(2000), 					// SIZE = 8KB = 2000 Words
    .AHB_DATA_WIDTH(`AHB_HDATA_SIZE),
    .AHB_ADDR_WIDTH(`AHB_HADDR_SIZE)
  )
  sram_1 (
    .HCLK(clk),
    .HRESETn(rst_n),
    .HSEL(s_slave[0].hsel),
    .HADDR(s_slave[0].haddr),
    .HWDATA(s_slave[0].hwdata),
    .HWRITE(s_slave[0].hwrite),
    .HSIZE(s_slave[0].hsize),
    .HBURST(s_slave[0].hburst),
    .HPROT(s_slave[0].hprot),
    .HTRANS(s_slave[0].htrans),
    .HMASTLOCK(s_slave[0].hmastlock),
    .HREADY(s_slave[0].hready),
    .HRDATA(s_slave[0].hrdata),
    .HREADYOUT(s_slave[0].hreadyout),
    .HRESP(s_slave[0].hresp)
  );

  AHBMemoryLite #(
    .MEM_DEPTH(2000), 					// SIZE = 8KB = 2000 Words
    .AHB_DATA_WIDTH(`AHB_HDATA_SIZE),
    .AHB_ADDR_WIDTH(`AHB_HADDR_SIZE)
  )
  sram_2 (
    .HCLK(clk),
    .HRESETn(rst_n),
    .HSEL(s_slave[1].hsel),
    .HADDR(s_slave[1].haddr),
    .HWDATA(s_slave[1].hwdata),
    .HWRITE(s_slave[1].hwrite),
    .HSIZE(s_slave[1].hsize),
    .HBURST(s_slave[1].hburst),
    .HPROT(s_slave[1].hprot),
    .HTRANS(s_slave[1].htrans),
    .HMASTLOCK(s_slave[1].hmastlock),
    .HREADY(s_slave[1].hready),
    .HRDATA(s_slave[1].hrdata),
    .HREADYOUT(s_slave[1].hreadyout),
    .HRESP(s_slave[1].hresp)
  );
endmodule
