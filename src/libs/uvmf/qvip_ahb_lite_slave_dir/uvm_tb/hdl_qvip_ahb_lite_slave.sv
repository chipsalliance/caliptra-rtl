//
// File: hdl_qvip_ahb_lite_slave.sv
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
//Time resolution of '1ns' will be used (See Makefiles and scripts)
module hdl_qvip_ahb_lite_slave;
    import uvm_pkg::*;
    import qvip_ahb_lite_slave_params_pkg::*;
    wire                                                                                                                                                                         default_clk_gen_CLK;
    wire                                                                                                                                                                         default_reset_gen_RESET;
    wire [(ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH-1):0]                                                                                                                      ahb_lite_slave_0_HADDR;
    wire [1:0]                                                                                                                                                                   ahb_lite_slave_0_HTRANS;
    wire                                                                                                                                                                         ahb_lite_slave_0_HWRITE;
    wire [2:0]                                                                                                                                                                   ahb_lite_slave_0_HSIZE;
    wire [(ahb_lite_slave_0_params::AHB_WDATA_WIDTH-1):0]                                                                                                                        ahb_lite_slave_0_HWDATA;
    wire [2:0]                                                                                                                                                                   ahb_lite_slave_0_HBURST;
    wire [6:0]                                                                                                                                                                   ahb_lite_slave_0_HPROT;
    wire                                                                                                                                                                         ahb_lite_slave_0_HMASTLOCK;
    wire                                                                                                                                                                         ahb_lite_slave_0_HREADYOUT;
    wire [(ahb_lite_slave_0_params::AHB_RDATA_WIDTH-1):0]                                                                                                                        ahb_lite_slave_0_HRDATA;
    wire                                                                                                                                                                         ahb_lite_slave_0_HREADY;
    wire                                                                                                                                                                         ahb_lite_slave_0_HRESP;
    wire                                                                                                                                                                         ahb_lite_slave_0_HSEL;
    wire                                                                                                                                                                         ahb_lite_slave_0_HNONSEC;
    wire [63:0]                                                                                                                                                                  ahb_lite_slave_0_HAUSER;
    wire [63:0]                                                                                                                                                                  ahb_lite_slave_0_HWUSER;
    wire [63:0]                                                                                                                                                                  ahb_lite_slave_0_HRUSER;
    wire [15:0]                                                                                                                                                                  ahb_lite_slave_0_mult_HSEL;
    wire                                                                                                                                                                         ahb_lite_slave_0_HEXCL;
    wire [15:0]                                                                                                                                                                  ahb_lite_slave_0_HMASTER;
    wire                                                                                                                                                                         ahb_lite_slave_0_HEXOKAY;
    
    mgc_ahb #(.AHB_NUM_MASTERS(ahb_lite_slave_0_params::AHB_NUM_MASTERS),.AHB_NUM_MASTER_BITS(ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS),.AHB_NUM_SLAVES(ahb_lite_slave_0_params::AHB_NUM_SLAVES),.AHB_ADDRESS_WIDTH(ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH),.AHB_WDATA_WIDTH(ahb_lite_slave_0_params::AHB_WDATA_WIDTH),.AHB_RDATA_WIDTH(ahb_lite_slave_0_params::AHB_RDATA_WIDTH))ahb_lite_slave_0_bfm(.iHCLK(default_clk_gen_CLK),.iHRESETn(default_reset_gen_RESET));
    
    ahb_lite_slave 
    #(
        .NUM_MASTERS(ahb_lite_slave_0_params::AHB_NUM_MASTERS),
        .NUM_MASTER_BITS(ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS),
        .NUM_SLAVES(ahb_lite_slave_0_params::AHB_NUM_SLAVES),
        .ADDR_WIDTH(ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH),
        .WDATA_WIDTH(ahb_lite_slave_0_params::AHB_WDATA_WIDTH),
        .RDATA_WIDTH(ahb_lite_slave_0_params::AHB_RDATA_WIDTH),
        .SLAVE_INDEX(0)
    )
    ahb_lite_slave_0
    (
        .ahb_if(ahb_lite_slave_0_bfm),
        .HADDR(ahb_lite_slave_0_HADDR),
        .HTRANS(ahb_lite_slave_0_HTRANS),
        .HWRITE(ahb_lite_slave_0_HWRITE),
        .HSIZE(ahb_lite_slave_0_HSIZE),
        .HWDATA(ahb_lite_slave_0_HWDATA),
        .HBURST(ahb_lite_slave_0_HBURST),
        .HPROT(ahb_lite_slave_0_HPROT),
        .HMASTLOCK(ahb_lite_slave_0_HMASTLOCK),
        .HREADYOUT(ahb_lite_slave_0_HREADYOUT),
        .HRDATA(ahb_lite_slave_0_HRDATA),
        .HREADY(ahb_lite_slave_0_HREADY),
        .HRESP(ahb_lite_slave_0_HRESP),
        .HSEL(ahb_lite_slave_0_HSEL),
        .HNONSEC(ahb_lite_slave_0_HNONSEC),
        .HAUSER(ahb_lite_slave_0_HAUSER),
        .HWUSER(ahb_lite_slave_0_HWUSER),
        .HRUSER(ahb_lite_slave_0_HRUSER),
        .mult_HSEL(ahb_lite_slave_0_mult_HSEL),
        .HEXCL(ahb_lite_slave_0_HEXCL),
        .HMASTER(ahb_lite_slave_0_HMASTER),
        .HEXOKAY(ahb_lite_slave_0_HEXOKAY)
    );
    
    initial
    begin
        uvm_config_db #(ahb_lite_slave_0_bfm_t)::set(null,"uvm_test_top","ahb_lite_slave_0",ahb_lite_slave_0_bfm);
    end
    default_clk_gen default_clk_gen
    (
        .CLK(default_clk_gen_CLK)
    );
    default_reset_gen default_reset_gen
    (
        .RESET(default_reset_gen_RESET),
        .CLK_IN(default_clk_gen_CLK)
    );

endmodule: hdl_qvip_ahb_lite_slave
