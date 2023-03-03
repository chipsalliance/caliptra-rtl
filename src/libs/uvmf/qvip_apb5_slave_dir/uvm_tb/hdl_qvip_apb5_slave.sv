//
// File: hdl_qvip_apb5_slave.sv
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
//Time resolution of '1ns' will be used (See Makefiles and scripts)
//Time resolution of '1ns' will be used (See Makefiles and scripts)
//Time resolution of '1ns' will be used (See Makefiles and scripts)
//Time resolution of '1ns' will be used (See Makefiles and scripts)
module hdl_qvip_apb5_slave;
    import uvm_pkg::*;
    import qvip_apb5_slave_params_pkg::*;
    wire                                                                                                                                                                         default_clk_gen_CLK;
    wire                                                                                                                                                                         default_reset_gen_RESET;
    wire [apb5_master_0_params::APB3_PADDR_BIT_WIDTH-1:0]                                                                                                                        apb5_master_0_PADDR;
    wire [apb5_master_0_params::APB3_SLAVE_COUNT-1:0]                                                                                                                            apb5_master_0_PSEL;
    wire                                                                                                                                                                         apb5_master_0_PENABLE;
    wire                                                                                                                                                                         apb5_master_0_PWRITE;
    wire [apb5_master_0_params::APB3_PWDATA_BIT_WIDTH-1:0]                                                                                                                       apb5_master_0_PWDATA;
    wire [apb5_master_0_params::APB3_PRDATA_BIT_WIDTH-1:0]                                                                                                                       apb5_master_0_PRDATA;
    wire                                                                                                                                                                         apb5_master_0_PREADY;
    wire                                                                                                                                                                         apb5_master_0_PSLVERR;
    wire [apb5_master_0_params::PAUSER_WIDTH-1:0]                                                                                                                                apb5_master_0_PAUSER;
    wire [apb5_master_0_params::PWUSER_WIDTH-1:0]                                                                                                                                apb5_master_0_PWUSER;
    wire [apb5_master_0_params::PRUSER_WIDTH-1:0]                                                                                                                                apb5_master_0_PRUSER;
    wire [apb5_master_0_params::PBUSER_WIDTH-1:0]                                                                                                                                apb5_master_0_PBUSER;
    wire                                                                                                                                                                         apb5_master_0_PWAKEUP;
    wire [((apb5_master_0_params::APB3_PADDR_BIT_WIDTH+7)/8)-1:0]                                                                                                                apb5_master_0_PADDRCHK;
    wire                                                                                                                                                                         apb5_master_0_PCTRLCHK;
    wire [apb5_master_0_params::APB3_SLAVE_COUNT-1:0]                                                                                                                            apb5_master_0_PSELxCHK;
    wire                                                                                                                                                                         apb5_master_0_PENABLECHK;
    wire [(((apb5_master_0_params::APB3_PWDATA_BIT_WIDTH+7)/8)-1):0]                                                                                                             apb5_master_0_PWDATACHK;
    wire [(((apb5_master_0_params::APB3_PWDATA_BIT_WIDTH/8)+7)/8)-1:0]                                                                                                           apb5_master_0_PSTRBCHK;
    wire                                                                                                                                                                         apb5_master_0_PWAKEUPCHK;
    wire [(((apb5_master_0_params::PAUSER_WIDTH+7)/8)-1):0]                                                                                                                      apb5_master_0_PAUSERCHK;
    wire [(((apb5_master_0_params::PWUSER_WIDTH+7)/8)-1):0]                                                                                                                      apb5_master_0_PWUSERCHK;
    wire                                                                                                                                                                         apb5_master_0_PREADYCHK;
    wire [(((apb5_master_0_params::APB3_PRDATA_BIT_WIDTH+7)/8)-1):0]                                                                                                             apb5_master_0_PRDATACHK;
    wire                                                                                                                                                                         apb5_master_0_PSLVERRCHK;
    wire [(((apb5_master_0_params::PRUSER_WIDTH+7)/8)-1):0]                                                                                                                      apb5_master_0_PRUSERCHK;
    wire [(((apb5_master_0_params::PBUSER_WIDTH+7)/8)-1):0]                                                                                                                      apb5_master_0_PBUSERCHK;
    
    apb5_master 
    #(
        .SLAVE_COUNT(apb5_master_0_params::APB3_SLAVE_COUNT),
        .ADDR_WIDTH(apb5_master_0_params::APB3_PADDR_BIT_WIDTH),
        .WDATA_WIDTH(apb5_master_0_params::APB3_PWDATA_BIT_WIDTH),
        .RDATA_WIDTH(apb5_master_0_params::APB3_PRDATA_BIT_WIDTH),
        .PAUSER_WIDTH(apb5_master_0_params::PAUSER_WIDTH),
        .PWUSER_WIDTH(apb5_master_0_params::PWUSER_WIDTH),
        .PRUSER_WIDTH(apb5_master_0_params::PRUSER_WIDTH),
        .PBUSER_WIDTH(apb5_master_0_params::PBUSER_WIDTH),
        .IF_NAME("apb5_master_0"),
        .PATH_NAME("uvm_test_top")
    )
    apb5_master_0
    (
        .PCLK(default_clk_gen_CLK),
        .PRESETn(default_reset_gen_RESET),
        .PADDR(apb5_master_0_PADDR),
        .PSEL(apb5_master_0_PSEL),
        .PENABLE(apb5_master_0_PENABLE),
        .PWRITE(apb5_master_0_PWRITE),
        .PWDATA(apb5_master_0_PWDATA),
        .PRDATA(apb5_master_0_PRDATA),
        .PREADY(apb5_master_0_PREADY),
        .PSLVERR(apb5_master_0_PSLVERR),
        .PPROT(),
        .PSTRB(),
        .PAUSER(apb5_master_0_PAUSER),
        .PWUSER(apb5_master_0_PWUSER),
        .PRUSER(apb5_master_0_PRUSER),
        .PBUSER(apb5_master_0_PBUSER),
        .PWAKEUP(apb5_master_0_PWAKEUP),
        .PADDRCHK(apb5_master_0_PADDRCHK),
        .PCTRLCHK(apb5_master_0_PCTRLCHK),
        .PSELxCHK(apb5_master_0_PSELxCHK),
        .PENABLECHK(apb5_master_0_PENABLECHK),
        .PWDATACHK(apb5_master_0_PWDATACHK),
        .PSTRBCHK(apb5_master_0_PSTRBCHK),
        .PWAKEUPCHK(apb5_master_0_PWAKEUPCHK),
        .PAUSERCHK(apb5_master_0_PAUSERCHK),
        .PWUSERCHK(apb5_master_0_PWUSERCHK),
        .PREADYCHK(apb5_master_0_PREADYCHK),
        .PRDATACHK(apb5_master_0_PRDATACHK),
        .PSLVERRCHK(apb5_master_0_PSLVERRCHK),
        .PRUSERCHK(apb5_master_0_PRUSERCHK),
        .PBUSERCHK(apb5_master_0_PBUSERCHK)
    );
    default_clk_gen default_clk_gen
    (
        .CLK(default_clk_gen_CLK)
    );
    default_reset_gen default_reset_gen
    (
        .RESET(default_reset_gen_RESET),
        .CLK_IN(default_clk_gen_CLK)
    );

endmodule: hdl_qvip_apb5_slave
