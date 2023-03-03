//
// File: qvip_apb5_slave_params_pkg.sv
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
package qvip_apb5_slave_params_pkg;
    import addr_map_pkg::*;
    //
    // Import the necessary QVIP packages:
    //
    import mgc_apb3_v1_0_pkg::*;
    class apb5_master_0_params;
        localparam int APB3_SLAVE_COUNT      = 1;
        localparam int APB3_PADDR_BIT_WIDTH  = 32;
        localparam int APB3_PWDATA_BIT_WIDTH = 32;
        localparam int APB3_PRDATA_BIT_WIDTH = 32;
        localparam int PAUSER_WIDTH          = 32;
        localparam int PWUSER_WIDTH          = 4;
        localparam int PRUSER_WIDTH          = 4;
        localparam int PBUSER_WIDTH          = 4;
    endclass: apb5_master_0_params
    
    typedef apb3_vip_config #(apb5_master_0_params::APB3_SLAVE_COUNT,apb5_master_0_params::APB3_PADDR_BIT_WIDTH,apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb5_master_0_cfg_t;
    
    typedef apb_agent #(apb5_master_0_params::APB3_SLAVE_COUNT,apb5_master_0_params::APB3_PADDR_BIT_WIDTH,apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb5_master_0_agent_t;
    
    typedef virtual mgc_apb3 #(apb5_master_0_params::APB3_SLAVE_COUNT,apb5_master_0_params::APB3_PADDR_BIT_WIDTH,apb5_master_0_params::APB3_PWDATA_BIT_WIDTH,apb5_master_0_params::APB3_PRDATA_BIT_WIDTH) apb5_master_0_bfm_t;
    
    //
    // `includes for the config policy classes:
    //
    `include "apb5_master_0_config_policy.svh"
endpackage: qvip_apb5_slave_params_pkg
