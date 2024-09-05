//
// File: qvip_ahb_lite_slave_params_pkg.sv
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
package qvip_ahb_lite_slave_params_pkg;
    import addr_map_pkg::*;
    //
    // Import the necessary QVIP packages:
    //
    import mgc_ahb_v2_0_pkg::*;
    import mgc_ahb_seq_pkg::*;
    class ahb_lite_slave_0_params;
        localparam int AHB_NUM_MASTERS     = 1;
        localparam int AHB_NUM_MASTER_BITS = 1;
        localparam int AHB_NUM_SLAVES      = 1;
        localparam int AHB_ADDRESS_WIDTH   = 32;
        localparam int AHB_WDATA_WIDTH     = 32;//64;
        localparam int AHB_RDATA_WIDTH     = 32;//64;
    endclass: ahb_lite_slave_0_params
    
    typedef ahb_vip_config #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,ahb_lite_slave_0_params::AHB_NUM_SLAVES,ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,ahb_lite_slave_0_params::AHB_WDATA_WIDTH,ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_lite_slave_0_cfg_t;
    
    typedef ahb_agent #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,ahb_lite_slave_0_params::AHB_NUM_SLAVES,ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,ahb_lite_slave_0_params::AHB_WDATA_WIDTH,ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_lite_slave_0_agent_t;
    
    typedef virtual mgc_ahb #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,ahb_lite_slave_0_params::AHB_NUM_SLAVES,ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,ahb_lite_slave_0_params::AHB_WDATA_WIDTH,ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_lite_slave_0_bfm_t;
    
    //
    // `includes for the config policy classes:
    //
    `include "ahb_lite_slave_0_config_policy.svh"
endpackage: qvip_ahb_lite_slave_params_pkg
