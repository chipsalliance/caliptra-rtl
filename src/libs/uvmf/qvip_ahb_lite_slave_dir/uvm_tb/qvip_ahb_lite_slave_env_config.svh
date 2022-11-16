//
// File: qvip_ahb_lite_slave_env_config.svh
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
class qvip_ahb_lite_slave_env_config extends uvm_object;
    `uvm_object_utils(qvip_ahb_lite_slave_env_config)
    // Handles for vip config for each of the QVIP instances
    
    ahb_lite_slave_0_cfg_t ahb_lite_slave_0_cfg;
    // Handles for address maps
    
    address_map MBOX;
    
    function new
    (
        string name = "qvip_ahb_lite_slave_env_config"
    );
        super.new(name);
    endfunction
    
    extern function void initialize;
    
endclass: qvip_ahb_lite_slave_env_config

function void qvip_ahb_lite_slave_env_config::initialize;
    begin
        addr_map_entry_s addr_map_entries[] = new [3];
        addr_map_entries = '{
            '{MAP_NORMAL,"MEM",0,MAP_NS,4'h0,64'h30000000,64'h20000,MEM_NORMAL,MAP_NORM_SEC_DATA},
            '{MAP_NORMAL,"CSR",1,MAP_NS,4'h0,64'h30020000,64'h10000,MEM_NORMAL,MAP_NORM_SEC_DATA},
            '{MAP_NORMAL,"REG",2,MAP_NS,4'h0,64'h30030000,64'h10000,MEM_NORMAL,MAP_NORM_SEC_DATA}};
        MBOX = address_map::type_id::create("MBOX_addr_map");
        MBOX.addr_mask = 64'hFFF;
        MBOX.set( addr_map_entries );
    end
endfunction: initialize

