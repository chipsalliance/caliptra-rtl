//
// File: qvip_ahb_lite_slave_env.svh
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
`include "uvm_macros.svh"
class qvip_ahb_lite_slave_env extends uvm_env;
    `uvm_component_utils(qvip_ahb_lite_slave_env)
    qvip_ahb_lite_slave_env_config cfg;
    // Agent handles
    
    ahb_lite_slave_0_agent_t ahb_lite_slave_0;
    function new
    (
        string name = "qvip_ahb_lite_slave_env",
        uvm_component parent = null
    );
        super.new(name, parent);
    endfunction
    
    extern function void build_phase
    (
        uvm_phase phase
    );
    
endclass: qvip_ahb_lite_slave_env

function void qvip_ahb_lite_slave_env::build_phase
(
    uvm_phase phase
);
    if ( cfg == null )
    begin
        if ( !uvm_config_db #(qvip_ahb_lite_slave_env_config)::get(this, "", "env_config", cfg) )
        begin
            `uvm_error("build_phase", "Unable to find the env config object in the uvm_config_db")
        end
    end
    ahb_lite_slave_0 = ahb_lite_slave_0_agent_t::type_id::create("ahb_lite_slave_0", this );
    ahb_lite_slave_0.set_mvc_config(cfg.ahb_lite_slave_0_cfg);
    
endfunction: build_phase

