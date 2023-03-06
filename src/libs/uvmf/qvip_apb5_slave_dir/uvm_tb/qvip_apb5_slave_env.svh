//
// File: qvip_apb5_slave_env.svh
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
`include "uvm_macros.svh"
class qvip_apb5_slave_env extends uvm_env;
    `uvm_component_utils(qvip_apb5_slave_env)
    qvip_apb5_slave_env_config cfg;
    // Agent handles
    
    apb5_master_0_agent_t apb5_master_0;
    function new
    (
        string name = "qvip_apb5_slave_env",
        uvm_component parent = null
    );
        super.new(name, parent);
    endfunction
    
    extern function void build_phase
    (
        uvm_phase phase
    );
    
endclass: qvip_apb5_slave_env

function void qvip_apb5_slave_env::build_phase
(
    uvm_phase phase
);
    if ( cfg == null )
    begin
        if ( !uvm_config_db #(qvip_apb5_slave_env_config)::get(this, "", "env_config", cfg) )
        begin
            `uvm_error("build_phase", "Unable to find the env config object in the uvm_config_db")
        end
    end
    apb5_master_0 = apb5_master_0_agent_t::type_id::create("apb5_master_0", this );
    apb5_master_0.set_mvc_config(cfg.apb5_master_0_cfg);
    
endfunction: build_phase

