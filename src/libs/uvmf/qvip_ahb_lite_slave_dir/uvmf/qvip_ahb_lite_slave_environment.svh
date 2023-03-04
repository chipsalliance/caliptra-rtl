//
// File: qvip_ahb_lite_slave_environment.svh
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
`include "uvm_macros.svh"
class qvip_ahb_lite_slave_environment
#(
    string UNIQUE_ID = ""
) extends uvmf_environment_base #(.CONFIG_T(qvip_ahb_lite_slave_env_configuration));
    `uvm_component_param_utils(qvip_ahb_lite_slave_environment #(UNIQUE_ID))
    // Agent handles
    
    ahb_lite_slave_0_agent_t ahb_lite_slave_0;
    function new
    (
        string name = "qvip_ahb_lite_slave_environment",
        uvm_component parent = null
    );
        super.new(name, parent);
    endfunction
    
    extern function void build_phase
    (
        uvm_phase phase
    );
    
    extern function void connect_phase
    (
        uvm_phase phase
    );
    
endclass: qvip_ahb_lite_slave_environment

function void qvip_ahb_lite_slave_environment::build_phase
(
    uvm_phase phase
);
    ahb_lite_slave_0 = ahb_lite_slave_0_agent_t::type_id::create("ahb_lite_slave_0", this );
    ahb_lite_slave_0.set_mvc_config(configuration.ahb_lite_slave_0_cfg);
    
endfunction: build_phase

function void qvip_ahb_lite_slave_environment::connect_phase
(
    uvm_phase phase
);
    uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,{UNIQUE_ID,"ahb_lite_slave_0"},ahb_lite_slave_0.m_sequencer);
endfunction: connect_phase

