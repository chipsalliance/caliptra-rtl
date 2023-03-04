//
// File: qvip_ahb_lite_slave_env_configuration.svh
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
class qvip_ahb_lite_slave_env_configuration extends uvmf_environment_configuration_base;
    `uvm_object_utils(qvip_ahb_lite_slave_env_configuration)
    // Handles for vip config for each of the QVIP instances
    
    ahb_lite_slave_0_cfg_t ahb_lite_slave_0_cfg;
    // Handles for address maps
    
    address_map MBOX;
    
    function new
    (
        string name = "qvip_ahb_lite_slave_env_configuration"
    );
        super.new(name);
        ahb_lite_slave_0_cfg = ahb_lite_slave_0_cfg_t::type_id::create("ahb_lite_slave_0_cfg");
    endfunction
    
    virtual function string convert2string;
        return {"qvip_ahb_lite_slave_env_configuration:",ahb_lite_slave_0_cfg.convert2string()};
    endfunction: convert2string
    
    extern function void initialize
    (
        uvmf_sim_level_t sim_level,
        string environment_path,
        string interface_names[],
        uvm_reg_block register_model = null,
        uvmf_active_passive_t interface_activity[] = {}
    );
    
endclass: qvip_ahb_lite_slave_env_configuration

function void qvip_ahb_lite_slave_env_configuration::initialize
(
    uvmf_sim_level_t sim_level,
    string environment_path,
    string interface_names[],
    uvm_reg_block register_model = null,
    uvmf_active_passive_t interface_activity[] = {}
);
    super.initialize(sim_level, environment_path, interface_names, register_model, interface_activity);
    
    if ( !uvm_config_db #(ahb_lite_slave_0_bfm_t)::get( null, "UVMF_VIRTUAL_INTERFACES", interface_names[0], ahb_lite_slave_0_cfg.m_bfm ) )
    begin
        `uvm_fatal("Config Error", $sformatf("uvm_config_db #(ahb_lite_slave_0_bfm_t)::get() cannot find bfm vif handle for agent with interface_name '%s'", interface_names[0]))
    end
    
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
    
    ahb_lite_slave_0_config_policy::configure(ahb_lite_slave_0_cfg, MBOX);
    if ( interface_activity.size() > 0 )
    begin
        case ( interface_activity[0] )
            ACTIVE :
                ahb_lite_slave_0_cfg.agent_cfg.is_active = 1;
            PASSIVE :
                ahb_lite_slave_0_cfg.agent_cfg.is_active = 0;
        endcase
    end
endfunction: initialize

