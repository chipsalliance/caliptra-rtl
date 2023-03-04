//
// File: qvip_ahb_lite_slave_test_base.svh
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
class qvip_ahb_lite_slave_test_base extends uvm_test;
    `uvm_component_utils(qvip_ahb_lite_slave_test_base)
    // QVIP Configuration objects = As defined in the qvip_ahb_lite_slave_params_pkg
    
    ahb_lite_slave_0_cfg_t ahb_lite_slave_0_cfg;
    // Environment configuration object
    qvip_ahb_lite_slave_env_config env_cfg;
    
    // Environment component
    qvip_ahb_lite_slave_env env;
    function new
    (
        string name = "qvip_ahb_lite_slave_test_base_test_base",
        uvm_component parent = null
    );
        super.new(name, parent);
    endfunction
    
    extern function void init_vseq
    (
        qvip_ahb_lite_slave_vseq_base vseq
    );
    
    extern function void build_phase
    (
        uvm_phase phase
    );
    
    extern task run_phase
    (
        uvm_phase phase
    );
    
endclass: qvip_ahb_lite_slave_test_base

function void qvip_ahb_lite_slave_test_base::init_vseq
(
    qvip_ahb_lite_slave_vseq_base vseq
);
    vseq.ahb_lite_slave_0 = env.ahb_lite_slave_0.m_sequencer;
endfunction: init_vseq

function void qvip_ahb_lite_slave_test_base::build_phase
(
    uvm_phase phase
);
    env_cfg = qvip_ahb_lite_slave_env_config::type_id::create("env_cfg");
    env_cfg.initialize();
    
    ahb_lite_slave_0_cfg = ahb_lite_slave_0_cfg_t::type_id::create("ahb_lite_slave_0_cfg" );
    if ( !uvm_config_db #(ahb_lite_slave_0_bfm_t)::get(this, "", "ahb_lite_slave_0", ahb_lite_slave_0_cfg.m_bfm) )
    begin
        `uvm_error("build_phase", "Unable to get virtual interface ahb_lite_slave_0 for ahb_lite_slave_0_cfg from uvm_config_db")
    end
    ahb_lite_slave_0_config_policy::configure(ahb_lite_slave_0_cfg, env_cfg.MBOX);
    env_cfg.ahb_lite_slave_0_cfg = ahb_lite_slave_0_cfg;
    
    // Once the agent configuration objects are done build the env
    env = qvip_ahb_lite_slave_env::type_id::create("env", this);
    env.cfg = env_cfg;
endfunction: build_phase

task qvip_ahb_lite_slave_test_base::run_phase
(
    uvm_phase phase
);
    string sequence_name;
    qvip_ahb_lite_slave_vseq_base vseq;
    uvm_object obj;
    uvm_cmdline_processor clp;
    uvm_factory factory;
    clp = uvm_cmdline_processor::get_inst();
    factory = uvm_factory::get();
    if ( clp.get_arg_value("+SEQ=", sequence_name) == 0 )
    begin
        `uvm_fatal(get_type_name(), "You must specify a virtual sequence to run using the +SEQ plusarg")
    end
    obj = factory.create_object_by_name(sequence_name);
    if ( obj == null )
    begin
        factory.print();
        `uvm_fatal(get_type_name(), {"Virtual sequence '",sequence_name,"' not found in factory"})
    end
    
    if ( !$cast(vseq, obj) )
    begin
        `uvm_fatal(get_type_name(), {"Virtual sequence '",sequence_name,"' is not derived from qvip_ahb_lite_slave_vseq_base"})
    end
    
    //The sequence is OK to run
    `uvm_info(get_type_name(), {"Running virtual sequence '",sequence_name,"'"}, UVM_LOW)
    
    phase.raise_objection(this);
    init_vseq(vseq);
    vseq.start(null);
    phase.drop_objection(this);
endtask: run_phase

