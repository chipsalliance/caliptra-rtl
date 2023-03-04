//
// File: qvip_ahb_lite_slave_pkg.sv
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
// ## The following code is used to add this qvip_configurator generated output into an
// ## encapsulating UVMF Generated environment.  The addQvipSubEnv function is added to 
// ## the python configuration file used by the UVMF environment generator.
// env.addQvipSubEnv('sub_env_instance_name', 'qvip_ahb_lite_slave', ['ahb_lite_slave_0'])
//
// ## The following code is used to add this qvip_configurator generated output into an
// ## encapsulating UVMF Generated test bench.  The addQvipBfm function is added to 
// ## the python configuration file used by the UVMF bench generator.
// ben.addQvipBfm('ahb_lite_slave_0', 'qvip_ahb_lite_slave', 'ACTIVE')
package qvip_ahb_lite_slave_pkg;
    import uvm_pkg::*;
    
    `include "uvm_macros.svh"
    
    import addr_map_pkg::*;
    
    import uvmf_base_pkg::*;
    import qvip_ahb_lite_slave_params_pkg::*;
    import mvc_pkg::*;
    import mgc_ahb_seq_pkg::*;
    import mgc_ahb_v2_0_pkg::*;
    
    `include "qvip_ahb_lite_slave_env_configuration.svh"
    `include "qvip_ahb_lite_slave_environment.svh"
endpackage: qvip_ahb_lite_slave_pkg
