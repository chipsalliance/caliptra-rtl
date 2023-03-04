//
// File: qvip_ahb_lite_slave_vseq_base.svh
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
class qvip_ahb_lite_slave_vseq_base extends uvm_sequence;
    `uvm_object_utils(qvip_ahb_lite_slave_vseq_base)
    // Handles for each of the target (QVIP) sequencers
    
    mvc_sequencer ahb_lite_slave_0_sqr;
    function new
    (
        string name = "qvip_ahb_lite_slave_vseq_base"
    );
        super.new(name);
        if ( !uvm_config_db #(mvc_sequencer)::get(null,UVMF_SEQUENCERS,"ahb_lite_slave_0", ahb_lite_slave_0_sqr) )
        begin
            `uvm_error("Config Error" , "uvm_config_db #( mvc_sequencer )::get cannot find resource 'ahb_lite_slave_0'" )
        end
    endfunction
    
    extern task body;
    
endclass: qvip_ahb_lite_slave_vseq_base

task qvip_ahb_lite_slave_vseq_base::body;
endtask: body

