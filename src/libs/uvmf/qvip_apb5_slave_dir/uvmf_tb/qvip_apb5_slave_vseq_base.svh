//
// File: qvip_apb5_slave_vseq_base.svh
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
class qvip_apb5_slave_vseq_base extends uvm_sequence;
    `uvm_object_utils(qvip_apb5_slave_vseq_base)
    // Handles for each of the target (QVIP) sequencers
    
    mvc_sequencer apb5_master_0_sqr;
    function new
    (
        string name = "qvip_apb5_slave_vseq_base"
    );
        super.new(name);
        if ( !uvm_config_db #(mvc_sequencer)::get(null,UVMF_SEQUENCERS,"apb5_master_0", apb5_master_0_sqr) )
        begin
            `uvm_error("Config Error" , "uvm_config_db #( mvc_sequencer )::get cannot find resource 'apb5_master_0'" )
        end
    endfunction
    
    extern task body;
    
endclass: qvip_apb5_slave_vseq_base

task qvip_apb5_slave_vseq_base::body;
endtask: body

