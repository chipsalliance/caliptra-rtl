//
// File: qvip_ahb_lite_slave_vseq_base.svh
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
class qvip_ahb_lite_slave_vseq_base extends uvm_sequence;
    `uvm_object_utils(qvip_ahb_lite_slave_vseq_base)
    // Handles for each of the target (QVIP) sequencers
    
    mvc_sequencer ahb_lite_slave_0;
    function new
    (
        string name = "qvip_ahb_lite_slave_vseq_base"
    );
        super.new(name);
    endfunction
    
    task body;
    endtask: body
    
endclass: qvip_ahb_lite_slave_vseq_base

