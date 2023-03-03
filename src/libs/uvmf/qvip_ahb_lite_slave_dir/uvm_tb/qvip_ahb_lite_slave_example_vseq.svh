//
// File: qvip_ahb_lite_slave_example_vseq.svh
//
// Generated from Mentor VIP Configurator (20220406)
// Generated using Mentor VIP Library ( 2022.2 : 04/20/2022:16:06 )
//
// The purpose of this example virtual sequence is to show how the default or selected sequences for 
// each QVIP can be run. The sequences are run in series in an arbitary order. 
class qvip_ahb_lite_slave_example_vseq extends qvip_ahb_lite_slave_vseq_base;
    `uvm_object_utils(qvip_ahb_lite_slave_example_vseq)
    function new
    (
        string name = "qvip_ahb_lite_slave_example_vseq"
    );
        super.new(name);
    endfunction
    
    extern task body;
    
endclass: qvip_ahb_lite_slave_example_vseq

task qvip_ahb_lite_slave_example_vseq::body;
    ahb_single_wr_deparam_seq ahb_lite_slave_0_seq_0 = ahb_single_wr_deparam_seq::type_id::create("ahb_single_wr_deparam_seq");
    ahb_single_rd_deparam_seq ahb_lite_slave_0_seq_1 = ahb_single_rd_deparam_seq::type_id::create("ahb_single_rd_deparam_seq");
    
    // Sequences run in the following order
    
    begin
        ahb_lite_slave_0_seq_0.start(ahb_lite_slave_0);
        ahb_lite_slave_0_seq_1.start(ahb_lite_slave_0);
    end
endtask: body

