class soc_ifc_env_axi_uvm_nonblocking_write_sequence extends aaxi_uvm_seq_basic_write;
    `uvm_object_utils(soc_ifc_env_axi_uvm_nonblocking_write_sequence)

    function new(string name = "");
        super.new(name);
    endfunction

    virtual task body();
        bit ok; 
        // super.body();

        repeat(5) begin
            `uvm_info("KNU_NB", "Creating and sending req", UVM_MEDIUM)
            `uvm_create(req);
            req.vers = AAXI4;
            ok = req.randomize() with {
                kind == AAXI_WRITE;
            };
            assert (ok) else `uvm_fatal(get_type_name(), "Randomization Failed");
            `uvm_send(req);
        end
    endtask
endclass