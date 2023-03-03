
// This file was autogenerated by PeakRDL-uvm
package pv_reg_uvm;
    `include "uvm_macros.svh"
    import uvm_pkg::*;
    
    // Reg - pv_reg::pvCtrl
    class pv_reg__pvCtrl extends uvm_reg;
        rand uvm_reg_field lock;
        rand uvm_reg_field clear;
        rand uvm_reg_field rsvd0;
        rand uvm_reg_field rsvd1;

        function new(string name = "pv_reg__pvCtrl");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.lock = new("lock");
            this.lock.configure(this, 1, 0, "RW", 0, 'h0, 1, 1, 0);
            this.clear = new("clear");
            this.clear.configure(this, 1, 1, "RW", 0, 'h0, 1, 1, 0);
            this.rsvd0 = new("rsvd0");
            this.rsvd0.configure(this, 1, 2, "RW", 1, 'h0, 1, 1, 0);
            this.rsvd1 = new("rsvd1");
            this.rsvd1.configure(this, 5, 3, "RW", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : pv_reg__pvCtrl

    // Reg - pv_reg::pcrReg
    class pv_reg__pcrReg extends uvm_reg;
        rand uvm_reg_field data;

        function new(string name = "pv_reg__pcrReg");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.data = new("data");
            this.data.configure(this, 32, 0, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : pv_reg__pcrReg

    // Addrmap - pv_reg
    class pv_reg extends uvm_reg_block;
        rand pv_reg__pvCtrl PCR_CTRL[32];
        rand pv_reg__pcrReg PCR_ENTRY[32][12];

        function new(string name = "pv_reg");
            super.new(name);
        endfunction : new

        virtual function void build();
            this.default_map = create_map("reg_map", 0, 4, UVM_NO_ENDIAN);
            foreach(this.PCR_CTRL[i0]) begin
                this.PCR_CTRL[i0] = new($sformatf("PCR_CTRL[%0d]", i0));
                this.PCR_CTRL[i0].configure(this);
                
                this.PCR_CTRL[i0].build();
                this.default_map.add_reg(this.PCR_CTRL[i0], 'h0 + i0*'h4);
            end
            foreach(this.PCR_ENTRY[i0, i1]) begin
                this.PCR_ENTRY[i0][i1] = new($sformatf("PCR_ENTRY[%0d][%0d]", i0, i1));
                this.PCR_ENTRY[i0][i1].configure(this);
                
                this.PCR_ENTRY[i0][i1].build();
                this.default_map.add_reg(this.PCR_ENTRY[i0][i1], 'h600 + i0*'h30 + i1*'h4);
            end
        endfunction : build
    endclass : pv_reg

endpackage: pv_reg_uvm
