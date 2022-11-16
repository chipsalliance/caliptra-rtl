//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
// Placeholder for complete register model.  This placeholder allows
//  compilation of generated environment without modification.
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

package soc_ifc_reg_model_top_pkg;

   import uvm_pkg::*;
// pragma uvmf custom additional_imports begin
    import soc_ifc_reg_uvm::*;
    import mbox_csr_uvm::*;
// pragma uvmf custom additional_imports end

   `include "uvm_macros.svh"

   /* DEFINE REGISTER CLASSES */
// pragma uvmf custom define_register_classes begin
    class soc_ifc_reg__intr_block_t_ext extends soc_ifc_reg__intr_block_t;
        uvm_reg_map soc_ifc_reg_intr_AHB_map;
        uvm_reg_map soc_ifc_reg_intr_APB_map;

        function new(string name = "soc_ifc_reg__intr_block_t_ext");
            super.new(name);
        endfunction : new

        virtual function void build();
            super.build();
            this.soc_ifc_reg_intr_AHB_map = create_map("intr_AHB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
            this.soc_ifc_reg_intr_APB_map = create_map("intr_APB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
        endfunction

        virtual function void build_ext_maps();
            uvm_reg regs[$];

            this.default_map.get_registers(regs, UVM_NO_HIER);
            foreach(regs[c_reg]) begin
                this.soc_ifc_reg_intr_AHB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
                this.soc_ifc_reg_intr_APB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
            end
        endfunction

    endclass : soc_ifc_reg__intr_block_t_ext

    class soc_ifc_reg_ext extends soc_ifc_reg;
        // default_map_ext has intr_block_rf_ext.default_map as a submap; the
        // native this.default_map adds intr_block_rf.default_map as submap
        // We need this additional map so that the new intr_block_rf_ext can be
        // initialized, and the default_map assigned to a parent. This allows
        // get_offset methods to work on member registers, so we can then add
        // them to the AHB/APB maps
        uvm_reg_map default_map_ext;
        uvm_reg_map soc_ifc_reg_AHB_map;
        uvm_reg_map soc_ifc_reg_APB_map;

        // This coexists with intr_block_rf (from the parent class), but
        // intr_block_rf is only added as a submap to default_map and
        // should never be used in practice
        rand soc_ifc_reg__intr_block_t_ext intr_block_rf_ext;

        function new(string name = "soc_ifc_reg_ext");
            super.new(name);
        endfunction : new

        virtual function void build();
            super.build();
            this.intr_block_rf_ext = new("intr_block_rf_ext");
            this.intr_block_rf_ext.configure(this);
            this.intr_block_rf_ext.build(); // This configures the default_map, which is used to find reg offsets for other maps
            this.default_map_ext     = create_map("default_map_ext", 0, 4, UVM_LITTLE_ENDIAN);
            this.soc_ifc_reg_AHB_map = create_map("AHB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
            this.soc_ifc_reg_APB_map = create_map("APB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
        endfunction

        virtual function void build_ext_maps();
            uvm_reg        regs[$];
            uvm_reg_map    submaps[$];
            uvm_reg_addr_t intr_block_offset;

            this.default_map.get_registers(regs,    UVM_NO_HIER);
            this.default_map.get_submaps  (submaps, UVM_NO_HIER); // <-- these submaps are from this.intr_block_rf.default_map, per the inherited build() method

            foreach(regs[c_reg]) begin
                this.default_map_ext    .add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
                this.soc_ifc_reg_AHB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
                this.soc_ifc_reg_APB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
            end
            // Find offset used to add intr_block_rf.default_map to this.default_map, so we can
            // use the same offset to add submaps to intr_block_rf_ext
            foreach(submaps[c_submap]) begin
                if (submaps[c_submap].get_name() == "reg_map") begin
                    intr_block_offset = this.default_map.get_submap_offset(submaps[c_submap]);
                end
            end

            this.default_map_ext    .add_submap(this.intr_block_rf_ext.default_map, intr_block_offset);
            this.intr_block_rf_ext.build_ext_maps(); // This configures the AHB/APB maps
            this.soc_ifc_reg_AHB_map.add_submap(this.intr_block_rf_ext.soc_ifc_reg_intr_AHB_map, intr_block_offset);
            this.soc_ifc_reg_APB_map.add_submap(this.intr_block_rf_ext.soc_ifc_reg_intr_APB_map, intr_block_offset);

        endfunction

    endclass : soc_ifc_reg_ext

    class mbox_csr_ext extends mbox_csr;
        uvm_reg_map mbox_csr_AHB_map;
        uvm_reg_map mbox_csr_APB_map;

        function new(string name = "mbox_csr_ext");
            super.new(name);
        endfunction : new

        virtual function void build();
            super.build();
            this.mbox_csr_AHB_map = create_map("AHB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
            this.mbox_csr_APB_map = create_map("APB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);
        endfunction

        virtual function void build_ext_maps();
            uvm_reg        regs[$];

            this.default_map.get_registers(regs, UVM_NO_HIER);

            foreach(regs[c_reg]) begin
                this.mbox_csr_AHB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
                this.mbox_csr_APB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.default_map));
            end

        endfunction

    endclass : mbox_csr_ext
// pragma uvmf custom define_register_classes end

// pragma uvmf custom define_block_map_coverage_class begin
   //--------------------------------------------------------------------
   // Class: soc_ifc_fixme_map_coverage
   // 
   // Coverage for the 'fixme_map' in 'soc_ifc_reg_model'
   //--------------------------------------------------------------------
   class soc_ifc_fixme_map_coverage extends uvm_object;
      `uvm_object_utils(soc_ifc_fixme_map_coverage)

      covergroup ra_cov(string name) with function sample(uvm_reg_addr_t addr, bit is_read);

         option.per_instance = 1;
         option.name = name; 

         ADDR: coverpoint addr {
            bins example_reg0 = {'h0};
            bins example_reg1 = {'h1};
         }

         RW: coverpoint is_read {
            bins RD = {1};
            bins WR = {0};
         }

         ACCESS: cross ADDR, RW;

      endgroup: ra_cov

      function new(string name = "soc_ifc_fixme_map_coverage");
         ra_cov = new(name);
      endfunction: new

      function void sample(uvm_reg_addr_t offset, bit is_read);
         ra_cov.sample(offset, is_read);
      endfunction: sample

   endclass: soc_ifc_fixme_map_coverage
// pragma uvmf custom define_block_map_coverage_class end

   //--------------------------------------------------------------------
   // Class: soc_ifc_reg_model_top
   // 
   //--------------------------------------------------------------------
   class soc_ifc_reg_model_top extends uvm_reg_block;
      `uvm_object_utils(soc_ifc_reg_model_top)
// pragma uvmf custom instantiate_registers_within_block begin
        rand uvm_mem          mbox_mem_rm;
        rand mbox_csr_ext     mbox_csr_rm;
        rand soc_ifc_reg_ext  soc_ifc_reg_rm;

        uvm_reg_map default_map; // Block map
        uvm_reg_map soc_ifc_APB_map; // Block map
        uvm_reg_map soc_ifc_AHB_map; // Block map
// pragma uvmf custom instantiate_registers_within_block end

      soc_ifc_fixme_map_coverage fixme_map_cg;

      // Function: new
      // 
      function new(string name = "soc_ifc_reg_model_top");
         super.new(name, build_coverage(UVM_CVR_ALL));
      endfunction

      // Function: build
      // 
      virtual function void build();
      if(has_coverage(UVM_CVR_ADDR_MAP)) begin
         fixme_map_cg = soc_ifc_fixme_map_coverage::type_id::create("fixme_map_cg");
         fixme_map_cg.ra_cov.set_inst_name(this.get_full_name());
         void'(set_coverage(UVM_CVR_ADDR_MAP));
      end


// pragma uvmf custom construct_configure_build_registers_within_block begin

        // inst all soc_ifc register blocks and memory model as single reg block
        /*mbox_mem_ahb_apb*/
        this.mbox_mem_rm = new("mbox_mem_rm", 18'h8000, 32, "RW", UVM_NO_COVERAGE);
        this.mbox_mem_rm.configure(this);

        /*mbox_csr_ahb_apb*/
        this.mbox_csr_rm = new("mbox_csr_rm");
        this.mbox_csr_rm.configure(this);
        this.mbox_csr_rm.build();

        /*soc_ifc_reg_ahb_apb*/
        this.soc_ifc_reg_rm = new("soc_ifc_reg_rm");
        this.soc_ifc_reg_rm.configure(this);
        this.soc_ifc_reg_rm.build();

// pragma uvmf custom construct_configure_build_registers_within_block end
// pragma uvmf custom add_registers_to_block_map begin
        /* Top register model default map */
        // NOTE: Initialize here using add_submap to avoid UVM_WARNING inside uvm_reg_map
        //       but we don't ever use the "default_map" -- instead use AHB/APB maps to
        //       access registers
        this.default_map = create_map("soc_ifc_default_map", 0, 4, UVM_LITTLE_ENDIAN);
        this.default_map.add_mem(this.mbox_mem_rm, 0, "RW");
        this.default_map.add_submap(this.mbox_csr_rm.default_map, 'h2_0000);
        this.default_map.add_submap(this.soc_ifc_reg_rm.default_map, 'h3_0000);

        this.soc_ifc_APB_map = create_map("soc_ifc_APB_map", 0, 4, UVM_LITTLE_ENDIAN);
        this.soc_ifc_AHB_map = create_map("soc_ifc_AHB_map", 0, 4, UVM_LITTLE_ENDIAN);

      endfunction

      // Called after lock_model in soc_ifc_env_configuration
      virtual function void build_ext_maps();
        // Requires default_map.add_submap first to avoid UVM_WARNING about
        // is_intialized (due to look-up of get_offset in constituent regs)
        // Also requires block.is_locked() to be true
        this.mbox_csr_rm.build_ext_maps();
        this.soc_ifc_reg_rm.build_ext_maps();

        /* Top register model APB map */
        this.soc_ifc_APB_map.add_mem(this.mbox_mem_rm, 0, "RW");
        this.soc_ifc_APB_map.add_submap(this.mbox_csr_rm.mbox_csr_APB_map, 'h2_0000);
        this.soc_ifc_APB_map.add_submap(this.soc_ifc_reg_rm.soc_ifc_reg_APB_map, 'h3_0000);

        /* Top register model AHB map */
        this.soc_ifc_AHB_map.add_mem(this.mbox_mem_rm, 0, "RW");
        this.soc_ifc_AHB_map.add_submap(this.mbox_csr_rm.mbox_csr_AHB_map, 'h2_0000);
        this.soc_ifc_AHB_map.add_submap(this.soc_ifc_reg_rm.soc_ifc_reg_AHB_map, 'h3_0000);

// pragma uvmf custom add_registers_to_block_map end


      endfunction

      // Function: sample
      //
      function void sample(uvm_reg_addr_t offset, bit is_read, uvm_reg_map  map);
         if(get_coverage(UVM_CVR_ADDR_MAP)) begin
            if(map.get_name() == "fixme_map_cg") begin
               fixme_map_cg.sample(offset, is_read);
            end
         end
      endfunction: sample

   endclass

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

