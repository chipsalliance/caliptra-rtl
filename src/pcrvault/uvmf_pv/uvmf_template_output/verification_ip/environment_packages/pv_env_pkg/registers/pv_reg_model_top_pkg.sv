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

package pv_reg_model_top_pkg;

   import uvm_pkg::*;
// pragma uvmf custom additional_imports begin
   import pv_reg_uvm::*;
// pragma uvmf custom additional_imports end

   `include "uvm_macros.svh"

   /* DEFINE REGISTER CLASSES */
// pragma uvmf custom define_register_classes begin

   class pv_reg_ext extends pv_reg;
      uvm_reg_map default_map_ext;

      //Write Interface
      uvm_reg_map pv_reg_sha512_write_map;

      //AHB Interface
      uvm_reg_map pv_reg_AHB_map;

      //Read Interface
      uvm_reg_map pv_reg_sha512_block_read_map;

      function new(string name = "pv_reg_ext");
         super.new(name);
      endfunction : new

      virtual function void build();
         super.build();
         this.default_map_ext                = create_map("default_map_ext", 0, 4, UVM_LITTLE_ENDIAN);

         //Write Interface
         this.pv_reg_sha512_write_map        = create_map("pcrvault_reg_sha512_write_map", 0, 4, UVM_LITTLE_ENDIAN);
         
         //AHB Interface
         this.pv_reg_AHB_map                 = create_map("pcrvault_AHB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);

         //Read Interface
         this.pv_reg_sha512_block_read_map   = create_map("pcrvault_reg_sha512_block_read_map", 0, 4, UVM_LITTLE_ENDIAN);

      endfunction

      virtual function void build_ext_maps();
         uvm_reg regs[$];

         this.default_map.get_registers(regs, UVM_NO_HIER);
         foreach(regs[c_reg]) begin
            this.default_map_ext.add_reg                (regs[c_reg], regs[c_reg].get_offset(this.default_map));

            //Write Interface
            this.pv_reg_sha512_write_map.add_reg        (regs[c_reg], regs[c_reg].get_offset(this.default_map));

            //AHB Interface
            this.pv_reg_AHB_map.add_reg                 (regs[c_reg], regs[c_reg].get_offset(this.default_map));

            //Read Interface
            this.pv_reg_sha512_block_read_map.add_reg   (regs[c_reg], regs[c_reg].get_offset(this.default_map));
            
         end

      endfunction

   endclass : pv_reg_ext

   //--------------------------------------------------------------------
   // Class: pv_example_reg0
   // 
   //--------------------------------------------------------------------
   class pv_example_reg0 extends uvm_reg;
      `uvm_object_utils(pv_example_reg0)

      rand uvm_reg_field example_field; 

      // Function: new
      // 
      function new(string name = "pv_example_reg0");
         super.new(name, 8, UVM_NO_COVERAGE);
      endfunction


      // Function: build
      // 
      virtual function void build();
         example_field = uvm_reg_field::type_id::create("example_field");
         example_field.configure(this, 8, 0, "RW", 0, 8'h00, 1, 1, 1);
      endfunction
   endclass

   //--------------------------------------------------------------------
   // Class: pv_example_reg1
   // 
   //--------------------------------------------------------------------
   class pv_example_reg1 extends uvm_reg;
      `uvm_object_utils(pv_example_reg1)

      rand uvm_reg_field example_field; 

      // Function: new
      // 
      function new(string name = "pv_example_reg1");
         super.new(name, 8, UVM_NO_COVERAGE);
      endfunction


      // Function: build
      // 
      virtual function void build();
         example_field = uvm_reg_field::type_id::create("example_field");
         example_field.configure(this, 8, 0, "RW", 0, 8'h00, 1, 1, 1);
      endfunction
   endclass

   //--------------------------------------------------------------------
   // Class: pv_val_reg
   // 1. Keeps track of when debug mode is unlocked in design so that writes 
   // to other regs can be blocked in reg model
   // 2. Strictly for UVM purposes. This reg is not in design!
   //--------------------------------------------------------------------
   class pv_val_reg extends uvm_reg;
      `uvm_object_utils(pv_val_reg)

      rand uvm_reg_field clear;

      // Function: new
      // 
      function new(string name = "pv_val_reg");
         super.new(name, 1, UVM_NO_COVERAGE);
      endfunction


      // Function: build
      // 
      virtual function void build();
         clear = uvm_reg_field::type_id::create("clear");
         clear.configure(this, 1, 0, "RW", 0, 1'b0, 1, 1, 1);
      endfunction
   endclass
// pragma uvmf custom define_register_classes end

// pragma uvmf custom define_block_map_coverage_class begin
   //--------------------------------------------------------------------
   // Class: pv_ahb_map_coverage
   // 
   // Coverage for the 'ahb_map' in 'pv_reg_model'
   //--------------------------------------------------------------------
   class pv_ahb_map_coverage extends uvm_object;
      `uvm_object_utils(pv_ahb_map_coverage)

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

      function new(string name = "pv_ahb_map_coverage");
         ra_cov = new(name);
      endfunction: new

      function void sample(uvm_reg_addr_t offset, bit is_read);
         ra_cov.sample(offset, is_read);
      endfunction: sample

   endclass: pv_ahb_map_coverage
// pragma uvmf custom define_block_map_coverage_class end

   //TODO: Add coverage classes for each of the maps

   //--------------------------------------------------------------------
   // Class: pv_reg_model_top
   // 
   //--------------------------------------------------------------------
   class pv_reg_model_top extends uvm_reg_block;
      `uvm_object_utils(pv_reg_model_top)
// pragma uvmf custom instantiate_registers_within_block begin
      rand pv_reg_ext pv_reg_rm;

      rand pv_example_reg0 example_reg0;
      rand pv_example_reg1 example_reg1;

      rand pv_val_reg val_reg;
// pragma uvmf custom instantiate_registers_within_block end
      uvm_reg_map default_map;

      //Write Interface
      uvm_reg_map pv_sha512_write_map;

      //AHB Interface
      uvm_reg_map pv_AHB_map; 
      uvm_reg_map ahb_map; //TODO: needed?

      //Read Interface
      uvm_reg_map pv_sha512_block_read_map;

      //TODO add coverage for the other maps
      pv_ahb_map_coverage ahb_map_cg;

      // Function: new
      // 
      function new(string name = "pv_reg_model_top");
         super.new(name, build_coverage(UVM_CVR_ALL));
      endfunction

      // Function: build
      // 
      virtual function void build();
      ahb_map = create_map("ahb_map", 0, 4, UVM_LITTLE_ENDIAN);
      if(has_coverage(UVM_CVR_ADDR_MAP)) begin
         ahb_map_cg = pv_ahb_map_coverage::type_id::create("ahb_map_cg");
         ahb_map_cg.ra_cov.set_inst_name(this.get_full_name());
         void'(set_coverage(UVM_CVR_ADDR_MAP));
      end


// pragma uvmf custom construct_configure_build_registers_within_block begin
      example_reg0 = pv_example_reg0::type_id::create("example_reg0");
      example_reg0.configure(this, null, "example_reg0");
      example_reg0.build();
      example_reg1 = pv_example_reg1::type_id::create("example_reg1");
      example_reg1.configure(this, null, "example_reg1");
      example_reg1.build();

      val_reg = pv_val_reg::type_id::create("val_reg");
      val_reg.configure(this,null,"val_reg");
      val_reg.build();
// pragma uvmf custom construct_configure_build_registers_within_block end
// pragma uvmf custom add_registers_to_block_map begin
      //ahb_map.add_reg(example_reg0, 'h0, "RW");
      //ahb_map.add_reg(example_reg1, 'h1, "RW");
// pragma uvmf custom add_registers_to_block_map end

      //---------------------------------
      this.pv_reg_rm = new("pv_reg_rm");
      this.pv_reg_rm.configure(this);
      this.pv_reg_rm.build();

      this.default_map = create_map("pv_default_map", 0, 4, UVM_LITTLE_ENDIAN);
      this.default_map.add_submap(this.pv_reg_rm.default_map, 0);
      
      //Write Interface
      this.pv_sha512_write_map = create_map("pv_sha512_write_map", 0, 4, UVM_LITTLE_ENDIAN);

      //AHB Interface
      this.pv_AHB_map = create_map("pv_AHB_map", 0, 4, UVM_LITTLE_ENDIAN);

      //Read Interface
      this.pv_sha512_block_read_map = create_map("pv_sha512_block_read_map", 0, 4, UVM_LITTLE_ENDIAN);

      //Add debug_mode reg to all maps (only for TB purposes)
      default_map.add_reg(val_reg, 'h1_0000, "RW");

      pv_sha512_write_map.add_reg(val_reg, 'h1_0000, "RW");

      pv_AHB_map.add_reg(val_reg, 'h1_0000, "RW");
      
      pv_sha512_block_read_map.add_reg(val_reg, 'h1_0000, "RW");
 
      endfunction

      //Called after lock_model in pv_env_configuration
      virtual function void build_ext_maps();
         this.pv_reg_rm.build_ext_maps();

         //top register model AHB map
         //Write
         this.pv_sha512_write_map.add_submap(this.pv_reg_rm.pv_reg_sha512_write_map, 'h0);

         //AHB
         this.pv_AHB_map.add_submap(this.pv_reg_rm.pv_reg_AHB_map, 'h0);

         //Read
         this.pv_sha512_block_read_map.add_submap  (this.pv_reg_rm.pv_reg_sha512_block_read_map, 'h0);

      endfunction

      // Function: sample
      // 
      function void sample(uvm_reg_addr_t offset, bit is_read, uvm_reg_map  map);
         if(get_coverage(UVM_CVR_ADDR_MAP)) begin
            if(map.get_name() == "ahb_map_cg") begin
               ahb_map_cg.sample(offset, is_read);
            end
         end
      endfunction: sample

   endclass

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

