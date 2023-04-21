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

package kv_reg_model_top_pkg;

   import uvm_pkg::*;
// pragma uvmf custom additional_imports begin
   import kv_reg_uvm::*;
// pragma uvmf custom additional_imports end

   `include "uvm_macros.svh"

   /* DEFINE REGISTER CLASSES */
// pragma uvmf custom define_register_classes begin

   class kv_reg_ext extends kv_reg;
      uvm_reg_map default_map_ext;

      //Write Interface
      uvm_reg_map kv_reg_hmac_write_map;
      uvm_reg_map kv_reg_sha512_write_map;
      uvm_reg_map kv_reg_ecc_write_map;
      uvm_reg_map kv_reg_doe_write_map;

      //AHB Interface
      uvm_reg_map kv_reg_AHB_map;

      //Read Interface
      uvm_reg_map kv_reg_hmac_key_read_map;
      uvm_reg_map kv_reg_hmac_block_read_map;
      uvm_reg_map kv_reg_sha512_block_read_map;
      uvm_reg_map kv_reg_ecc_privkey_read_map;
      uvm_reg_map kv_reg_ecc_seed_read_map;

      function new(string name = "kv_reg_ext");
         super.new(name);
      endfunction : new

      virtual function void build();
         super.build();
         this.default_map_ext                = create_map("default_map_ext", 0, 4, UVM_LITTLE_ENDIAN);

         //Write Interface
         this.kv_reg_hmac_write_map          = create_map("keyvault_reg_hmac_write_map", 0, 4, UVM_LITTLE_ENDIAN);
         this.kv_reg_sha512_write_map        = create_map("keyvault_reg_sha512_write_map", 0, 4, UVM_LITTLE_ENDIAN);
         this.kv_reg_ecc_write_map           = create_map("keyvault_reg_ecc_write_map", 0, 4, UVM_LITTLE_ENDIAN);
         this.kv_reg_doe_write_map           = create_map("keyvault_reg_doe_write_map", 0, 4, UVM_LITTLE_ENDIAN);

         //AHB Interface
         this.kv_reg_AHB_map                 = create_map("keyvault_AHB_reg_map", 0, 4, UVM_LITTLE_ENDIAN);

         //Read Interface
         this.kv_reg_hmac_key_read_map       = create_map("keyvault_reg_hmac_key_read_map", 0, 4, UVM_LITTLE_ENDIAN);
         this.kv_reg_hmac_block_read_map     = create_map("keyvault_reg_hmac_block_read_map", 0, 4, UVM_LITTLE_ENDIAN);
         this.kv_reg_sha512_block_read_map   = create_map("keyvault_reg_sha512_block_read_map", 0, 4, UVM_LITTLE_ENDIAN);
         this.kv_reg_ecc_privkey_read_map    = create_map("keyvault_reg_ecc_privkey_read_map", 0, 4, UVM_LITTLE_ENDIAN);
         this.kv_reg_ecc_seed_read_map       = create_map("keyvault_reg_ecc_seed_read_map", 0, 4, UVM_LITTLE_ENDIAN);
      endfunction

      virtual function void build_ext_maps();
         uvm_reg regs[$];

         this.default_map.get_registers(regs, UVM_NO_HIER);
         foreach(regs[c_reg]) begin
            this.default_map_ext.add_reg                (regs[c_reg], regs[c_reg].get_offset(this.default_map));

            //Write Interface
            this.kv_reg_hmac_write_map.add_reg          (regs[c_reg], regs[c_reg].get_offset(this.default_map));
            this.kv_reg_sha512_write_map.add_reg        (regs[c_reg], regs[c_reg].get_offset(this.default_map));
            this.kv_reg_ecc_write_map.add_reg           (regs[c_reg], regs[c_reg].get_offset(this.default_map));
            this.kv_reg_doe_write_map.add_reg           (regs[c_reg], regs[c_reg].get_offset(this.default_map));

            //AHB Interface
            this.kv_reg_AHB_map.add_reg                 (regs[c_reg], regs[c_reg].get_offset(this.default_map));

            //Read Interface
            this.kv_reg_hmac_key_read_map.add_reg       (regs[c_reg], regs[c_reg].get_offset(this.default_map));
            this.kv_reg_hmac_block_read_map.add_reg     (regs[c_reg], regs[c_reg].get_offset(this.default_map));
            this.kv_reg_sha512_block_read_map.add_reg   (regs[c_reg], regs[c_reg].get_offset(this.default_map));
            this.kv_reg_ecc_privkey_read_map.add_reg    (regs[c_reg], regs[c_reg].get_offset(this.default_map));
            this.kv_reg_ecc_seed_read_map.add_reg       (regs[c_reg], regs[c_reg].get_offset(this.default_map));
         end

      endfunction

   endclass : kv_reg_ext

   //--------------------------------------------------------------------
   // Class: kv_example_reg0
   // 
   //--------------------------------------------------------------------
   class kv_example_reg0 extends uvm_reg;
      `uvm_object_utils(kv_example_reg0)

      rand uvm_reg_field example_field; 

      // Function: new
      // 
      function new(string name = "kv_example_reg0");
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
   // Class: kv_example_reg1
   // 
   //--------------------------------------------------------------------
   class kv_example_reg1 extends uvm_reg;
      `uvm_object_utils(kv_example_reg1)

      rand uvm_reg_field example_field; 

      // Function: new
      // 
      function new(string name = "kv_example_reg1");
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
   // Class: kv_val_reg
   // 1. Keeps track of when debug mode is unlocked in design so that writes 
   // to other regs can be blocked in reg model
   // 2. Strictly for UVM purposes. This reg is not in design!
   //--------------------------------------------------------------------
   class kv_val_reg extends uvm_reg;
      `uvm_object_utils(kv_val_reg)

      rand uvm_reg_field debug_mode_unlocked;
      rand uvm_reg_field clear_secrets_bit;

      // Function: new
      // 
      function new(string name = "kv_val_reg");
         super.new(name, 2, UVM_NO_COVERAGE);
      endfunction


      // Function: build
      // 
      virtual function void build();
         debug_mode_unlocked = uvm_reg_field::type_id::create("debug_mode_unlocked");
         debug_mode_unlocked.configure(this, 1, 0, "RW", 0, 1'b0, 1, 1, 1);

         clear_secrets_bit = uvm_reg_field::type_id::create("clear_secrets_bit");
         clear_secrets_bit.configure(this, 1, 1, "RW", 0, 1'b0, 1, 1, 1);
      endfunction
   endclass

   //--------------------------------------------------------------------
   // Class: kv_val_ctrl
   // 1. Keeps track of when clear is set in design so that dest_valid and last_dword
   // reset can be emulated in uvm
   // 2. Strictly for UVM purposes. This reg is not in design!
   //--------------------------------------------------------------------
   class kv_val_ctrl extends uvm_reg;
      `uvm_object_utils(kv_val_ctrl)

      rand uvm_reg_field clear; //32 bits, one for each KEY_CTRL

      // Function: new
      // 
      function new(string name = "kv_val_ctrl");
         super.new(name, 32, UVM_NO_COVERAGE);
      endfunction


      // Function: build
      // 
      virtual function void build();
         clear = uvm_reg_field::type_id::create("clear");
         clear.configure(this, 32, 0, "RW", 0, 32'b0, 1, 1, 1);
      endfunction
   endclass
// pragma uvmf custom define_register_classes end

// pragma uvmf custom define_block_map_coverage_class begin
   //--------------------------------------------------------------------
   // Class: kv_ahb_map_coverage
   // 
   // Coverage for the 'ahb_map' in 'kv_reg_model'
   //--------------------------------------------------------------------
   class kv_ahb_map_coverage extends uvm_object;
      `uvm_object_utils(kv_ahb_map_coverage)

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

      function new(string name = "kv_ahb_map_coverage");
         ra_cov = new(name);
      endfunction: new

      function void sample(uvm_reg_addr_t offset, bit is_read);
         ra_cov.sample(offset, is_read);
      endfunction: sample

   endclass: kv_ahb_map_coverage
// pragma uvmf custom define_block_map_coverage_class end

   //TODO: Add coverage classes for each of the maps

   //--------------------------------------------------------------------
   // Class: kv_reg_model_top
   // 
   //--------------------------------------------------------------------
   class kv_reg_model_top extends uvm_reg_block;
      `uvm_object_utils(kv_reg_model_top)
// pragma uvmf custom instantiate_registers_within_block begin
      rand kv_reg_ext kv_reg_rm;

      rand kv_example_reg0 example_reg0;
      rand kv_example_reg1 example_reg1;

      rand kv_val_reg val_reg;
      rand kv_val_ctrl val_ctrl;
// pragma uvmf custom instantiate_registers_within_block end
      uvm_reg_map default_map;

      //Write Interface
      uvm_reg_map kv_hmac_write_map;
      uvm_reg_map kv_sha512_write_map;
      uvm_reg_map kv_ecc_write_map;
      uvm_reg_map kv_doe_write_map;

      //AHB Interface
      uvm_reg_map kv_AHB_map; 
      uvm_reg_map ahb_map; //TODO: needed?

      //Read Interface
      uvm_reg_map kv_hmac_key_read_map;
      uvm_reg_map kv_hmac_block_read_map;
      uvm_reg_map kv_sha512_block_read_map;
      uvm_reg_map kv_ecc_privkey_read_map;
      uvm_reg_map kv_ecc_seed_read_map;

      //TODO add coverage for the other maps
      kv_ahb_map_coverage ahb_map_cg;

      // Function: new
      // 
      function new(string name = "kv_reg_model_top");
         super.new(name, build_coverage(UVM_CVR_ALL));
      endfunction

      // Function: build
      // 
      virtual function void build();
      ahb_map = create_map("ahb_map", 0, 4, UVM_LITTLE_ENDIAN);
      if(has_coverage(UVM_CVR_ADDR_MAP)) begin
         ahb_map_cg = kv_ahb_map_coverage::type_id::create("ahb_map_cg");
         ahb_map_cg.ra_cov.set_inst_name(this.get_full_name());
         void'(set_coverage(UVM_CVR_ADDR_MAP));
      end


// pragma uvmf custom construct_configure_build_registers_within_block begin
      example_reg0 = kv_example_reg0::type_id::create("example_reg0");
      example_reg0.configure(this, null, "example_reg0");
      example_reg0.build();
      example_reg1 = kv_example_reg1::type_id::create("example_reg1");
      example_reg1.configure(this, null, "example_reg1");
      example_reg1.build();

      val_reg = kv_val_reg::type_id::create("val_reg");
      val_reg.configure(this,null,"val_reg");
      val_reg.build();

      val_ctrl = kv_val_ctrl::type_id::create("val_ctrl");
      val_ctrl.configure(this,null,"val_ctrl");
      val_ctrl.build();
// pragma uvmf custom construct_configure_build_registers_within_block end
// pragma uvmf custom add_registers_to_block_map begin
      //ahb_map.add_reg(example_reg0, 'h0, "RW");
      //ahb_map.add_reg(example_reg1, 'h1, "RW");
// pragma uvmf custom add_registers_to_block_map end

      //---------------------------------
      this.kv_reg_rm = new("kv_reg_rm");
      this.kv_reg_rm.configure(this);
      this.kv_reg_rm.build();

      this.default_map = create_map("kv_default_map", 0, 4, UVM_LITTLE_ENDIAN);
      this.default_map.add_submap(this.kv_reg_rm.default_map, 0);
      
      //Write Interface
      this.kv_hmac_write_map   = create_map("kv_hmac_write_map", 0, 4, UVM_LITTLE_ENDIAN);
      this.kv_sha512_write_map = create_map("kv_sha512_write_map", 0, 4, UVM_LITTLE_ENDIAN);
      this.kv_ecc_write_map    = create_map("kv_ecc_write_map", 0, 4, UVM_LITTLE_ENDIAN);
      this.kv_doe_write_map    = create_map("kv_doe_write_map", 0, 4, UVM_LITTLE_ENDIAN);

      //AHB Interface
      this.kv_AHB_map = create_map("kv_AHB_map", 0, 4, UVM_LITTLE_ENDIAN);

      //Read Interface
      this.kv_hmac_key_read_map     = create_map("kv_hmac_key_read_map", 0, 4, UVM_LITTLE_ENDIAN);
      this.kv_hmac_block_read_map   = create_map("kv_hmac_block_read_map", 0, 4, UVM_LITTLE_ENDIAN);
      this.kv_sha512_block_read_map = create_map("kv_sha512_block_read_map", 0, 4, UVM_LITTLE_ENDIAN);
      this.kv_ecc_privkey_read_map  = create_map("kv_ecc_privkey_read_map", 0, 4, UVM_LITTLE_ENDIAN);
      this.kv_ecc_seed_read_map     = create_map("kv_ecc_seed_read_map", 0, 4, UVM_LITTLE_ENDIAN);

      //Add debug_mode reg to all maps (only for TB purposes)
      default_map.add_reg(val_reg, 'h1_0000, "RW");
      default_map.add_reg(val_ctrl, 'h1_0004, "RW");

      kv_hmac_write_map.add_reg(val_reg, 'h1_0000, "RW");
      kv_sha512_write_map.add_reg(val_reg, 'h1_0000, "RW");
      kv_ecc_write_map.add_reg(val_reg, 'h1_0000, "RW");
      kv_doe_write_map.add_reg(val_reg, 'h1_0000, "RW");
      
      kv_hmac_write_map.add_reg  (val_ctrl, 'h1_0004, "RW");
      kv_sha512_write_map.add_reg(val_ctrl, 'h1_0004, "RW");
      kv_ecc_write_map.add_reg   (val_ctrl, 'h1_0004, "RW");
      kv_doe_write_map.add_reg   (val_ctrl, 'h1_0004, "RW");

      kv_AHB_map.add_reg(val_reg, 'h1_0000, "RW");
      kv_AHB_map.add_reg(val_ctrl, 'h1_0004, "RW");
      
      kv_hmac_key_read_map.add_reg(val_reg, 'h1_0000, "RW");
      kv_hmac_block_read_map.add_reg(val_reg, 'h1_0000, "RW");
      kv_sha512_block_read_map.add_reg(val_reg, 'h1_0000, "RW");
      kv_ecc_privkey_read_map.add_reg(val_reg, 'h1_0000, "RW");
      kv_ecc_seed_read_map.add_reg(val_reg, 'h1_0000, "RW");

      kv_hmac_key_read_map.add_reg    (val_ctrl, 'h1_0004, "RW");
      kv_hmac_block_read_map.add_reg  (val_ctrl, 'h1_0004, "RW");
      kv_sha512_block_read_map.add_reg(val_ctrl, 'h1_0004, "RW");
      kv_ecc_privkey_read_map.add_reg (val_ctrl, 'h1_0004, "RW");
      kv_ecc_seed_read_map.add_reg    (val_ctrl, 'h1_0004, "RW");
 
      endfunction

      //Called after lock_model in kv_env_configuration
      virtual function void build_ext_maps();
         this.kv_reg_rm.build_ext_maps();

         //top register model AHB map
         //Write
         this.kv_hmac_write_map.add_submap(this.kv_reg_rm.kv_reg_hmac_write_map, 'h0);
         this.kv_sha512_write_map.add_submap(this.kv_reg_rm.kv_reg_sha512_write_map, 'h0);
         this.kv_ecc_write_map.add_submap(this.kv_reg_rm.kv_reg_ecc_write_map, 'h0);
         this.kv_doe_write_map.add_submap(this.kv_reg_rm.kv_reg_doe_write_map, 'h0);

         //AHB
         this.kv_AHB_map.add_submap(this.kv_reg_rm.kv_reg_AHB_map, 'h0);

         //Read
         this.kv_hmac_key_read_map.add_submap      (this.kv_reg_rm.kv_reg_hmac_key_read_map, 'h0);
         this.kv_hmac_block_read_map.add_submap    (this.kv_reg_rm.kv_reg_hmac_block_read_map, 'h0);
         this.kv_sha512_block_read_map.add_submap  (this.kv_reg_rm.kv_reg_sha512_block_read_map, 'h0);
         this.kv_ecc_privkey_read_map.add_submap   (this.kv_reg_rm.kv_reg_ecc_privkey_read_map, 'h0);
         this.kv_ecc_seed_read_map.add_submap      (this.kv_reg_rm.kv_reg_ecc_seed_read_map, 'h0);

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

