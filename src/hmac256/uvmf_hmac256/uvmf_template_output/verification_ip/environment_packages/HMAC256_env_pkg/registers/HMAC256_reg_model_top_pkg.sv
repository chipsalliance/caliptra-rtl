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

package HMAC256_reg_model_top_pkg;

   import uvm_pkg::*;
// pragma uvmf custom additional_imports begin
   import hmac256_reg_uvm::*;
// pragma uvmf custom additional_imports end

   `include "uvm_macros.svh"

   /* DEFINE REGISTER CLASSES */
// pragma uvmf custom define_register_classes begin
   //--------------------------------------------------------------------
   // Class: hmac256_example_reg0
   //
   // Unused placeholder kept to mirror the abr/mldsa pattern. Real
   // HMAC256 register classes come from the PeakRDL-generated
   // hmac256_reg_uvm package imported above.
   //--------------------------------------------------------------------
   class hmac256_example_reg0 extends uvm_reg;
      `uvm_object_utils(hmac256_example_reg0)

      rand uvm_reg_field example_field;

      function new(string name = "hmac256_example_reg0");
         super.new(name, 8, UVM_NO_COVERAGE);
      endfunction

      virtual function void build();
         example_field = uvm_reg_field::type_id::create("example_field");
         example_field.configure(this, 8, 0, "RW", 0, 8'h00, 1, 1, 1);
      endfunction
   endclass

   //--------------------------------------------------------------------
   // Class: hmac256_example_reg1
   //
   // Unused placeholder; see hmac256_example_reg0 above.
   //--------------------------------------------------------------------
   class hmac256_example_reg1 extends uvm_reg;
      `uvm_object_utils(hmac256_example_reg1)

      rand uvm_reg_field example_field;

      function new(string name = "hmac256_example_reg1");
         super.new(name, 8, UVM_NO_COVERAGE);
      endfunction

      virtual function void build();
         example_field = uvm_reg_field::type_id::create("example_field");
         example_field.configure(this, 8, 0, "RW", 0, 8'h00, 1, 1, 1);
      endfunction
   endclass
// pragma uvmf custom define_register_classes end

// pragma uvmf custom define_block_map_coverage_class begin
   //--------------------------------------------------------------------
   // Class: hmac256_ahb_map_coverage
   // 
   // Coverage for the 'ahb_map' in 'hmac256_reg_model'
   //--------------------------------------------------------------------
   class hmac256_ahb_map_coverage extends uvm_object;
      `uvm_object_utils(hmac256_ahb_map_coverage)

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

      function new(string name = "hmac256_ahb_map_coverage");
         ra_cov = new(name);
      endfunction: new

      function void sample(uvm_reg_addr_t offset, bit is_read);
         ra_cov.sample(offset, is_read);
      endfunction: sample

   endclass: hmac256_ahb_map_coverage
// pragma uvmf custom define_block_map_coverage_class end

   //--------------------------------------------------------------------
   // Class: hmac256_reg_model_top
   // 
   //--------------------------------------------------------------------
   class hmac256_reg_model_top extends hmac256_reg;
      `uvm_object_utils(hmac256_reg_model_top)
// pragma uvmf custom instantiate_registers_within_block begin
      // All HMAC256 register handles are inherited from hmac256_reg
      // (HMAC256_CTRL, HMAC256_KEY[16], HMAC256_BLOCK[16],
      // HMAC256_TAG[8], HMAC256_LFSR_SEED[3], HMAC256_STATUS, etc.).
      // Alias the PeakRDL parent's default_map under the name the
      // UVMF-generated HMAC256_environment.svh expects.
      uvm_reg_map ahb_map;
// pragma uvmf custom instantiate_registers_within_block end

      hmac256_ahb_map_coverage ahb_map_cg;

      // Function: new
      function new(string name = "hmac256_reg_model_top");
         super.new(name);
      endfunction

      // Function: build
      virtual function void build();
         super.build();   // builds and maps every HMAC256 register
         ahb_map = this.default_map;   // alias so UVMF env can call regmodel.ahb_map.*
         if(has_coverage(UVM_CVR_ADDR_MAP)) begin
            ahb_map_cg = hmac256_ahb_map_coverage::type_id::create("ahb_map_cg");
            ahb_map_cg.ra_cov.set_inst_name({this.get_full_name(), "_ahb_cg"});
            void'(set_coverage(UVM_CVR_ADDR_MAP));
         end
// pragma uvmf custom construct_configure_build_registers_within_block begin
         // No extra registers to construct; hmac256_reg::build() already did it all.
// pragma uvmf custom construct_configure_build_registers_within_block end
// pragma uvmf custom add_registers_to_block_map begin
         // hmac256_reg::build() added all registers to default_map already.
// pragma uvmf custom add_registers_to_block_map end
      endfunction

      // Function: sample
      function void sample(uvm_reg_addr_t offset, bit is_read, uvm_reg_map map);
         if(get_coverage(UVM_CVR_ADDR_MAP)) begin
            if(map.get_name() == "reg_map") begin
               ahb_map_cg.sample(offset, is_read);
            end
         end
      endfunction: sample

   endclass

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

