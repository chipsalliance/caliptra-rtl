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
//----------------------------------------------------------------------
//
// DESCRIPTION: This test extends test_top and makes
//    changes to test_top using the UVM factory type_override:
//
//    Test scenario:
//        External TRNG req test
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_trng_test extends test_top;

  `uvm_component_utils( soc_ifc_trng_test );

  function new( string name = "", uvm_component parent = null );
    super.new( name, parent );
  endfunction

  virtual function void build_phase(uvm_phase phase);
    // The factory override below is an example of how to replace the soc_ifc_bench_sequence_base
    // sequence with the example_derived_test_sequence.
    soc_ifc_bench_sequence_base::type_id::set_type_override(soc_ifc_trng_test_sequence::get_type());
    // Execute the build_phase of test_top AFTER all factory overrides have been created.
    super.build_phase(phase);
    // pragma uvmf custom configuration_settings_post_randomize begin
    // UVMF_CHANGE_ME Test specific configuration values can be set here.
    // The configuration structure has already been randomized.
    // pragma uvmf custom configuration_settings_post_randomize end
  endfunction

  // FIXME this disables uvm_warning messages! We should fix the warnings, but for
  //       now this reduces sim.log (for regressions) to a manageable level
  virtual function void start_of_simulation_phase(uvm_phase phase);
      super.start_of_simulation_phase(phase);
      if ($test$plusargs("CLP_REGRESSION")) begin
          uvm_top.set_report_verbosity_level_hier(UVM_NONE);
          this.environment.soc_ifc_pred.set_report_severity_action(UVM_WARNING,UVM_NO_ACTION);
          this.environment.soc_ifc_sb.set_report_severity_action(UVM_WARNING,UVM_NO_ACTION);
          // Since en_sb is recently set to 0, this is unavailable and gives null-object
          //this.environment.qvip_apb5_slave_subenv.apb5_master_0.get_analysis_component("checker").set_report_severity_id_action(UVM_WARNING,"scoreboard_debug",UVM_NO_ACTION);
      end
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
