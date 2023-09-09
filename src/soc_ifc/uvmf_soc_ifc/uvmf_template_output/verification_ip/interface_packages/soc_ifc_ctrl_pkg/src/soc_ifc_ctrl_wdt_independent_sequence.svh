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
// DESCRIPTION: 
// This sequences randomizes the soc_ifc_ctrl transaction and sends it 
// to the UVM driver.
//
// This sequence constructs and randomizes a soc_ifc_ctrl_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_ctrl_wdt_independent_sequence 
  extends soc_ifc_ctrl_sequence_base ;

  `uvm_object_utils( soc_ifc_ctrl_wdt_independent_sequence )

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  //*****************************************************************
  function new(string name = "");
    super.new(name);
  endfunction: new

  // ****************************************************************************
  // TASK : body()
  // This task is automatically executed when this sequence is started using the 
  // start(sequencerHandle) task.
  //
  task body();

      // Construct the transaction
    req=soc_ifc_ctrl_transaction::type_id::create("req");
    start_item(req);
    // Randomize the transaction
    if(!req.randomize()) `uvm_fatal("SEQ", "soc_ifc_ctrl_wdt_independent_sequence::body()-soc_ifc_ctrl_transaction randomization failed")
    // req.wait_cycles = 'd1000;
    req.generic_input_val = 64'h1234_5678_90AB_CDEF;
    req.set_pwrgood = 'b1;
    req.assert_rst = 'b0;
    // Send the transaction to the soc_ifc_ctrl_driver_bfm via the sequencer and soc_ifc_ctrl_driver.
    finish_item(req);
    `uvm_info("SEQ", {"Response:",req.convert2string()},UVM_MEDIUM)

      // Construct the transaction
      req=soc_ifc_ctrl_transaction::type_id::create("req");
      start_item(req);
      // Randomize the transaction
      if(!req.randomize()) `uvm_fatal("SEQ", "soc_ifc_ctrl_wdt_independent_sequence::body()-soc_ifc_ctrl_transaction randomization failed")
      // req.wait_cycles = 'd1000;
      req.generic_input_val = 64'hEFEF;
      req.set_pwrgood = 'b1;
      req.assert_rst = 'b0;
      // Send the transaction to the soc_ifc_ctrl_driver_bfm via the sequencer and soc_ifc_ctrl_driver.
      finish_item(req);
      `uvm_info("SEQ", {"Response:",req.convert2string()},UVM_MEDIUM)

  endtask

endclass: soc_ifc_ctrl_wdt_independent_sequence

// pragma uvmf custom external begin
// pragma uvmf custom external end

