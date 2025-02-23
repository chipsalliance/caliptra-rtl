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
// This sequences randomizes the ss_mode_ctrl transaction and sends it 
// to the UVM driver.
//
// This sequence constructs and randomizes a ss_mode_ctrl_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class ss_mode_ctrl_random_sequence 
  extends ss_mode_ctrl_sequence_base ;

  `uvm_object_utils( ss_mode_ctrl_random_sequence )

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
      req=ss_mode_ctrl_transaction::type_id::create("req");
      start_item(req);
      // Randomize the transaction
      if(!req.randomize()) `uvm_fatal("SEQ", "ss_mode_ctrl_random_sequence::body()-ss_mode_ctrl_transaction randomization failed")
      // Send the transaction to the ss_mode_ctrl_driver_bfm via the sequencer and ss_mode_ctrl_driver.
      finish_item(req);
      `uvm_info("SEQ", {"Response:",req.convert2string()},UVM_MEDIUM)

  endtask

endclass: ss_mode_ctrl_random_sequence

// pragma uvmf custom external begin
// pragma uvmf custom external end

