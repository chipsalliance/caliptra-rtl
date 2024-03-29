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
// This sequences randomizes the kv_write transaction and sends it 
// to the UVM driver.
//
// This sequence constructs and randomizes a kv_write_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class kv_write_random_sequence #(
      string KV_WRITE_REQUESTOR = "HMAC"
      )
  extends kv_write_sequence_base #(
      .KV_WRITE_REQUESTOR(KV_WRITE_REQUESTOR)
      );

  `uvm_object_param_utils( kv_write_random_sequence #(
                           KV_WRITE_REQUESTOR
                           ))

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
      req=kv_write_transaction#(
                .KV_WRITE_REQUESTOR(KV_WRITE_REQUESTOR)
                )::type_id::create("req");
      req.write_en = 1'b1; //Tie write en to 1 for entire write seq
      start_item(req);
      // Randomize the transaction
      if(!req.randomize()) `uvm_fatal("SEQ", "kv_write_random_sequence::body()-kv_write_transaction randomization failed")
      // Send the transaction to the kv_write_driver_bfm via the sequencer and kv_write_driver.
      finish_item(req);
      `uvm_info("SEQ", {"Response:",req.convert2string()},UVM_MEDIUM)

  endtask

endclass: kv_write_random_sequence

// pragma uvmf custom external begin
// pragma uvmf custom external end

