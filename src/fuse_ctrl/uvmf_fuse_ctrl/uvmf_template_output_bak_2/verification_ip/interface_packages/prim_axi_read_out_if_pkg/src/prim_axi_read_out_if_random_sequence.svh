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
// This sequences randomizes the prim_axi_read_out_if transaction and sends it 
// to the UVM driver.
//
// This sequence constructs and randomizes a prim_axi_read_out_if_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class prim_axi_read_out_if_random_sequence #(
      int AW = 32,
      int DW = 32,
      int IW = 3,
      int UW = 32
      )

  extends prim_axi_read_out_if_sequence_base #(
      .AW(AW),
      .DW(DW),
      .IW(IW),
      .UW(UW)
      )
;

  `uvm_object_param_utils( prim_axi_read_out_if_random_sequence #(
                           AW,
                           DW,
                           IW,
                           UW
                           )
)

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
      req=prim_axi_read_out_if_transaction#(
                .AW(AW),
                .DW(DW),
                .IW(IW),
                .UW(UW)
                )
::type_id::create("req");
      start_item(req);
      // Randomize the transaction
      if(!req.randomize()) `uvm_fatal("SEQ", "prim_axi_read_out_if_random_sequence::body()-prim_axi_read_out_if_transaction randomization failed")
      // Send the transaction to the prim_axi_read_out_if_driver_bfm via the sequencer and prim_axi_read_out_if_driver.
      finish_item(req);
      `uvm_info("SEQ", {"Response:",req.convert2string()},UVM_MEDIUM)

  endtask

endclass: prim_axi_read_out_if_random_sequence

// pragma uvmf custom external begin
// pragma uvmf custom external end

