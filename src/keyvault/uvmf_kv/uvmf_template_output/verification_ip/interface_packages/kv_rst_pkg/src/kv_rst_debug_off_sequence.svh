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
class kv_rst_debug_off_sequence extends kv_rst_sequence_base;

    `uvm_object_utils( kv_rst_debug_off_sequence )

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

    // Deassert debug mode
    req=kv_rst_transaction::type_id::create("rst_req");
    start_item(req);
    // Randomize the transaction
    if(!req.randomize()) `uvm_fatal("KV_RST_DEBUG", "kv_rst_debug_off_sequence::body()-kv_rst_transaction randomization failed")
    `uvm_info("KV_RST_DEBUG", "Asserting reset, pwrgood high", UVM_MEDIUM)
    req.set_pwrgood = 1'b1;
    req.assert_rst = 1'b0;
    req.assert_core_rst = 1'b0;
    req.debug_mode = 1'b0;
    req.scan_mode = 1'b0;
    
    finish_item(req);
    `uvm_info("KV_RST_DEBUG", {"Response:",req.convert2string()},UVM_MEDIUM)

    

endtask

endclass