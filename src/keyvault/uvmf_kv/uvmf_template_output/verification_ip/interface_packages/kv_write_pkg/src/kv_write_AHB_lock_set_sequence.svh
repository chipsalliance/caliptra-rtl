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
//
// This sequence constructs and randomizes a kv_write_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class kv_write_AHB_lock_set_sequence #(
    string KV_WRITE_REQUESTOR = "HMAC"
    )
extends kv_write_sequence_base #(
    .KV_WRITE_REQUESTOR(KV_WRITE_REQUESTOR)
    );

`uvm_object_param_utils( kv_write_AHB_lock_set_sequence #(
                         KV_WRITE_REQUESTOR
                         ))

// pragma uvmf custom class_item_additional begin
// pragma uvmf custom class_item_additional end
rand reg [KV_ENTRY_ADDR_W-1:0] local_write_entry;
reg [KV_ENTRY_ADDR_W-1:0] write_entry;
rand reg [1:0] lock_data;
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
    int entry;
    uvm_status_e sts;
    reg_model = configuration.kv_rm;

    // Construct the transaction
    for(entry = 0; entry < KV_NUM_KEYS; entry++) begin
      lock_data = $urandom_range(1,3); //Can set one of lock_wr, lock_use or both together
      reg_model.kv_reg_rm.KEY_CTRL[entry].write(sts, lock_data, UVM_FRONTDOOR, reg_model.kv_AHB_map, this);
      //`uvm_info("KV WR RD", $sformatf("Status = %x, Read data = 0x%x", sts, rd_data), UVM_MEDIUM)
      assert(sts == UVM_IS_OK) else `uvm_error("AHB_LOCK_SET", $sformatf("Failed when writing to KEY_CTRL[%d]",entry))
    end



endtask

endclass: kv_write_AHB_lock_set_sequence

// pragma uvmf custom external begin
// pragma uvmf custom external end

