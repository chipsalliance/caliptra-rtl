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
// This sequence constructs and randomizes a kv_read_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class kv_read_key_entry_sequence #(
    string KV_READ_REQUESTOR = "HMAC_KEY"
    )
extends kv_read_sequence_base #(
    .KV_READ_REQUESTOR(KV_READ_REQUESTOR)
    );

`uvm_object_param_utils( kv_read_key_entry_sequence #(
                         KV_READ_REQUESTOR
                         ))

// pragma uvmf custom class_item_additional begin
  logic [KV_ENTRY_ADDR_W-1:0] local_read_entry;
  logic [KV_ENTRY_SIZE_W-1:0] local_read_offset;
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
    int entry;
    int offset;

    // Construct the transaction
    //for(entry=0; entry<8; entry++) begin
      req=kv_read_transaction#(
            .KV_READ_REQUESTOR(KV_READ_REQUESTOR)
            )::type_id::create("req");
      
            uvm_config_db#(reg [KV_ENTRY_ADDR_W-1:0])::get(null, get_full_name(), "local_read_entry", local_read_entry);
            uvm_config_db#(reg [KV_ENTRY_SIZE_W-1:0])::get(null, get_full_name(), "local_read_offset", local_read_offset);

            if((local_read_entry !== 'x) && (local_read_offset !== 'x)) begin
              //Use read_entry and read_offset passed in from top level sequence
              `uvm_do_with(req, {
                req.read_entry == local_read_entry;
                req.read_offset == local_read_offset;
              })
            end
            else if((local_read_entry !== 'x)) begin
              //Use read entry passed in from top level sequence
              `uvm_do_with(req, {
              req.read_entry == local_read_entry;
            })
            end
            else if ((local_read_offset !== 'x)) begin
              //Use read offset passed in from top level sequence
              `uvm_do_with(req, {
              req.read_offset == local_read_offset;
              })
            end
            else begin
              //Use randomized transaction read entry
              `uvm_do(req);
            end

endtask

endclass: kv_read_key_entry_sequence

// pragma uvmf custom external begin
// pragma uvmf custom external end

