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
// This sequence constructs and randomizes a pv_write_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class pv_write_pcr_entry_sequence #(
    string PV_WRITE_REQUESTOR = "SHA512"
    )
extends pv_write_sequence_base #(
    .PV_WRITE_REQUESTOR(PV_WRITE_REQUESTOR)
    );

`uvm_object_param_utils( pv_write_pcr_entry_sequence #(
                         PV_WRITE_REQUESTOR
                         ))

// pragma uvmf custom class_item_additional begin
  logic [PV_ENTRY_ADDR_W-1:0] local_write_entry;
  logic [PV_ENTRY_SIZE_WIDTH-1:0] local_write_offset;
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
      req=pv_write_transaction#(
            .PV_WRITE_REQUESTOR(PV_WRITE_REQUESTOR)
            )::type_id::create("req");
      
      uvm_config_db#(reg [PV_ENTRY_ADDR_W-1:0])::get(null, get_full_name(), "local_write_entry", local_write_entry);
      uvm_config_db#(reg [PV_ENTRY_SIZE_WIDTH-1:0])::get(null, get_full_name(), "local_write_offset", local_write_offset);

      if((local_write_entry !== 'x) && (local_write_offset !== 'x)) begin
        //Use write_entry and write_offset passed in from top level sequence
        `uvm_do_with(req, {
          req.write_entry == local_write_entry;
          req.write_offset == local_write_offset;
        })
      end
      else if((local_write_entry !== 'x)) begin
        //Use write entry passed in from top level sequence
        `uvm_do_with(req, {
        req.write_entry == local_write_entry;
      })
      end
      else if ((local_write_offset !== 'x)) begin
        //Use write offset passed in from top level sequence
        `uvm_do_with(req, {
        req.write_offset == local_write_offset;
        })
      end
      else begin
        //Use randomized transaction write entry
        `uvm_do(req);
      end


endtask

endclass: pv_write_pcr_entry_sequence

// pragma uvmf custom external begin
// pragma uvmf custom external end

