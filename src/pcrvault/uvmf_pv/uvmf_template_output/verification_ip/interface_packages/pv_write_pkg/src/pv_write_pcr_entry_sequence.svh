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
  // Opt-in directed beats; the existing randomized/config-db path is unchanged.
  bit directed = 0;
  int unsigned beats = 1;
  logic [PV_ENTRY_ADDR_W-1:0] directed_write_entry;
  logic [PV_ENTRY_SIZE_WIDTH-1:0] directed_write_offset;
  logic [PV_DATA_W-1:0] directed_write_data;
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
// pragma uvmf custom body begin
    int entry;
    int offset;

    if (directed) begin
      if (beats == 0 || beats > 64 ||
          $isunknown({directed_write_entry, directed_write_offset}) ||
          directed_write_entry >= PV_NUM_PCR || directed_write_offset >= PV_NUM_DWORDS)
        `uvm_fatal("PV_DIRECTED_WRITE", "Invalid bounded PCR write")
      repeat (beats) begin
        req = pv_write_transaction#(.PV_WRITE_REQUESTOR(PV_WRITE_REQUESTOR))::type_id::create("req");
        start_item(req);
        req.write_en = 1'b1;
        req.write_entry = directed_write_entry;
        req.write_offset = directed_write_offset;
        req.write_data = directed_write_data;
        finish_item(req);
      end
      return;
    end

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

// pragma uvmf custom body end
endtask

endclass: pv_write_pcr_entry_sequence

// pragma uvmf custom external begin
// pragma uvmf custom external end
