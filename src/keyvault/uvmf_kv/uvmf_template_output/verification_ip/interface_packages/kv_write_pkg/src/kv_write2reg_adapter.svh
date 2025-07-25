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
// This file contains the UVM register adapter for the kv_write interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
//`include "environment_packages/kv_env_pkg/registers/kv_reg_adapter_functions.sv"
import kv_reg_adapter_functions_pkg::*;
class kv_write2reg_adapter #(
      string KV_WRITE_REQUESTOR = "HMAC"
      )
 extends uvm_reg_adapter;

  `uvm_object_param_utils( kv_write2reg_adapter #(
                           KV_WRITE_REQUESTOR
                           )
)
  
  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //--------------------------------------------------------------------
  // new
  //--------------------------------------------------------------------
  function new (string name = "kv_write2reg_adapter" );
    super.new(name);
    // pragma uvmf custom new begin
    // UVMF_CHANGE_ME : Configure the adapter regarding byte enables and provides response.

    // Does the protocol the Agent is modeling support byte enables?
    // 0 = NO
    // 1 = YES
    supports_byte_enable = 0;

    // Does the Agent's Driver provide separate response sequence items?
    // i.e. Does the driver call seq_item_port.put() 
    // and do the sequences call get_response()?
    // 0 = NO
    // 1 = YES
    provides_responses = 0;
    // pragma uvmf custom new end

  endfunction: new

  //--------------------------------------------------------------------
  // reg2bus
  //--------------------------------------------------------------------
  virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);

    kv_write_transaction #(
                    .KV_WRITE_REQUESTOR(KV_WRITE_REQUESTOR)
                    )
 trans_h = kv_write_transaction #(
                             .KV_WRITE_REQUESTOR(KV_WRITE_REQUESTOR)
                             )
::type_id::create("trans_h");
    
    // pragma uvmf custom reg2bus begin
    // UVMF_CHANGE_ME : Fill in the reg2bus adapter mapping registe fields to protocol fields.

    uvm_reg_addr_t wr_addr;
    reg [KV_ENTRY_ADDR_W-1:0] wr_entry;
    reg [KV_ENTRY_SIZE_W-1:0] wr_offset;

    //Calculate KV entry and offset based on reg model address
    wr_addr = rw.addr;
    {wr_offset, wr_entry} = convert_addr_to_kv(wr_addr);
    //Adapt the following for your sequence item type
    // trans_h.op = (rw.kind == UVM_READ) ? WB_READ : WB_WRITE;
    //Copy over address
    // trans_h.addr = rw.addr;
    trans_h.write_en = (rw.kind == UVM_WRITE);
    trans_h.write_entry = wr_entry;
    trans_h.write_offset = wr_offset;
    trans_h.write_data = rw.data;
    trans_h.write_dest_valid = 'hFF;
    //Copy over write data
    // trans_h.data = rw.data;

    // pragma uvmf custom reg2bus end
    
    // Return the adapted transaction
    return trans_h;

  endfunction: reg2bus

  //--------------------------------------------------------------------
  // bus2reg
  //--------------------------------------------------------------------
  virtual function void bus2reg(uvm_sequence_item bus_item,
                                ref uvm_reg_bus_op rw);
    kv_write_transaction #(
        .KV_WRITE_REQUESTOR(KV_WRITE_REQUESTOR)
        )
 trans_h;

    reg [KV_ENTRY_ADDR_W-1:0] wr_entry;
    reg [KV_ENTRY_SIZE_W-1:0] wr_offset;

    if (!$cast(trans_h, bus_item)) begin
      `uvm_fatal("ADAPT","Provided bus_item is not of the correct type")
      return;
    end
    // pragma uvmf custom bus2reg begin
    // UVMF_CHANGE_ME : Fill in the bus2reg adapter mapping protocol fields to register fields.
    wr_entry = trans_h.write_entry;
    wr_offset = trans_h.write_offset;
    //Adapt the following for your sequence item type
    //Copy over instruction type 
    // rw.kind = (trans_h.op == WB_WRITE) ? UVM_WRITE : UVM_READ;
    rw.kind = UVM_WRITE;
    //Copy over address
    // rw.addr = trans_h.addr;
    rw.addr = convert_kv_to_addr({wr_offset, wr_entry}); 
    //Copy over read data
    rw.data = trans_h.write_data; //Note, dest_valid always 'hFF in kv_reg_predictor
    // rw.data = trans_h.data;
    //Check for errors on the bus and return UVM_NOT_OK if there is an error
    // rw.status = UVM_IS_OK;
    // pragma uvmf custom bus2reg end

  endfunction: bus2reg

endclass : kv_write2reg_adapter

// pragma uvmf custom external begin


// pragma uvmf custom external end

