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
// This file contains the UVM register adapter for the pv_write interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import pv_reg_adapter_functions_pkg::*;
class pv_write2reg_adapter #(
      string PV_WRITE_REQUESTOR = "SHA512"
      )
 extends uvm_reg_adapter;

  `uvm_object_param_utils( pv_write2reg_adapter #(
                           PV_WRITE_REQUESTOR
                           )
)
  
  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //--------------------------------------------------------------------
  // new
  //--------------------------------------------------------------------
  function new (string name = "pv_write2reg_adapter" );
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

    pv_write_transaction #(
                    .PV_WRITE_REQUESTOR(PV_WRITE_REQUESTOR)
                    )
 trans_h = pv_write_transaction #(
                             .PV_WRITE_REQUESTOR(PV_WRITE_REQUESTOR)
                             )
::type_id::create("trans_h");
    
    // pragma uvmf custom reg2bus begin
    // UVMF_CHANGE_ME : Fill in the reg2bus adapter mapping registe fields to protocol fields.
    uvm_reg_addr_t wr_addr;
    reg [PV_ENTRY_ADDR_W-1:0] wr_entry;
    reg [PV_ENTRY_SIZE_WIDTH-1:0] wr_offset;

    //Calculate PV entry and offset based on reg model address
    wr_addr = rw.addr;
    {wr_offset, wr_entry} = convert_addr_to_pv(wr_addr);
    
    trans_h.write_en = (rw.kind == UVM_WRITE);
    trans_h.write_entry = wr_entry;
    trans_h.write_offset = wr_offset;
    trans_h.write_data = rw.data;
    
    // pragma uvmf custom reg2bus end
    
    // Return the adapted transaction
    return trans_h;

  endfunction: reg2bus

  //--------------------------------------------------------------------
  // bus2reg
  //--------------------------------------------------------------------
  virtual function void bus2reg(uvm_sequence_item bus_item,
                                ref uvm_reg_bus_op rw);
    pv_write_transaction #(
        .PV_WRITE_REQUESTOR(PV_WRITE_REQUESTOR)
        )
 trans_h;

    reg [PV_ENTRY_ADDR_W-1:0] wr_entry;
    reg [PV_ENTRY_SIZE_WIDTH-1:0] wr_offset;

    if (!$cast(trans_h, bus_item)) begin
      `uvm_fatal("ADAPT","Provided bus_item is not of the correct type")
      return;
    end
    // pragma uvmf custom bus2reg begin
    // UVMF_CHANGE_ME : Fill in the bus2reg adapter mapping protocol fields to register fields.
    wr_entry = trans_h.write_entry;
    wr_offset = trans_h.write_offset;

    rw.kind = UVM_WRITE;
    rw.addr = convert_pv_to_addr({wr_offset, wr_entry}); 
    rw.data = trans_h.write_data;
    // pragma uvmf custom bus2reg end

  endfunction: bus2reg

endclass : pv_write2reg_adapter

// pragma uvmf custom external begin
// pragma uvmf custom external end

