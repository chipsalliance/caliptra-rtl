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
// This file contains the UVM register adapter for the pv_read interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
import pv_reg_adapter_functions_pkg::*;
class pv_read2reg_adapter #(
      string PV_READ_REQUESTOR = "SHA512_BLOCK"
      )
 extends uvm_reg_adapter;

  `uvm_object_param_utils( pv_read2reg_adapter #(
                           PV_READ_REQUESTOR
                           )
)
  
  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //--------------------------------------------------------------------
  // new
  //--------------------------------------------------------------------
  function new (string name = "pv_read2reg_adapter" );
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

    pv_read_transaction #(
                    .PV_READ_REQUESTOR(PV_READ_REQUESTOR)
                    )
 trans_h = pv_read_transaction #(
                             .PV_READ_REQUESTOR(PV_READ_REQUESTOR)
                             )
::type_id::create("trans_h");
    
    // pragma uvmf custom reg2bus begin
    // UVMF_CHANGE_ME : Fill in the reg2bus adapter mapping registe fields to protocol fields.

    uvm_reg_addr_t rd_addr;
    reg [PV_ENTRY_ADDR_W-1:0] rd_entry;
    reg [PV_ENTRY_SIZE_WIDTH-1:0] rd_offset;

    //Calculate PV entry and offset based on reg model address
    rd_addr = rw.addr;

    {rd_offset, rd_entry} = convert_addr_to_pv(rd_addr);

    //Construct txn
    trans_h.read_entry = rd_entry;
    trans_h.read_offset = rd_offset;
    trans_h.error = 0;
    trans_h.last = 0; //TODO - is this ok?
    trans_h.read_data = rw.data;

    // pragma uvmf custom reg2bus end
    
    // Return the adapted transaction
    return trans_h;

  endfunction: reg2bus

  //--------------------------------------------------------------------
  // bus2reg
  //--------------------------------------------------------------------
  virtual function void bus2reg(uvm_sequence_item bus_item,
                                ref uvm_reg_bus_op rw);
    pv_read_transaction #(
        .PV_READ_REQUESTOR(PV_READ_REQUESTOR)
        )
 trans_h;
    if (!$cast(trans_h, bus_item)) begin
      `uvm_fatal("ADAPT","Provided bus_item is not of the correct type")
      return;
    end
    // pragma uvmf custom bus2reg begin
    // UVMF_CHANGE_ME : Fill in the bus2reg adapter mapping protocol fields to register fields.
    rw.kind = UVM_READ;
    rw.addr = convert_pv_to_addr({trans_h.read_offset, trans_h.read_entry});
    rw.data = trans_h.read_data;
    // pragma uvmf custom bus2reg end

  endfunction: bus2reg

endclass : pv_read2reg_adapter

// pragma uvmf custom external begin
// pragma uvmf custom external end

