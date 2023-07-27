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
// This file contains the class used as the base class for all sequences
// for this interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class mbox_sram_sequence_base    extends uvmf_sequence_base #(
                             .REQ(mbox_sram_transaction  ),
                             .RSP(mbox_sram_transaction  ));

  `uvm_object_utils( mbox_sram_sequence_base )

  // variables
  typedef mbox_sram_transaction  mbox_sram_transaction_req_t;
  mbox_sram_transaction_req_t req;
  typedef mbox_sram_transaction  mbox_sram_transaction_rsp_t;
  mbox_sram_transaction_rsp_t rsp;

  // Event for identifying when a response was received from the sequencer
  event new_rsp;


  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  // TASK : get_responses()
  // This task recursively gets sequence item responses from the sequencer.
  //
  virtual task get_responses();
    fork
      forever begin
        // Block until new rsp available
        get_response(rsp);
        // New rsp received.  Indicate to sequence using event.
        ->new_rsp;
        // Display the received response transaction
        `uvm_info("SEQ", {"New response transaction:",rsp.convert2string()}, UVM_MEDIUM)
      end
    join_none
  endtask

  // ****************************************************************************
  // TASK : pre_body()
  // This task is called automatically when start is called with call_pre_post set to 1 (default).
  // By calling get_responses() within pre_body() any derived sequences are automatically 
  // processing response transactions. Only un-comment this call to get_responses() if you
  // have configured the interface driver to utilize the response transaction path by setting
  // the configuration variable "return_transaction_response" to 1. Otherwise it is possible
  // to impact runtime performance and memory utilization.
  //
  virtual task pre_body();
    // pragma uvmf custom pre_body begin
    get_responses();
    // pragma uvmf custom pre_body end
  endtask

  // ****************************************************************************
  // TASK : body()
  // This task is called automatically when start is called.  This sequence sends
  // a req sequence item to the sequencer identified as an argument in the call
  // to start.
  //
  virtual task body();
    // pragma uvmf custom body begin
  	start_item(req);
  	finish_item(req);
    // pragma uvmf custom body end
  endtask

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new( string name ="");
    super.new( name );
    // pragma uvmf custom new begin
    req = mbox_sram_transaction_req_t::type_id::create("req");
    rsp = mbox_sram_transaction_rsp_t::type_id::create("rsp");
    // pragma uvmf custom new end
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

