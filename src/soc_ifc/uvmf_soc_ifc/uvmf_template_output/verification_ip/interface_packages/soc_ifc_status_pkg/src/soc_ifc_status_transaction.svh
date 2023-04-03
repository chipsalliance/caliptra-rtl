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
// DESCRIPTION: This class defines the variables required for an soc_ifc_status
//    transaction.  Class variables to be displayed in waveform transaction
//    viewing are added to the transaction viewing stream in the add_to_wave
//    function.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_status_transaction  extends uvmf_transaction_base;

  `uvm_object_utils( soc_ifc_status_transaction )

  bit ready_for_fuses ;
  bit ready_for_fw_push ;
  bit ready_for_runtime ;
  bit mailbox_data_avail ;
  bit mailbox_flow_done ;
  bit cptra_error_fatal_intr_pending ;
  bit cptra_error_non_fatal_intr_pending ;
  bit trng_req_pending ;
  bit [63:0] generic_output_val ;

  //Constraints for the transaction variables:

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //*******************************************************************
  //*******************************************************************
  // Macros that define structs and associated functions are
  // located in soc_ifc_status_macros.svh

  //*******************************************************************
  // Monitor macro used by soc_ifc_status_monitor and soc_ifc_status_monitor_bfm
  // This struct is defined in soc_ifc_status_macros.svh
  `soc_ifc_status_MONITOR_STRUCT
    soc_ifc_status_monitor_s soc_ifc_status_monitor_struct;
  //*******************************************************************
  // FUNCTION: to_monitor_struct()
  // This function packs transaction variables into a soc_ifc_status_monitor_s
  // structure.  The function returns the handle to the soc_ifc_status_monitor_struct.
  // This function is defined in soc_ifc_status_macros.svh
  `soc_ifc_status_TO_MONITOR_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_monitor_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in soc_ifc_status_macros.svh
  `soc_ifc_status_FROM_MONITOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Initiator macro used by soc_ifc_status_driver and soc_ifc_status_driver_bfm
  // to communicate initiator driven data to soc_ifc_status_driver_bfm.
  // This struct is defined in soc_ifc_status_macros.svh
  `soc_ifc_status_INITIATOR_STRUCT
    soc_ifc_status_initiator_s soc_ifc_status_initiator_struct;
  //*******************************************************************
  // FUNCTION: to_initiator_struct()
  // This function packs transaction variables into a soc_ifc_status_initiator_s
  // structure.  The function returns the handle to the soc_ifc_status_initiator_struct.
  // This function is defined in soc_ifc_status_macros.svh
  `soc_ifc_status_TO_INITIATOR_STRUCT_FUNCTION  
  //*******************************************************************
  // FUNCTION: from_initiator_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in soc_ifc_status_macros.svh
  `soc_ifc_status_FROM_INITIATOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Responder macro used by soc_ifc_status_driver and soc_ifc_status_driver_bfm
  // to communicate Responder driven data to soc_ifc_status_driver_bfm.
  // This struct is defined in soc_ifc_status_macros.svh
  `soc_ifc_status_RESPONDER_STRUCT
    soc_ifc_status_responder_s soc_ifc_status_responder_struct;
  //*******************************************************************
  // FUNCTION: to_responder_struct()
  // This function packs transaction variables into a soc_ifc_status_responder_s
  // structure.  The function returns the handle to the soc_ifc_status_responder_struct.
  // This function is defined in soc_ifc_status_macros.svh
  `soc_ifc_status_TO_RESPONDER_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_responder_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in soc_ifc_status_macros.svh
  `soc_ifc_status_FROM_RESPONDER_STRUCT_FUNCTION 
  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new( string name = "" );
    super.new( name );
  endfunction

  // ****************************************************************************
  // FUNCTION: convert2string()
  // This function converts all variables in this class to a single string for 
  // logfile reporting.
  //
  virtual function string convert2string();
    // pragma uvmf custom convert2string begin
    // UVMF_CHANGE_ME : Customize format if desired.
    return $sformatf("ready_for_fuses:0x%x ready_for_fw_push:0x%x ready_for_runtime:0x%x mailbox_data_avail:0x%x mailbox_flow_done:0x%x cptra_error_fatal_intr_pending:0x%x cptra_error_non_fatal_intr_pending:0x%x trng_req_pending:0x%x generic_output_val:0x%x ",ready_for_fuses,ready_for_fw_push,ready_for_runtime,mailbox_data_avail,mailbox_flow_done,cptra_error_fatal_intr_pending,cptra_error_non_fatal_intr_pending,trng_req_pending,generic_output_val);
    // pragma uvmf custom convert2string end
  endfunction

  //*******************************************************************
  // FUNCTION: do_print()
  // This function is automatically called when the .print() function
  // is called on this class.
  //
  virtual function void do_print(uvm_printer printer);
    // pragma uvmf custom do_print begin
    // UVMF_CHANGE_ME : Current contents of do_print allows for the use of UVM 1.1d, 1.2 or P1800.2.
    // Update based on your own printing preference according to your preferred UVM version
    $display(convert2string());
    // pragma uvmf custom do_print end
  endfunction

  //*******************************************************************
  // FUNCTION: do_compare()
  // This function is automatically called when the .compare() function
  // is called on this class.
  //
  virtual function bit do_compare (uvm_object rhs, uvm_comparer comparer);
    soc_ifc_status_transaction  RHS;
    if (!$cast(RHS,rhs)) return 0;
    // pragma uvmf custom do_compare begin
    // UVMF_CHANGE_ME : Eliminate comparison of variables not to be used for compare
    return (super.do_compare(rhs,comparer)
            &&(this.ready_for_fuses == RHS.ready_for_fuses)
            &&(this.ready_for_fw_push == RHS.ready_for_fw_push)
            &&(this.ready_for_runtime == RHS.ready_for_runtime)
            &&(this.mailbox_data_avail == RHS.mailbox_data_avail)
            &&(this.mailbox_flow_done == RHS.mailbox_flow_done)
            &&(this.cptra_error_fatal_intr_pending == RHS.cptra_error_fatal_intr_pending)
            &&(this.cptra_error_non_fatal_intr_pending == RHS.cptra_error_non_fatal_intr_pending)
            &&(this.trng_req_pending == RHS.trng_req_pending)
            &&(this.generic_output_val == RHS.generic_output_val)
            );
    // pragma uvmf custom do_compare end
  endfunction

  //*******************************************************************
  // FUNCTION: do_copy()
  // This function is automatically called when the .copy() function
  // is called on this class.
  //
  virtual function void do_copy (uvm_object rhs);
    soc_ifc_status_transaction  RHS;
    assert($cast(RHS,rhs));
    // pragma uvmf custom do_copy begin
    super.do_copy(rhs);
    this.ready_for_fuses = RHS.ready_for_fuses;
    this.ready_for_fw_push = RHS.ready_for_fw_push;
    this.ready_for_runtime = RHS.ready_for_runtime;
    this.mailbox_data_avail = RHS.mailbox_data_avail;
    this.mailbox_flow_done = RHS.mailbox_flow_done;
    this.cptra_error_fatal_intr_pending     = RHS.cptra_error_fatal_intr_pending    ;
    this.cptra_error_non_fatal_intr_pending = RHS.cptra_error_non_fatal_intr_pending;
    this.trng_req_pending                   = RHS.trng_req_pending                  ;
    this.generic_output_val = RHS.generic_output_val;
    // pragma uvmf custom do_copy end
  endfunction

  // ****************************************************************************
  // FUNCTION: add_to_wave()
  // This function is used to display variables in this class in the waveform 
  // viewer.  The start_time and end_time variables must be set before this 
  // function is called.  If the start_time and end_time variables are not set
  // the transaction will be hidden at 0ns on the waveform display.
  // 
  virtual function void add_to_wave(int transaction_viewing_stream_h);
    `ifdef QUESTA
    if (transaction_view_h == 0) begin
      transaction_view_h = $begin_transaction(transaction_viewing_stream_h,"soc_ifc_status_transaction",start_time);
    end
    super.add_to_wave(transaction_view_h);
    // pragma uvmf custom add_to_wave begin
    // UVMF_CHANGE_ME : Color can be applied to transaction entries based on content, example below
    // case()
    //   1 : $add_color(transaction_view_h,"red");
    //   default : $add_color(transaction_view_h,"grey");
    // endcase
    // UVMF_CHANGE_ME : Eliminate transaction variables not wanted in transaction viewing in the waveform viewer
    $add_attribute(transaction_view_h,ready_for_fuses,"ready_for_fuses");
    $add_attribute(transaction_view_h,ready_for_fw_push,"ready_for_fw_push");
    $add_attribute(transaction_view_h,ready_for_runtime,"ready_for_runtime");
    $add_attribute(transaction_view_h,mailbox_data_avail,"mailbox_data_avail");
    $add_attribute(transaction_view_h,mailbox_flow_done,"mailbox_flow_done");
    $add_attribute(transaction_view_h,cptra_error_fatal_intr_pending    ,"cptra_error_fatal_intr_pending    ");
    $add_attribute(transaction_view_h,cptra_error_non_fatal_intr_pending,"cptra_error_non_fatal_intr_pending");
    $add_attribute(transaction_view_h,trng_req_pending                  ,"trng_req_pending                  ");
    $add_attribute(transaction_view_h,generic_output_val,"generic_output_val");
    // pragma uvmf custom add_to_wave end
    $end_transaction(transaction_view_h,end_time);
    $free_transaction(transaction_view_h);
    `endif // QUESTA
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

