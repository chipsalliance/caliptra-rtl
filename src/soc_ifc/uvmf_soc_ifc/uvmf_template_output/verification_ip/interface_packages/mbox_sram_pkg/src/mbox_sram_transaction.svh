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
// DESCRIPTION: This class defines the variables required for an mbox_sram
//    transaction.  Class variables to be displayed in waveform transaction
//    viewing are added to the transaction viewing stream in the add_to_wave
//    function.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class mbox_sram_transaction  extends uvmf_transaction_base;

  `uvm_object_utils( mbox_sram_transaction )

  rand bit is_read ;
  rand bit [MBOX_ADDR_W-1:0] address ;
  rand bit [MBOX_DATA_W-1:0] data ;
  bit [MBOX_ECC_DATA_W-1:0] data_ecc ;
  rand bit ecc_single_bit_error ;
  rand bit ecc_double_bit_error ;

  //Constraints for the transaction variables:

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //*******************************************************************
  //*******************************************************************
  // Macros that define structs and associated functions are
  // located in mbox_sram_macros.svh

  //*******************************************************************
  // Monitor macro used by mbox_sram_monitor and mbox_sram_monitor_bfm
  // This struct is defined in mbox_sram_macros.svh
  `mbox_sram_MONITOR_STRUCT
    mbox_sram_monitor_s mbox_sram_monitor_struct;
  //*******************************************************************
  // FUNCTION: to_monitor_struct()
  // This function packs transaction variables into a mbox_sram_monitor_s
  // structure.  The function returns the handle to the mbox_sram_monitor_struct.
  // This function is defined in mbox_sram_macros.svh
  `mbox_sram_TO_MONITOR_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_monitor_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in mbox_sram_macros.svh
  `mbox_sram_FROM_MONITOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Initiator macro used by mbox_sram_driver and mbox_sram_driver_bfm
  // to communicate initiator driven data to mbox_sram_driver_bfm.
  // This struct is defined in mbox_sram_macros.svh
  `mbox_sram_INITIATOR_STRUCT
    mbox_sram_initiator_s mbox_sram_initiator_struct;
  //*******************************************************************
  // FUNCTION: to_initiator_struct()
  // This function packs transaction variables into a mbox_sram_initiator_s
  // structure.  The function returns the handle to the mbox_sram_initiator_struct.
  // This function is defined in mbox_sram_macros.svh
  `mbox_sram_TO_INITIATOR_STRUCT_FUNCTION  
  //*******************************************************************
  // FUNCTION: from_initiator_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in mbox_sram_macros.svh
  `mbox_sram_FROM_INITIATOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Responder macro used by mbox_sram_driver and mbox_sram_driver_bfm
  // to communicate Responder driven data to mbox_sram_driver_bfm.
  // This struct is defined in mbox_sram_macros.svh
  `mbox_sram_RESPONDER_STRUCT
    mbox_sram_responder_s mbox_sram_responder_struct;
  //*******************************************************************
  // FUNCTION: to_responder_struct()
  // This function packs transaction variables into a mbox_sram_responder_s
  // structure.  The function returns the handle to the mbox_sram_responder_struct.
  // This function is defined in mbox_sram_macros.svh
  `mbox_sram_TO_RESPONDER_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_responder_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in mbox_sram_macros.svh
  `mbox_sram_FROM_RESPONDER_STRUCT_FUNCTION 
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
    return $sformatf("is_read:0x%x address:0x%x data:0x%x data_ecc:0x%x ecc_single_bit_error:0x%x ecc_double_bit_error:0x%x ",is_read,address,data,data_ecc,ecc_single_bit_error,ecc_double_bit_error);
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
    mbox_sram_transaction  RHS;
    if (!$cast(RHS,rhs)) return 0;
    // pragma uvmf custom do_compare begin
    // UVMF_CHANGE_ME : Eliminate comparison of variables not to be used for compare
    return (super.do_compare(rhs,comparer)
            &&(this.is_read == RHS.is_read)
            &&(this.address == RHS.address)
            &&(this.data == RHS.data)
            &&(this.data_ecc == RHS.data_ecc)
            &&(this.ecc_single_bit_error == RHS.ecc_single_bit_error)
            &&(this.ecc_double_bit_error == RHS.ecc_double_bit_error)
            );
    // pragma uvmf custom do_compare end
  endfunction

  //*******************************************************************
  // FUNCTION: do_copy()
  // This function is automatically called when the .copy() function
  // is called on this class.
  //
  virtual function void do_copy (uvm_object rhs);
    mbox_sram_transaction  RHS;
    assert($cast(RHS,rhs));
    // pragma uvmf custom do_copy begin
    super.do_copy(rhs);
    this.is_read = RHS.is_read;
    this.address = RHS.address;
    this.data = RHS.data;
    this.data_ecc = RHS.data_ecc;
    this.ecc_single_bit_error = RHS.ecc_single_bit_error;
    this.ecc_double_bit_error = RHS.ecc_double_bit_error;
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
      transaction_view_h = $begin_transaction(transaction_viewing_stream_h,"mbox_sram_transaction",start_time);
    end
    super.add_to_wave(transaction_view_h);
    // pragma uvmf custom add_to_wave begin
    // UVMF_CHANGE_ME : Color can be applied to transaction entries based on content, example below
    // case()
    //   1 : $add_color(transaction_view_h,"red");
    //   default : $add_color(transaction_view_h,"grey");
    // endcase
    // UVMF_CHANGE_ME : Eliminate transaction variables not wanted in transaction viewing in the waveform viewer
    $add_attribute(transaction_view_h,is_read,"is_read");
    $add_attribute(transaction_view_h,address,"address");
    $add_attribute(transaction_view_h,data,"data");
    $add_attribute(transaction_view_h,data_ecc,"data_ecc");
    $add_attribute(transaction_view_h,ecc_single_bit_error,"ecc_single_bit_error");
    $add_attribute(transaction_view_h,ecc_double_bit_error,"ecc_double_bit_error");
    // pragma uvmf custom add_to_wave end
    $end_transaction(transaction_view_h,end_time);
    $free_transaction(transaction_view_h);
    `endif // QUESTA
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

