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
// DESCRIPTION: This class defines the variables required for an ss_mode_status
//    transaction.  Class variables to be displayed in waveform transaction
//    viewing are added to the transaction viewing stream in the add_to_wave
//    function.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class ss_mode_status_transaction  extends uvmf_transaction_base;

  `uvm_object_utils( ss_mode_status_transaction )

  bit cptra_ss_debug_intent ;
  bit ss_dbg_manuf_enable ;
  bit [63:0] ss_soc_dbg_unlock_level ;
  bit [127:0] ss_generic_fw_exec_ctrl ;

  //Constraints for the transaction variables:

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //*******************************************************************
  //*******************************************************************
  // Macros that define structs and associated functions are
  // located in ss_mode_status_macros.svh

  //*******************************************************************
  // Monitor macro used by ss_mode_status_monitor and ss_mode_status_monitor_bfm
  // This struct is defined in ss_mode_status_macros.svh
  `ss_mode_status_MONITOR_STRUCT
    ss_mode_status_monitor_s ss_mode_status_monitor_struct;
  //*******************************************************************
  // FUNCTION: to_monitor_struct()
  // This function packs transaction variables into a ss_mode_status_monitor_s
  // structure.  The function returns the handle to the ss_mode_status_monitor_struct.
  // This function is defined in ss_mode_status_macros.svh
  `ss_mode_status_TO_MONITOR_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_monitor_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in ss_mode_status_macros.svh
  `ss_mode_status_FROM_MONITOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Initiator macro used by ss_mode_status_driver and ss_mode_status_driver_bfm
  // to communicate initiator driven data to ss_mode_status_driver_bfm.
  // This struct is defined in ss_mode_status_macros.svh
  `ss_mode_status_INITIATOR_STRUCT
    ss_mode_status_initiator_s ss_mode_status_initiator_struct;
  //*******************************************************************
  // FUNCTION: to_initiator_struct()
  // This function packs transaction variables into a ss_mode_status_initiator_s
  // structure.  The function returns the handle to the ss_mode_status_initiator_struct.
  // This function is defined in ss_mode_status_macros.svh
  `ss_mode_status_TO_INITIATOR_STRUCT_FUNCTION  
  //*******************************************************************
  // FUNCTION: from_initiator_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in ss_mode_status_macros.svh
  `ss_mode_status_FROM_INITIATOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Responder macro used by ss_mode_status_driver and ss_mode_status_driver_bfm
  // to communicate Responder driven data to ss_mode_status_driver_bfm.
  // This struct is defined in ss_mode_status_macros.svh
  `ss_mode_status_RESPONDER_STRUCT
    ss_mode_status_responder_s ss_mode_status_responder_struct;
  //*******************************************************************
  // FUNCTION: to_responder_struct()
  // This function packs transaction variables into a ss_mode_status_responder_s
  // structure.  The function returns the handle to the ss_mode_status_responder_struct.
  // This function is defined in ss_mode_status_macros.svh
  `ss_mode_status_TO_RESPONDER_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_responder_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in ss_mode_status_macros.svh
  `ss_mode_status_FROM_RESPONDER_STRUCT_FUNCTION 
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
    return $sformatf("cptra_ss_debug_intent:0x%x ss_dbg_manuf_enable:0x%x ss_soc_dbg_unlock_level:0x%x ss_generic_fw_exec_ctrl:0x%x %s",cptra_ss_debug_intent,ss_dbg_manuf_enable,ss_soc_dbg_unlock_level,ss_generic_fw_exec_ctrl,super.convert2string());
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
    ss_mode_status_transaction  RHS;
    if (!$cast(RHS,rhs)) return 0;
    // pragma uvmf custom do_compare begin
    // UVMF_CHANGE_ME : Eliminate comparison of variables not to be used for compare
    return (super.do_compare(rhs,comparer)
            &&(this.cptra_ss_debug_intent == RHS.cptra_ss_debug_intent)
            &&(this.ss_dbg_manuf_enable == RHS.ss_dbg_manuf_enable)
            &&(this.ss_soc_dbg_unlock_level == RHS.ss_soc_dbg_unlock_level)
            &&(this.ss_generic_fw_exec_ctrl == RHS.ss_generic_fw_exec_ctrl)
            );
    // pragma uvmf custom do_compare end
  endfunction

  //*******************************************************************
  // FUNCTION: do_copy()
  // This function is automatically called when the .copy() function
  // is called on this class.
  //
  virtual function void do_copy (uvm_object rhs);
    ss_mode_status_transaction  RHS;
    assert($cast(RHS,rhs));
    // pragma uvmf custom do_copy begin
    super.do_copy(rhs);
    this.cptra_ss_debug_intent = RHS.cptra_ss_debug_intent;
    this.ss_dbg_manuf_enable = RHS.ss_dbg_manuf_enable;
    this.ss_soc_dbg_unlock_level = RHS.ss_soc_dbg_unlock_level;
    this.ss_generic_fw_exec_ctrl = RHS.ss_generic_fw_exec_ctrl;
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
      transaction_view_h = $begin_transaction(transaction_viewing_stream_h,"ss_mode_status_transaction",start_time);
    end
    super.add_to_wave(transaction_view_h);
    // pragma uvmf custom add_to_wave begin
    // UVMF_CHANGE_ME : Color can be applied to transaction entries based on content, example below
    // case()
    //   1 : $add_color(transaction_view_h,"red");
    //   default : $add_color(transaction_view_h,"grey");
    // endcase
    // UVMF_CHANGE_ME : Eliminate transaction variables not wanted in transaction viewing in the waveform viewer
    $add_attribute(transaction_view_h,cptra_ss_debug_intent,"cptra_ss_debug_intent");
    $add_attribute(transaction_view_h,ss_dbg_manuf_enable,"ss_dbg_manuf_enable");
    $add_attribute(transaction_view_h,ss_soc_dbg_unlock_level,"ss_soc_dbg_unlock_level");
    $add_attribute(transaction_view_h,ss_generic_fw_exec_ctrl,"ss_generic_fw_exec_ctrl");
    // pragma uvmf custom add_to_wave end
    $end_transaction(transaction_view_h,end_time);
    $free_transaction(transaction_view_h);
    `endif // QUESTA
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

