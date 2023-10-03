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
// DESCRIPTION: This class defines the variables required for an soc_ifc_ctrl
//    transaction.  Class variables to be displayed in waveform transaction
//    viewing are added to the transaction viewing stream in the add_to_wave
//    function.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class soc_ifc_ctrl_transaction  extends uvmf_transaction_base;

  `uvm_object_utils( soc_ifc_ctrl_transaction )

  rand bit [`CLP_OBF_KEY_DWORDS-1:0] [31:0] cptra_obf_key_rand ;
  bit set_pwrgood ;
  bit assert_rst ;
  rand int unsigned wait_cycles ;
  rand security_state_t security_state ;
  rand bit set_bootfsm_breakpoint ;
  rand bit [63:0] generic_input_val ;

  //Constraints for the transaction variables:
  constraint wait_cycles_c { wait_cycles dist {[1:25] := 80, [25:100] := 15, [100:500] := 5}; }
  constraint generic_tie_zero_c { generic_input_val == 64'h0; }
  constraint debug_locked_c {security_state.debug_locked == 1'b1;} //reset sequence tied this off, doing it here instead
  constraint device_lifecycle_const_c { if (device_lifecycle_set_static) {security_state.device_lifecycle == device_lifecycle_static; } }
  
  //Match RTL constraint for latching bootfsm breakpoint
  //we'll never set bootfsm breakpoint unless we are in the appropriate debug/device lifecycle state to latch it in RTL
  constraint set_bootfsm_breakpoint_c { if ((security_state.debug_locked) & 
                                            ~((security_state.debug_locked) & (security_state.device_lifecycle == DEVICE_MANUFACTURING)))
                                            {set_bootfsm_breakpoint == 0;} 
                                          solve security_state before set_bootfsm_breakpoint; }

  // pragma uvmf custom class_item_additional begin
  static device_lifecycle_e device_lifecycle_static = 'X;
  static bit device_lifecycle_set_static = 1'b0;
  extern function void post_randomize();
  // pragma uvmf custom class_item_additional end

  //*******************************************************************
  //*******************************************************************
  // Macros that define structs and associated functions are
  // located in soc_ifc_ctrl_macros.svh

  //*******************************************************************
  // Monitor macro used by soc_ifc_ctrl_monitor and soc_ifc_ctrl_monitor_bfm
  // This struct is defined in soc_ifc_ctrl_macros.svh
  `soc_ifc_ctrl_MONITOR_STRUCT
    soc_ifc_ctrl_monitor_s soc_ifc_ctrl_monitor_struct;
  //*******************************************************************
  // FUNCTION: to_monitor_struct()
  // This function packs transaction variables into a soc_ifc_ctrl_monitor_s
  // structure.  The function returns the handle to the soc_ifc_ctrl_monitor_struct.
  // This function is defined in soc_ifc_ctrl_macros.svh
  `soc_ifc_ctrl_TO_MONITOR_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_monitor_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in soc_ifc_ctrl_macros.svh
  `soc_ifc_ctrl_FROM_MONITOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Initiator macro used by soc_ifc_ctrl_driver and soc_ifc_ctrl_driver_bfm
  // to communicate initiator driven data to soc_ifc_ctrl_driver_bfm.
  // This struct is defined in soc_ifc_ctrl_macros.svh
  `soc_ifc_ctrl_INITIATOR_STRUCT
    soc_ifc_ctrl_initiator_s soc_ifc_ctrl_initiator_struct;
  //*******************************************************************
  // FUNCTION: to_initiator_struct()
  // This function packs transaction variables into a soc_ifc_ctrl_initiator_s
  // structure.  The function returns the handle to the soc_ifc_ctrl_initiator_struct.
  // This function is defined in soc_ifc_ctrl_macros.svh
  `soc_ifc_ctrl_TO_INITIATOR_STRUCT_FUNCTION  
  //*******************************************************************
  // FUNCTION: from_initiator_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in soc_ifc_ctrl_macros.svh
  `soc_ifc_ctrl_FROM_INITIATOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Responder macro used by soc_ifc_ctrl_driver and soc_ifc_ctrl_driver_bfm
  // to communicate Responder driven data to soc_ifc_ctrl_driver_bfm.
  // This struct is defined in soc_ifc_ctrl_macros.svh
  `soc_ifc_ctrl_RESPONDER_STRUCT
    soc_ifc_ctrl_responder_s soc_ifc_ctrl_responder_struct;
  //*******************************************************************
  // FUNCTION: to_responder_struct()
  // This function packs transaction variables into a soc_ifc_ctrl_responder_s
  // structure.  The function returns the handle to the soc_ifc_ctrl_responder_struct.
  // This function is defined in soc_ifc_ctrl_macros.svh
  `soc_ifc_ctrl_TO_RESPONDER_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_responder_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in soc_ifc_ctrl_macros.svh
  `soc_ifc_ctrl_FROM_RESPONDER_STRUCT_FUNCTION 
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
    return $sformatf("cptra_obf_key_rand:0x%x set_pwrgood:0x%x assert_rst:0x%x wait_cycles:0x%x security_state:%p set_bootfsm_breakpoint:0x%x generic_input_val:0x%x %s",cptra_obf_key_rand,set_pwrgood,assert_rst,wait_cycles,security_state,set_bootfsm_breakpoint,generic_input_val,super.convert2string());
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
    soc_ifc_ctrl_transaction  RHS;
    if (!$cast(RHS,rhs)) return 0;
    // pragma uvmf custom do_compare begin
    // UVMF_CHANGE_ME : Eliminate comparison of variables not to be used for compare
    return (super.do_compare(rhs,comparer)
            &&(this.cptra_obf_key_rand == RHS.cptra_obf_key_rand)
            );
    // pragma uvmf custom do_compare end
  endfunction

  //*******************************************************************
  // FUNCTION: do_copy()
  // This function is automatically called when the .copy() function
  // is called on this class.
  //
  virtual function void do_copy (uvm_object rhs);
    soc_ifc_ctrl_transaction  RHS;
    assert($cast(RHS,rhs));
    // pragma uvmf custom do_copy begin
    super.do_copy(rhs);
    this.cptra_obf_key_rand = RHS.cptra_obf_key_rand;
    this.set_pwrgood = RHS.set_pwrgood;
    this.assert_rst = RHS.assert_rst;
    this.wait_cycles = RHS.wait_cycles;
    this.security_state = RHS.security_state;
    this.set_bootfsm_breakpoint = RHS.set_bootfsm_breakpoint;
    this.generic_input_val = RHS.generic_input_val;
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
      transaction_view_h = $begin_transaction(transaction_viewing_stream_h,"soc_ifc_ctrl_transaction",start_time);
    end
    super.add_to_wave(transaction_view_h);
    // pragma uvmf custom add_to_wave begin
    // UVMF_CHANGE_ME : Color can be applied to transaction entries based on content, example below
    // case()
    //   1 : $add_color(transaction_view_h,"red");
    //   default : $add_color(transaction_view_h,"grey");
    // endcase
    // UVMF_CHANGE_ME : Eliminate transaction variables not wanted in transaction viewing in the waveform viewer
    $add_attribute(transaction_view_h,cptra_obf_key_rand,"cptra_obf_key_rand");
    $add_attribute(transaction_view_h,set_pwrgood,"set_pwrgood");
    $add_attribute(transaction_view_h,assert_rst,"assert_rst");
    $add_attribute(transaction_view_h,wait_cycles,"wait_cycles");
    $add_attribute(transaction_view_h,security_state,"security_state");
    $add_attribute(transaction_view_h,set_bootfsm_breakpoint,"set_bootfsm_breakpoint");
    $add_attribute(transaction_view_h,generic_input_val,"generic_input_val");
    // pragma uvmf custom add_to_wave end
    $end_transaction(transaction_view_h,end_time);
    $free_transaction(transaction_view_h);
    `endif // QUESTA
  endfunction

endclass

// pragma uvmf custom external begin
function void soc_ifc_ctrl_transaction::post_randomize();
    super.post_randomize();

    if (!device_lifecycle_set_static || (device_lifecycle_static == 'hX)) begin
        device_lifecycle_static = this.security_state.device_lifecycle;
        device_lifecycle_set_static = 1'b1;
        `uvm_info("SOC_IFC_CTRL_TXN", $sformatf("Initializing static class variable 'device_lifecycle_static' to value [%p] due to first randomize() call on class object", device_lifecycle_static), UVM_LOW)
    end
endfunction
// pragma uvmf custom external end

