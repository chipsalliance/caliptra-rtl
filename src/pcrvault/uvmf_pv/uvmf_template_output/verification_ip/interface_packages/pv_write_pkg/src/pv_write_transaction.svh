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
// DESCRIPTION: This class defines the variables required for an pv_write
//    transaction.  Class variables to be displayed in waveform transaction
//    viewing are added to the transaction viewing stream in the add_to_wave
//    function.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class pv_write_transaction #(
      string PV_WRITE_REQUESTOR = "SHA512"
      )
 extends uvmf_transaction_base;

  `uvm_object_param_utils( pv_write_transaction #(
                           PV_WRITE_REQUESTOR
                           )
)

  rand logic write_en ;
  rand logic    [PV_ENTRY_ADDR_W-1:0] write_entry ;
  rand logic    [PV_ENTRY_SIZE_WIDTH-1:0] write_offset ;
  rand logic    [PV_DATA_W-1:0] write_data ;
  logic error ;

  //Constraints for the transaction variables:
  //constraint write_en_c {write_en == 1'b1;}
  constraint write_offset_c {write_offset >= 0; write_offset < 12;}
  constraint write_en_c {write_en == 1;}
  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //*******************************************************************
  //*******************************************************************
  // Macros that define structs and associated functions are
  // located in pv_write_macros.svh

  //*******************************************************************
  // Monitor macro used by pv_write_monitor and pv_write_monitor_bfm
  // This struct is defined in pv_write_macros.svh
  `pv_write_MONITOR_STRUCT
    pv_write_monitor_s pv_write_monitor_struct;
  //*******************************************************************
  // FUNCTION: to_monitor_struct()
  // This function packs transaction variables into a pv_write_monitor_s
  // structure.  The function returns the handle to the pv_write_monitor_struct.
  // This function is defined in pv_write_macros.svh
  `pv_write_TO_MONITOR_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_monitor_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in pv_write_macros.svh
  `pv_write_FROM_MONITOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Initiator macro used by pv_write_driver and pv_write_driver_bfm
  // to communicate initiator driven data to pv_write_driver_bfm.
  // This struct is defined in pv_write_macros.svh
  `pv_write_INITIATOR_STRUCT
    pv_write_initiator_s pv_write_initiator_struct;
  //*******************************************************************
  // FUNCTION: to_initiator_struct()
  // This function packs transaction variables into a pv_write_initiator_s
  // structure.  The function returns the handle to the pv_write_initiator_struct.
  // This function is defined in pv_write_macros.svh
  `pv_write_TO_INITIATOR_STRUCT_FUNCTION  
  //*******************************************************************
  // FUNCTION: from_initiator_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in pv_write_macros.svh
  `pv_write_FROM_INITIATOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Responder macro used by pv_write_driver and pv_write_driver_bfm
  // to communicate Responder driven data to pv_write_driver_bfm.
  // This struct is defined in pv_write_macros.svh
  `pv_write_RESPONDER_STRUCT
    pv_write_responder_s pv_write_responder_struct;
  //*******************************************************************
  // FUNCTION: to_responder_struct()
  // This function packs transaction variables into a pv_write_responder_s
  // structure.  The function returns the handle to the pv_write_responder_struct.
  // This function is defined in pv_write_macros.svh
  `pv_write_TO_RESPONDER_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_responder_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in pv_write_macros.svh
  `pv_write_FROM_RESPONDER_STRUCT_FUNCTION 
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
    return $sformatf("write_en:0x%x write_entry:0x%x write_offset:0x%x write_data:0x%x err:0x%x ",write_en,write_entry,write_offset,write_data,error);
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
    pv_write_transaction #(
        .PV_WRITE_REQUESTOR(PV_WRITE_REQUESTOR)
        )
 RHS;
    if (!$cast(RHS,rhs)) return 0;
    // pragma uvmf custom do_compare begin
    // UVMF_CHANGE_ME : Eliminate comparison of variables not to be used for compare
    return (super.do_compare(rhs,comparer)
            &&(this.write_entry == RHS.write_entry)
            &&(this.write_data == RHS.write_data)
            &&(this.error == RHS.error)
            );
    // pragma uvmf custom do_compare end
  endfunction

  //*******************************************************************
  // FUNCTION: do_copy()
  // This function is automatically called when the .copy() function
  // is called on this class.
  //
  virtual function void do_copy (uvm_object rhs);
    pv_write_transaction #(
        .PV_WRITE_REQUESTOR(PV_WRITE_REQUESTOR)
        )
 RHS;
    assert($cast(RHS,rhs));
    // pragma uvmf custom do_copy begin
    super.do_copy(rhs);
    this.write_en = RHS.write_en;
    this.write_entry = RHS.write_entry;
    this.write_offset = RHS.write_offset;
    this.write_data = RHS.write_data;
    this.error = RHS.error;
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
      transaction_view_h = $begin_transaction(transaction_viewing_stream_h,"pv_write_transaction",start_time);
    end
    super.add_to_wave(transaction_view_h);
    // pragma uvmf custom add_to_wave begin
    // UVMF_CHANGE_ME : Color can be applied to transaction entries based on content, example below
    // case()
    //   1 : $add_color(transaction_view_h,"red");
    //   default : $add_color(transaction_view_h,"grey");
    // endcase
    // UVMF_CHANGE_ME : Eliminate transaction variables not wanted in transaction viewing in the waveform viewer
    $add_attribute(transaction_view_h,write_en,"write_en");
    $add_attribute(transaction_view_h,write_entry,"write_entry");
    $add_attribute(transaction_view_h,write_offset,"write_offset");
    $add_attribute(transaction_view_h,write_data,"write_data");
    $add_attribute(transaction_view_h,error,"error");
    // pragma uvmf custom add_to_wave end
    $end_transaction(transaction_view_h,end_time);
    $free_transaction(transaction_view_h);
    `endif // QUESTA
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

