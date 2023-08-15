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
// DESCRIPTION: This class defines the variables required for an cptra_status
//    transaction.  Class variables to be displayed in waveform transaction
//    viewing are added to the transaction viewing stream in the add_to_wave
//    function.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class cptra_status_transaction  extends uvmf_transaction_base;

  `uvm_object_utils( cptra_status_transaction )

  bit soc_ifc_err_intr_pending ;
  bit soc_ifc_notif_intr_pending ;
  bit sha_err_intr_pending ;
  bit sha_notif_intr_pending ;
  bit timer_intr_pending ;
  bit noncore_rst_asserted ;
  bit uc_rst_asserted ;
  bit fw_update_rst_window ;
  bit [`CLP_OBF_KEY_DWORDS-1:0] [31:0] cptra_obf_key_reg ;
  bit [`CLP_OBF_FE_DWORDS-1:0] [31:0] obf_field_entropy ;
  bit [`CLP_OBF_UDS_DWORDS-1:0] [31:0] obf_uds_seed ;
  bit [31:0] nmi_vector ;
  bit nmi_intr_pending ;
  bit iccm_locked ;

  //Constraints for the transaction variables:

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //*******************************************************************
  //*******************************************************************
  // Macros that define structs and associated functions are
  // located in cptra_status_macros.svh

  //*******************************************************************
  // Monitor macro used by cptra_status_monitor and cptra_status_monitor_bfm
  // This struct is defined in cptra_status_macros.svh
  `cptra_status_MONITOR_STRUCT
    cptra_status_monitor_s cptra_status_monitor_struct;
  //*******************************************************************
  // FUNCTION: to_monitor_struct()
  // This function packs transaction variables into a cptra_status_monitor_s
  // structure.  The function returns the handle to the cptra_status_monitor_struct.
  // This function is defined in cptra_status_macros.svh
  `cptra_status_TO_MONITOR_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_monitor_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in cptra_status_macros.svh
  `cptra_status_FROM_MONITOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Initiator macro used by cptra_status_driver and cptra_status_driver_bfm
  // to communicate initiator driven data to cptra_status_driver_bfm.
  // This struct is defined in cptra_status_macros.svh
  `cptra_status_INITIATOR_STRUCT
    cptra_status_initiator_s cptra_status_initiator_struct;
  //*******************************************************************
  // FUNCTION: to_initiator_struct()
  // This function packs transaction variables into a cptra_status_initiator_s
  // structure.  The function returns the handle to the cptra_status_initiator_struct.
  // This function is defined in cptra_status_macros.svh
  `cptra_status_TO_INITIATOR_STRUCT_FUNCTION  
  //*******************************************************************
  // FUNCTION: from_initiator_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in cptra_status_macros.svh
  `cptra_status_FROM_INITIATOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Responder macro used by cptra_status_driver and cptra_status_driver_bfm
  // to communicate Responder driven data to cptra_status_driver_bfm.
  // This struct is defined in cptra_status_macros.svh
  `cptra_status_RESPONDER_STRUCT
    cptra_status_responder_s cptra_status_responder_struct;
  //*******************************************************************
  // FUNCTION: to_responder_struct()
  // This function packs transaction variables into a cptra_status_responder_s
  // structure.  The function returns the handle to the cptra_status_responder_struct.
  // This function is defined in cptra_status_macros.svh
  `cptra_status_TO_RESPONDER_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_responder_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in cptra_status_macros.svh
  `cptra_status_FROM_RESPONDER_STRUCT_FUNCTION 
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
    return $sformatf("soc_ifc_err_intr_pending:0x%x soc_ifc_notif_intr_pending:0x%x sha_err_intr_pending:0x%x sha_notif_intr_pending:0x%x timer_intr_pending:0x%x noncore_rst_asserted:0x%x uc_rst_asserted:0x%x fw_update_rst_window:0x%x cptra_obf_key_reg:0x%x obf_field_entropy:0x%x obf_uds_seed:0x%x nmi_vector:0x%x nmi_intr_pending:0x%x iccm_locked:0x%x %s",soc_ifc_err_intr_pending,soc_ifc_notif_intr_pending,sha_err_intr_pending,sha_notif_intr_pending,timer_intr_pending,noncore_rst_asserted,uc_rst_asserted,fw_update_rst_window,cptra_obf_key_reg,obf_field_entropy,obf_uds_seed,nmi_vector,nmi_intr_pending,iccm_locked,super.convert2string());
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
    cptra_status_transaction  RHS;
    if (!$cast(RHS,rhs)) return 0;
    // pragma uvmf custom do_compare begin
    // UVMF_CHANGE_ME : Eliminate comparison of variables not to be used for compare
    return (super.do_compare(rhs,comparer)
            &&(this.soc_ifc_err_intr_pending == RHS.soc_ifc_err_intr_pending)
            &&(this.soc_ifc_notif_intr_pending == RHS.soc_ifc_notif_intr_pending)
            &&(this.sha_err_intr_pending == RHS.sha_err_intr_pending)
            &&(this.sha_notif_intr_pending == RHS.sha_notif_intr_pending)
            &&(this.timer_intr_pending == RHS.timer_intr_pending)
            &&(this.noncore_rst_asserted == RHS.noncore_rst_asserted)
            &&(this.uc_rst_asserted == RHS.uc_rst_asserted)
            &&(this.fw_update_rst_window == RHS.fw_update_rst_window)
            &&(this.cptra_obf_key_reg == RHS.cptra_obf_key_reg)
            &&(this.obf_field_entropy == RHS.obf_field_entropy)
            &&(this.obf_uds_seed == RHS.obf_uds_seed)
            &&(this.nmi_vector == RHS.nmi_vector)
            &&(this.nmi_intr_pending == RHS.nmi_intr_pending)
            &&(this.iccm_locked == RHS.iccm_locked)
            );
    // pragma uvmf custom do_compare end
  endfunction

  //*******************************************************************
  // FUNCTION: do_copy()
  // This function is automatically called when the .copy() function
  // is called on this class.
  //
  virtual function void do_copy (uvm_object rhs);
    cptra_status_transaction  RHS;
    assert($cast(RHS,rhs));
    // pragma uvmf custom do_copy begin
    super.do_copy(rhs);
    this.soc_ifc_err_intr_pending = RHS.soc_ifc_err_intr_pending;
    this.soc_ifc_notif_intr_pending = RHS.soc_ifc_notif_intr_pending;
    this.sha_err_intr_pending = RHS.sha_err_intr_pending;
    this.sha_notif_intr_pending = RHS.sha_notif_intr_pending;
    this.timer_intr_pending = RHS.timer_intr_pending;
    this.noncore_rst_asserted = RHS.noncore_rst_asserted;
    this.uc_rst_asserted = RHS.uc_rst_asserted;
    this.fw_update_rst_window = RHS.fw_update_rst_window;
    this.cptra_obf_key_reg = RHS.cptra_obf_key_reg;
    this.obf_field_entropy = RHS.obf_field_entropy;
    this.obf_uds_seed = RHS.obf_uds_seed;
    this.nmi_vector = RHS.nmi_vector;
    this.nmi_intr_pending = RHS.nmi_intr_pending;
    this.iccm_locked = RHS.iccm_locked;
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
      transaction_view_h = $begin_transaction(transaction_viewing_stream_h,"cptra_status_transaction",start_time);
    end
    super.add_to_wave(transaction_view_h);
    // pragma uvmf custom add_to_wave begin
    // UVMF_CHANGE_ME : Color can be applied to transaction entries based on content, example below
    // case()
    //   1 : $add_color(transaction_view_h,"red");
    //   default : $add_color(transaction_view_h,"grey");
    // endcase
    // UVMF_CHANGE_ME : Eliminate transaction variables not wanted in transaction viewing in the waveform viewer
    $add_attribute(transaction_view_h,soc_ifc_err_intr_pending,"soc_ifc_err_intr_pending");
    $add_attribute(transaction_view_h,soc_ifc_notif_intr_pending,"soc_ifc_notif_intr_pending");
    $add_attribute(transaction_view_h,sha_err_intr_pending,"sha_err_intr_pending");
    $add_attribute(transaction_view_h,sha_notif_intr_pending,"sha_notif_intr_pending");
    $add_attribute(transaction_view_h,timer_intr_pending,"timer_intr_pending");
    $add_attribute(transaction_view_h,noncore_rst_asserted,"noncore_rst_asserted");
    $add_attribute(transaction_view_h,uc_rst_asserted,"uc_rst_asserted");
    $add_attribute(transaction_view_h,fw_update_rst_window,"fw_update_rst_window");
    $add_attribute(transaction_view_h,cptra_obf_key_reg,"cptra_obf_key_reg");
    $add_attribute(transaction_view_h,obf_field_entropy,"obf_field_entropy");
    $add_attribute(transaction_view_h,obf_uds_seed,"obf_uds_seed");
    $add_attribute(transaction_view_h,nmi_vector,"nmi_vector");
    $add_attribute(transaction_view_h,nmi_intr_pending,"nmi_intr_pending");
    $add_attribute(transaction_view_h,iccm_locked,"iccm_locked");
    // pragma uvmf custom add_to_wave end
    $end_transaction(transaction_view_h,end_time);
    $free_transaction(transaction_view_h);
    `endif // QUESTA
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

