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
// DESCRIPTION: This class defines the variables required for an ss_mode_ctrl
//    transaction.  Class variables to be displayed in waveform transaction
//    viewing are added to the transaction viewing stream in the add_to_wave
//    function.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class ss_mode_ctrl_transaction  extends uvmf_transaction_base;

  `uvm_object_utils( ss_mode_ctrl_transaction )

  rand bit [63:0] strap_ss_caliptra_base_addr ;
  rand bit [63:0] strap_ss_mci_base_addr ;
  rand bit [63:0] strap_ss_recovery_ifc_base_addr ;
  rand bit [63:0] strap_ss_external_staging_area_base_addr ;
  rand bit [63:0] strap_ss_otp_fc_base_addr ;
  rand bit [63:0] strap_ss_uds_seed_base_addr ;
  rand bit [63:0] strap_ss_key_release_base_addr ;
  rand bit [15:0] strap_ss_key_release_key_size ;
  rand bit [31:0] strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset ;
  rand bit [31:0] strap_ss_num_of_prod_debug_unlock_auth_pk_hashes ;
  rand bit [31:0] strap_ss_strap_generic_0 ;
  rand bit [31:0] strap_ss_strap_generic_1 ;
  rand bit [31:0] strap_ss_strap_generic_2 ;
  rand bit [31:0] strap_ss_strap_generic_3 ;
  rand bit [31:0] strap_ss_caliptra_dma_axi_user ;
  rand bit ss_debug_intent ;

  //Constraints for the transaction variables:
  constraint strap_ss_caliptra_base_addr_c { strap_ss_caliptra_base_addr dist {0 :/ 1, [1:64'hFFFF_FFFF_FFFF_FFFE] :/ 98, 64'hFFFF_FFFF_FFFF_FFFF :/ 1}; }
  constraint strap_ss_mci_base_addr_c { strap_ss_mci_base_addr dist {0 :/ 1, [1:64'hFFFF_FFFF_FFFF_FFFE] :/ 98, 64'hFFFF_FFFF_FFFF_FFFF :/ 1}; }
  constraint strap_ss_recovery_ifc_base_addr_c { strap_ss_recovery_ifc_base_addr dist {0 :/ 1, [1:64'hFFFF_FFFF_FFFF_FFFE] :/ 98, 64'hFFFF_FFFF_FFFF_FFFF :/ 1}; }
  constraint strap_ss_external_staging_area_base_addr_c { strap_ss_external_staging_area_base_addr dist {0 :/ 1, [1:64'hFFFF_FFFF_FFFF_FFFE] :/ 98, 64'hFFFF_FFFF_FFFF_FFFF :/ 1}; }
  constraint strap_ss_otp_fc_base_addr_c { strap_ss_otp_fc_base_addr dist {0 :/ 1, [1:64'hFFFF_FFFF_FFFF_FFFE] :/ 98, 64'hFFFF_FFFF_FFFF_FFFF :/ 1}; }
  constraint strap_ss_uds_seed_base_addr_c { strap_ss_uds_seed_base_addr dist {0 :/ 1, [1:64'hFFFF_FFFF_FFFF_FFFE] :/ 98, 64'hFFFF_FFFF_FFFF_FFFF :/ 1}; }
  constraint strap_ss_key_release_base_addr_c { strap_ss_key_release_base_addr dist {0 :/ 1, [1:64'hFFFF_FFFF_FFFF_FFFE] :/ 98, 64'hFFFF_FFFF_FFFF_FFFF :/ 1}; }
  constraint strap_ss_key_release_key_size_c { strap_ss_key_release_key_size == 16'h40; }
  // All base address straps are configured to a different 4KiB region
  constraint strap_ss_addr_unique_c { (strap_ss_caliptra_base_addr     & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_mci_base_addr          & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_caliptra_base_addr     & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_recovery_ifc_base_addr & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_caliptra_base_addr     & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_external_staging_area_base_addr & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_caliptra_base_addr     & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_otp_fc_base_addr       & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_caliptra_base_addr     & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_uds_seed_base_addr     & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_caliptra_base_addr     & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_key_release_base_addr  & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_mci_base_addr          & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_recovery_ifc_base_addr & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_mci_base_addr          & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_external_staging_area_base_addr & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_mci_base_addr          & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_otp_fc_base_addr       & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_mci_base_addr          & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_uds_seed_base_addr     & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_mci_base_addr          & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_key_release_base_addr  & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_recovery_ifc_base_addr & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_external_staging_area_base_addr & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_recovery_ifc_base_addr & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_otp_fc_base_addr       & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_recovery_ifc_base_addr & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_uds_seed_base_addr     & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_recovery_ifc_base_addr & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_key_release_base_addr  & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_otp_fc_base_addr       & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_external_staging_area_base_addr & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_otp_fc_base_addr       & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_uds_seed_base_addr     & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_otp_fc_base_addr       & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_key_release_base_addr  & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_external_staging_area_base_addr & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_uds_seed_base_addr     & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_external_staging_area_base_addr & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_key_release_base_addr  & 64'hFFFF_FFFF_FFFF_F000);
                                      (strap_ss_uds_seed_base_addr              & 64'hFFFF_FFFF_FFFF_F000) != (strap_ss_key_release_base_addr  & 64'hFFFF_FFFF_FFFF_F000); }
  constraint strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_c { strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset dist {0 :/ 1, [1:32'hFFFF_FFFE] :/ 98, 32'hFFFF_FFFF :/ 1}; }
  constraint strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_c { strap_ss_num_of_prod_debug_unlock_auth_pk_hashes dist {0 :/ 1, [1:32'hFFF] :/ 98, 32'h1000 :/ 1}; }
  constraint strap_ss_strap_generic_0_c { strap_ss_strap_generic_0 dist {0 :/ 1, [1:32'hFFFF_FFFE] :/ 98, 32'hFFFF_FFFF :/ 1}; }
  constraint strap_ss_strap_generic_1_c { strap_ss_strap_generic_1 dist {0 :/ 1, [1:32'hFFFF_FFFE] :/ 98, 32'hFFFF_FFFF :/ 1}; }
  constraint strap_ss_strap_generic_2_c { strap_ss_strap_generic_2 dist {0 :/ 1, [1:32'hFFFF_FFFE] :/ 98, 32'hFFFF_FFFF :/ 1}; }
  constraint strap_ss_strap_generic_3_c { strap_ss_strap_generic_3 dist {0 :/ 1, [1:32'hFFFF_FFFE] :/ 98, 32'hFFFF_FFFF :/ 1}; }
  constraint strap_ss_caliptra_dma_axi_user_c { strap_ss_caliptra_dma_axi_user dist {0 :/ 1, [1:32'hFFFF_FFFE] :/ 98, 32'hFFFF_FFFF :/ 1}; }
  constraint debug_intent_c { ss_debug_intent dist {1 :/ 1, 0 :/ 9}; }

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //*******************************************************************
  //*******************************************************************
  // Macros that define structs and associated functions are
  // located in ss_mode_ctrl_macros.svh

  //*******************************************************************
  // Monitor macro used by ss_mode_ctrl_monitor and ss_mode_ctrl_monitor_bfm
  // This struct is defined in ss_mode_ctrl_macros.svh
  `ss_mode_ctrl_MONITOR_STRUCT
    ss_mode_ctrl_monitor_s ss_mode_ctrl_monitor_struct;
  //*******************************************************************
  // FUNCTION: to_monitor_struct()
  // This function packs transaction variables into a ss_mode_ctrl_monitor_s
  // structure.  The function returns the handle to the ss_mode_ctrl_monitor_struct.
  // This function is defined in ss_mode_ctrl_macros.svh
  `ss_mode_ctrl_TO_MONITOR_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_monitor_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in ss_mode_ctrl_macros.svh
  `ss_mode_ctrl_FROM_MONITOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Initiator macro used by ss_mode_ctrl_driver and ss_mode_ctrl_driver_bfm
  // to communicate initiator driven data to ss_mode_ctrl_driver_bfm.
  // This struct is defined in ss_mode_ctrl_macros.svh
  `ss_mode_ctrl_INITIATOR_STRUCT
    ss_mode_ctrl_initiator_s ss_mode_ctrl_initiator_struct;
  //*******************************************************************
  // FUNCTION: to_initiator_struct()
  // This function packs transaction variables into a ss_mode_ctrl_initiator_s
  // structure.  The function returns the handle to the ss_mode_ctrl_initiator_struct.
  // This function is defined in ss_mode_ctrl_macros.svh
  `ss_mode_ctrl_TO_INITIATOR_STRUCT_FUNCTION  
  //*******************************************************************
  // FUNCTION: from_initiator_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in ss_mode_ctrl_macros.svh
  `ss_mode_ctrl_FROM_INITIATOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Responder macro used by ss_mode_ctrl_driver and ss_mode_ctrl_driver_bfm
  // to communicate Responder driven data to ss_mode_ctrl_driver_bfm.
  // This struct is defined in ss_mode_ctrl_macros.svh
  `ss_mode_ctrl_RESPONDER_STRUCT
    ss_mode_ctrl_responder_s ss_mode_ctrl_responder_struct;
  //*******************************************************************
  // FUNCTION: to_responder_struct()
  // This function packs transaction variables into a ss_mode_ctrl_responder_s
  // structure.  The function returns the handle to the ss_mode_ctrl_responder_struct.
  // This function is defined in ss_mode_ctrl_macros.svh
  `ss_mode_ctrl_TO_RESPONDER_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_responder_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in ss_mode_ctrl_macros.svh
  `ss_mode_ctrl_FROM_RESPONDER_STRUCT_FUNCTION 
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
    return $sformatf("strap_ss_caliptra_base_addr:0x%x strap_ss_mci_base_addr:0x%x strap_ss_recovery_ifc_base_addr:0x%x strap_ss_external_staging_area_base_addr:0x%x strap_ss_otp_fc_base_addr:0x%x strap_ss_uds_seed_base_addr:0x%x strap_ss_key_release_base_addr:0x%x strap_ss_key_release_key_size:0x%x strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset:0x%x strap_ss_num_of_prod_debug_unlock_auth_pk_hashes:0x%x strap_ss_strap_generic_0:0x%x strap_ss_strap_generic_1:0x%x strap_ss_strap_generic_2:0x%x strap_ss_strap_generic_3:0x%x strap_ss_caliptra_dma_axi_user:0x%x ss_debug_intent:0x%x %s",strap_ss_caliptra_base_addr,strap_ss_mci_base_addr,strap_ss_recovery_ifc_base_addr,strap_ss_external_staging_area_base_addr,strap_ss_otp_fc_base_addr,strap_ss_uds_seed_base_addr,strap_ss_key_release_base_addr,strap_ss_key_release_key_size,strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset,strap_ss_num_of_prod_debug_unlock_auth_pk_hashes,strap_ss_strap_generic_0,strap_ss_strap_generic_1,strap_ss_strap_generic_2,strap_ss_strap_generic_3,strap_ss_caliptra_dma_axi_user,ss_debug_intent,super.convert2string);
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
    ss_mode_ctrl_transaction  RHS;
    if (!$cast(RHS,rhs)) return 0;
    // pragma uvmf custom do_compare begin
    // UVMF_CHANGE_ME : Eliminate comparison of variables not to be used for compare
    return (super.do_compare(rhs,comparer)
            );
    // pragma uvmf custom do_compare end
  endfunction

  //*******************************************************************
  // FUNCTION: do_copy()
  // This function is automatically called when the .copy() function
  // is called on this class.
  //
  virtual function void do_copy (uvm_object rhs);
    ss_mode_ctrl_transaction  RHS;
    assert($cast(RHS,rhs));
    // pragma uvmf custom do_copy begin
    super.do_copy(rhs);
    this.strap_ss_caliptra_base_addr = RHS.strap_ss_caliptra_base_addr;
    this.strap_ss_mci_base_addr = RHS.strap_ss_mci_base_addr;
    this.strap_ss_recovery_ifc_base_addr = RHS.strap_ss_recovery_ifc_base_addr;
    this.strap_ss_external_staging_area_base_addr = RHS.strap_ss_external_staging_area_base_addr;
    this.strap_ss_otp_fc_base_addr = RHS.strap_ss_otp_fc_base_addr;
    this.strap_ss_uds_seed_base_addr = RHS.strap_ss_uds_seed_base_addr;
    this.strap_ss_key_release_base_addr = RHS.strap_ss_key_release_base_addr;
    this.strap_ss_key_release_key_size = RHS.strap_ss_key_release_key_size;
    this.strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset = RHS.strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset;
    this.strap_ss_num_of_prod_debug_unlock_auth_pk_hashes = RHS.strap_ss_num_of_prod_debug_unlock_auth_pk_hashes;
    this.strap_ss_strap_generic_0 = RHS.strap_ss_strap_generic_0;
    this.strap_ss_strap_generic_1 = RHS.strap_ss_strap_generic_1;
    this.strap_ss_strap_generic_2 = RHS.strap_ss_strap_generic_2;
    this.strap_ss_strap_generic_3 = RHS.strap_ss_strap_generic_3;
    this.strap_ss_caliptra_dma_axi_user = RHS.strap_ss_caliptra_dma_axi_user;
    this.ss_debug_intent = RHS.ss_debug_intent;
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
      transaction_view_h = $begin_transaction(transaction_viewing_stream_h,"ss_mode_ctrl_transaction",start_time);
    end
    super.add_to_wave(transaction_view_h);
    // pragma uvmf custom add_to_wave begin
    // UVMF_CHANGE_ME : Color can be applied to transaction entries based on content, example below
    // case()
    //   1 : $add_color(transaction_view_h,"red");
    //   default : $add_color(transaction_view_h,"grey");
    // endcase
    // UVMF_CHANGE_ME : Eliminate transaction variables not wanted in transaction viewing in the waveform viewer
    $add_attribute(transaction_view_h,strap_ss_caliptra_base_addr,"strap_ss_caliptra_base_addr");
    $add_attribute(transaction_view_h,strap_ss_mci_base_addr,"strap_ss_mci_base_addr");
    $add_attribute(transaction_view_h,strap_ss_recovery_ifc_base_addr,"strap_ss_recovery_ifc_base_addr");
    $add_attribute(transaction_view_h,strap_ss_external_staging_area_base_addr,"strap_ss_external_staging_area_base_addr");
    $add_attribute(transaction_view_h,strap_ss_otp_fc_base_addr,"strap_ss_otp_fc_base_addr");
    $add_attribute(transaction_view_h,strap_ss_uds_seed_base_addr,"strap_ss_uds_seed_base_addr");
    $add_attribute(transaction_view_h,strap_ss_key_release_base_addr,"strap_ss_key_release_base_addr");
    $add_attribute(transaction_view_h,strap_ss_key_release_key_size,"strap_ss_key_release_key_size");
    $add_attribute(transaction_view_h,strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset,"strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset");
    $add_attribute(transaction_view_h,strap_ss_num_of_prod_debug_unlock_auth_pk_hashes,"strap_ss_num_of_prod_debug_unlock_auth_pk_hashes");
    $add_attribute(transaction_view_h,strap_ss_strap_generic_0,"strap_ss_strap_generic_0");
    $add_attribute(transaction_view_h,strap_ss_strap_generic_1,"strap_ss_strap_generic_1");
    $add_attribute(transaction_view_h,strap_ss_strap_generic_2,"strap_ss_strap_generic_2");
    $add_attribute(transaction_view_h,strap_ss_strap_generic_3,"strap_ss_strap_generic_3");
    $add_attribute(transaction_view_h,strap_ss_caliptra_dma_axi_user,"strap_ss_caliptra_dma_axi_user");
    $add_attribute(transaction_view_h,ss_debug_intent,"ss_debug_intent");
    // pragma uvmf custom add_to_wave end
    $end_transaction(transaction_view_h,end_time);
    $free_transaction(transaction_view_h);
    `endif // QUESTA
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

