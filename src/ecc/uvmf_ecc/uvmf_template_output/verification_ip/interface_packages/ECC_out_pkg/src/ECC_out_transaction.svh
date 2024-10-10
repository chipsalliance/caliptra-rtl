//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This class defines the variables required for an ECC_out
//    transaction.  Class variables to be displayed in waveform transaction
//    viewing are added to the transaction viewing stream in the add_to_wave
//    function.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class ECC_out_transaction #(
      int AHB_ADDR_WIDTH = 32,
      int AHB_DATA_WIDTH = 32,
      int OUTPUT_TEXT_WIDTH = 384
      )
 extends uvmf_transaction_base;

  `uvm_object_param_utils( ECC_out_transaction #(
                           AHB_ADDR_WIDTH,
                           AHB_DATA_WIDTH,
                           OUTPUT_TEXT_WIDTH
                           )
)

  bit [OUTPUT_TEXT_WIDTH-1:0] result_privkey ;
  bit [OUTPUT_TEXT_WIDTH-1:0] result_pubkey_x ;
  bit [OUTPUT_TEXT_WIDTH-1:0] result_pubkey_y ;
  bit [OUTPUT_TEXT_WIDTH-1:0] result_R ;
  bit [OUTPUT_TEXT_WIDTH-1:0] result_S ;
  bit [OUTPUT_TEXT_WIDTH-1:0] result_verify_R ;
  bit [OUTPUT_TEXT_WIDTH-1:0] result_sharedkey ;

  //Constraints for the transaction variables:

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //*******************************************************************
  //*******************************************************************
  // Macros that define structs and associated functions are
  // located in ECC_out_macros.svh

  //*******************************************************************
  // Monitor macro used by ECC_out_monitor and ECC_out_monitor_bfm
  // This struct is defined in ECC_out_macros.svh
  `ECC_out_MONITOR_STRUCT
    ECC_out_monitor_s ECC_out_monitor_struct;
  //*******************************************************************
  // FUNCTION: to_monitor_struct()
  // This function packs transaction variables into a ECC_out_monitor_s
  // structure.  The function returns the handle to the ECC_out_monitor_struct.
  // This function is defined in ECC_out_macros.svh
  `ECC_out_TO_MONITOR_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_monitor_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in ECC_out_macros.svh
  `ECC_out_FROM_MONITOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Initiator macro used by ECC_out_driver and ECC_out_driver_bfm
  // to communicate initiator driven data to ECC_out_driver_bfm.
  // This struct is defined in ECC_out_macros.svh
  `ECC_out_INITIATOR_STRUCT
    ECC_out_initiator_s ECC_out_initiator_struct;
  //*******************************************************************
  // FUNCTION: to_initiator_struct()
  // This function packs transaction variables into a ECC_out_initiator_s
  // structure.  The function returns the handle to the ECC_out_initiator_struct.
  // This function is defined in ECC_out_macros.svh
  `ECC_out_TO_INITIATOR_STRUCT_FUNCTION  
  //*******************************************************************
  // FUNCTION: from_initiator_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in ECC_out_macros.svh
  `ECC_out_FROM_INITIATOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Responder macro used by ECC_out_driver and ECC_out_driver_bfm
  // to communicate Responder driven data to ECC_out_driver_bfm.
  // This struct is defined in ECC_out_macros.svh
  `ECC_out_RESPONDER_STRUCT
    ECC_out_responder_s ECC_out_responder_struct;
  //*******************************************************************
  // FUNCTION: to_responder_struct()
  // This function packs transaction variables into a ECC_out_responder_s
  // structure.  The function returns the handle to the ECC_out_responder_struct.
  // This function is defined in ECC_out_macros.svh
  `ECC_out_TO_RESPONDER_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_responder_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in ECC_out_macros.svh
  `ECC_out_FROM_RESPONDER_STRUCT_FUNCTION 
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
    return $sformatf("result_privkey:0x%x result_pubkey_x:0x%x result_pubkey_y:0x%x result_R:0x%x result_S:0x%x result_verify_R:0x%x result_sharedkey:0x%x",result_privkey,result_pubkey_x,result_pubkey_y,result_R,result_S,result_verify_R, result_sharedkey);
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
    ECC_out_transaction #(
        .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
        .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
        .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH)
        )
 RHS;
    if (!$cast(RHS,rhs)) return 0;
    // pragma uvmf custom do_compare begin
    // UVMF_CHANGE_ME : Eliminate comparison of variables not to be used for compare
    return (super.do_compare(rhs,comparer)
            &&(this.result_privkey == RHS.result_privkey)
            &&(this.result_pubkey_x == RHS.result_pubkey_x)
            &&(this.result_pubkey_y == RHS.result_pubkey_y)
            &&(this.result_R == RHS.result_R)
            &&(this.result_S == RHS.result_S)
            &&(this.result_verify_R == RHS.result_verify_R)
            &&(this.result_sharedkey == RHS.result_sharedkey)
            );
    // pragma uvmf custom do_compare end
  endfunction

  //*******************************************************************
  // FUNCTION: do_copy()
  // This function is automatically called when the .copy() function
  // is called on this class.
  //
  virtual function void do_copy (uvm_object rhs);
    ECC_out_transaction #(
        .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
        .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
        .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH)
        )
 RHS;
    assert($cast(RHS,rhs));
    // pragma uvmf custom do_copy begin
    super.do_copy(rhs);
    this.result_privkey = RHS.result_privkey;
    this.result_pubkey_x = RHS.result_pubkey_x;
    this.result_pubkey_y = RHS.result_pubkey_y;
    this.result_R = RHS.result_R;
    this.result_S = RHS.result_S;
    this.result_verify_R = RHS.result_verify_R;
    this.result_sharedkey = RHS.result_sharedkey;
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
      transaction_view_h = $begin_transaction(transaction_viewing_stream_h,"ECC_out_transaction",start_time);
    end
    super.add_to_wave(transaction_view_h);
    // pragma uvmf custom add_to_wave begin
    // UVMF_CHANGE_ME : Color can be applied to transaction entries based on content, example below
    // case()
    //   1 : $add_color(transaction_view_h,"red");
    //   default : $add_color(transaction_view_h,"grey");
    // endcase
    // UVMF_CHANGE_ME : Eliminate transaction variables not wanted in transaction viewing in the waveform viewer
    $add_attribute(transaction_view_h,result_privkey,"result_privkey");
    $add_attribute(transaction_view_h,result_pubkey_x,"result_pubkey_x");
    $add_attribute(transaction_view_h,result_pubkey_y,"result_pubkey_y");
    $add_attribute(transaction_view_h,result_R,"result_R");
    $add_attribute(transaction_view_h,result_S,"result_S");
    $add_attribute(transaction_view_h,result_verify_R,"result_verify_R");
    $add_attribute(transaction_view_h,result_sharedkey,"result_sharedkey");
    // pragma uvmf custom add_to_wave end
    $end_transaction(transaction_view_h,end_time);
    $free_transaction(transaction_view_h);
    `endif // QUESTA
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

