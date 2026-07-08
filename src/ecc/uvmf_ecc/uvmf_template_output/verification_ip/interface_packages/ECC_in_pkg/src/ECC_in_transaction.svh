//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This class defines the variables required for an ECC_in
//    transaction.  Class variables to be displayed in waveform transaction
//    viewing are added to the transaction viewing stream in the add_to_wave
//    function.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class ECC_in_transaction #(
      int AHB_ADDR_WIDTH = 32,
      int AHB_DATA_WIDTH = 64
      )
 extends uvmf_transaction_base;

  `uvm_object_param_utils( ECC_in_transaction #(
                           AHB_ADDR_WIDTH,
                           AHB_DATA_WIDTH
                           )
)

  rand ecc_in_test_transactions test ;
  rand ecc_in_op_transactions op ;
  // New random axes for dual-curve + nondet-SIGN + error-injection coverage.
  rand ecc_in_curve_e    curve;
  rand ecc_in_err_mode_e err_mode;
  rand bit               rand_k_en;
  rand bit               pcr_sign;
  rand bit               kv_intf;
  rand bit [4:0]         kv_slot;
  rand bit               pollute_upper;
  // Zeroize-mid-op axis: when set, BFM injects ZEROIZE cmd N clocks
  // after dispatch (before ready reasserts) to fire zeroize_ready_cp
  // [ready=0], zeroize_x_curve_cp, zeroize_cmd_cp, zeroize_pcr_cp bins.
  rand bit               zeroize_mid_op;
  rand bit [3:0]         zeroize_delay_clks;

  //Constraints for the transaction variables:
  constraint ecc_valid_test_contraints { test inside {ecc_normal_test, ecc_otf_reset_test}; }
  constraint ecc_valid_op_constraints { op inside {key_gen, key_sign, key_verify, ecdh_sharedkey}; }

  // Legal-op constraints when err_mode == ERR_NONE. rand_k_en/pcr_sign are
  // only permitted in DUT-legal combinations. kv_intf is forced off because
  // the block TB has no KV data source; only the KV-error modes arm KV ctrl.
  constraint ecc_legal_axes_c {
    (err_mode == ERR_NONE) -> {
      rand_k_en -> (op == key_sign);
      pcr_sign  -> ((op == key_sign) && (curve == ecc_curve_p384) && (rand_k_en == 1'b0));
      kv_intf   == 1'b0;
    }
  }

  // Zeroize-mid-op is a random-path-only feature. Disallow it in error
  // paths (error already aborts the op) since combining them would
  // race the two abort mechanisms.
  constraint ecc_zeroize_legality_c {
    (err_mode != ERR_NONE) -> (zeroize_mid_op == 1'b0);
  }

  // Force op/curve/rand_k/pcr/kv into the illegal combination that fires the
  // targeted error gate. Non-listed axes remain free so each error test still
  // covers a range of the "don't care" dimensions.
  constraint ecc_err_mode_c {
    (err_mode == ERR_PCR_P256)      -> ((op == key_sign) && (curve == ecc_curve_p256) && (pcr_sign == 1'b1));
    (err_mode == ERR_RAND_K_PCR)    -> ((op == key_sign) && (pcr_sign == 1'b1) && (rand_k_en == 1'b1));
    (err_mode == ERR_RAND_K_KEYGEN) -> ((op == key_gen)         && (rand_k_en == 1'b1));
    (err_mode == ERR_RAND_K_VERIFY) -> ((op == key_verify)      && (rand_k_en == 1'b1));
    (err_mode == ERR_RAND_K_SHARED) -> ((op == ecdh_sharedkey)  && (rand_k_en == 1'b1));
    (err_mode == ERR_KV_P256)       -> ((kv_intf == 1'b1) && (curve == ecc_curve_p256));
    (err_mode == ERR_KV_RAND_K)     -> ((kv_intf == 1'b1) && (op == key_sign) && (rand_k_en == 1'b1));
  }

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //*******************************************************************
  //*******************************************************************
  // Macros that define structs and associated functions are
  // located in ECC_in_macros.svh

  //*******************************************************************
  // Monitor macro used by ECC_in_monitor and ECC_in_monitor_bfm
  // This struct is defined in ECC_in_macros.svh
  `ECC_in_MONITOR_STRUCT
    ECC_in_monitor_s ECC_in_monitor_struct;
  //*******************************************************************
  // FUNCTION: to_monitor_struct()
  // This function packs transaction variables into a ECC_in_monitor_s
  // structure.  The function returns the handle to the ECC_in_monitor_struct.
  // This function is defined in ECC_in_macros.svh
  `ECC_in_TO_MONITOR_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_monitor_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in ECC_in_macros.svh
  `ECC_in_FROM_MONITOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Initiator macro used by ECC_in_driver and ECC_in_driver_bfm
  // to communicate initiator driven data to ECC_in_driver_bfm.
  // This struct is defined in ECC_in_macros.svh
  `ECC_in_INITIATOR_STRUCT
    ECC_in_initiator_s ECC_in_initiator_struct;
  //*******************************************************************
  // FUNCTION: to_initiator_struct()
  // This function packs transaction variables into a ECC_in_initiator_s
  // structure.  The function returns the handle to the ECC_in_initiator_struct.
  // This function is defined in ECC_in_macros.svh
  `ECC_in_TO_INITIATOR_STRUCT_FUNCTION  
  //*******************************************************************
  // FUNCTION: from_initiator_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in ECC_in_macros.svh
  `ECC_in_FROM_INITIATOR_STRUCT_FUNCTION 

  //*******************************************************************
  // Responder macro used by ECC_in_driver and ECC_in_driver_bfm
  // to communicate Responder driven data to ECC_in_driver_bfm.
  // This struct is defined in ECC_in_macros.svh
  `ECC_in_RESPONDER_STRUCT
    ECC_in_responder_s ECC_in_responder_struct;
  //*******************************************************************
  // FUNCTION: to_responder_struct()
  // This function packs transaction variables into a ECC_in_responder_s
  // structure.  The function returns the handle to the ECC_in_responder_struct.
  // This function is defined in ECC_in_macros.svh
  `ECC_in_TO_RESPONDER_STRUCT_FUNCTION 
  //*******************************************************************
  // FUNCTION: from_responder_struct()
  // This function unpacks the struct provided as an argument into transaction 
  // variables of this class.
  // This function is defined in ECC_in_macros.svh
  `ECC_in_FROM_RESPONDER_STRUCT_FUNCTION 
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
    return $sformatf("test:%s op:%s curve:%s err_mode:%s rand_k_en:%0d pcr_sign:%0d kv_intf:%0d kv_slot:%0d pollute_upper:%0d zeroize_mid_op:%0d zeroize_delay_clks:%0d",
                     test.name(), op.name(), curve.name(), err_mode.name(),
                     rand_k_en, pcr_sign, kv_intf, kv_slot, pollute_upper,
                     zeroize_mid_op, zeroize_delay_clks);
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
    ECC_in_transaction #(
        .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
        .AHB_DATA_WIDTH(AHB_DATA_WIDTH)
        )
 RHS;
    if (!$cast(RHS,rhs)) return 0;
    // pragma uvmf custom do_compare begin
    // UVMF_CHANGE_ME : Eliminate comparison of variables not to be used for compare
    return (super.do_compare(rhs,comparer)
            &&(this.test == RHS.test)
            &&(this.op == RHS.op)
            &&(this.curve == RHS.curve)
            &&(this.err_mode == RHS.err_mode)
            &&(this.rand_k_en == RHS.rand_k_en)
            &&(this.pcr_sign == RHS.pcr_sign)
            &&(this.kv_intf == RHS.kv_intf)
            &&(this.kv_slot == RHS.kv_slot)
            &&(this.pollute_upper == RHS.pollute_upper)
            &&(this.zeroize_mid_op == RHS.zeroize_mid_op)
            &&(this.zeroize_delay_clks == RHS.zeroize_delay_clks)
            );
    // pragma uvmf custom do_compare end
  endfunction

  //*******************************************************************
  // FUNCTION: do_copy()
  // This function is automatically called when the .copy() function
  // is called on this class.
  //
  virtual function void do_copy (uvm_object rhs);
    ECC_in_transaction #(
        .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
        .AHB_DATA_WIDTH(AHB_DATA_WIDTH)
        )
 RHS;
    assert($cast(RHS,rhs));
    // pragma uvmf custom do_copy begin
    super.do_copy(rhs);
    this.test = RHS.test;
    this.op = RHS.op;
    this.curve = RHS.curve;
    this.err_mode = RHS.err_mode;
    this.rand_k_en = RHS.rand_k_en;
    this.pcr_sign = RHS.pcr_sign;
    this.kv_intf = RHS.kv_intf;
    this.kv_slot = RHS.kv_slot;
    this.pollute_upper = RHS.pollute_upper;
    this.zeroize_mid_op = RHS.zeroize_mid_op;
    this.zeroize_delay_clks = RHS.zeroize_delay_clks;
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
      transaction_view_h = $begin_transaction(transaction_viewing_stream_h,"ECC_in_transaction",start_time);
    end
    super.add_to_wave(transaction_view_h);
    // pragma uvmf custom add_to_wave begin
    // UVMF_CHANGE_ME : Color can be applied to transaction entries based on content, example below
    // case()
    //   1 : $add_color(transaction_view_h,"red");
    //   default : $add_color(transaction_view_h,"grey");
    // endcase
    // UVMF_CHANGE_ME : Eliminate transaction variables not wanted in transaction viewing in the waveform viewer
    $add_attribute(transaction_view_h,test,"test");
    $add_attribute(transaction_view_h,op,"op");
    $add_attribute(transaction_view_h,curve,"curve");
    $add_attribute(transaction_view_h,err_mode,"err_mode");
    $add_attribute(transaction_view_h,rand_k_en,"rand_k_en");
    $add_attribute(transaction_view_h,pcr_sign,"pcr_sign");
    $add_attribute(transaction_view_h,kv_intf,"kv_intf");
    $add_attribute(transaction_view_h,kv_slot,"kv_slot");
    $add_attribute(transaction_view_h,pollute_upper,"pollute_upper");
    $add_attribute(transaction_view_h,zeroize_mid_op,"zeroize_mid_op");
    $add_attribute(transaction_view_h,zeroize_delay_clks,"zeroize_delay_clks");
    // pragma uvmf custom add_to_wave end
    $end_transaction(transaction_view_h,end_time);
    $free_transaction(transaction_view_h);
    `endif // QUESTA
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

