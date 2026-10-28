//----------------------------------------------------------------------
// Created with uvmf_gen version 2020.2
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
// This sequences randomizes the ECC_in transaction and sends it 
// to the UVM driver.
//
// This sequence constructs and randomizes a ECC_in_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class ECC_in_normal_sequence #(
      int AHB_DATA_WIDTH = 64,
      int AHB_ADDR_WIDTH = 32
      )
  extends ECC_in_sequence_base #(
      .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
      .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH)

      );

  `uvm_object_param_utils( ECC_in_normal_sequence #(
                           AHB_DATA_WIDTH,
                           AHB_ADDR_WIDTH
                           ))

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  //*****************************************************************
  function new(string name = "");
    super.new(name);
  endfunction: new

  // ****************************************************************************
  // TASK : body()
  // This task is automatically executed when this sequence is started using the 
  // start(sequencerHandle) task.
  //
  task body();
    string operation;
    bit select_operation;
    ecc_in_op_transactions selected_operation;
    begin
      select_operation = $value$plusargs("ECC_OPERATION=%s", operation);
      selected_operation = key_gen;
      if (select_operation) begin
        case (operation)
          "keygen": selected_operation = key_gen;
          "signing": selected_operation = key_sign;
          "verifying": selected_operation = key_verify;
          "ecdh": selected_operation = ecdh_sharedkey;
          default: `uvm_fatal("ECC_OPERATION", {"Unknown ECC_OPERATION: ", operation})
        endcase
      end
      // Construct the transaction
      req=ECC_in_transaction#(
                .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH)
                )::type_id::create("req");
      start_item(req);
      // Randomize the transaction
      if (!req.randomize() with {
        test == ecc_normal_test;
        if (local::select_operation) op == local::selected_operation;
      }) `uvm_fatal("SEQ", "ECC_in_normal_sequence::body()-ECC_in_transaction randomization failed")
      // set the operation
      //req.test = ecc_normal_test;
      //$display("*** ANJANA*** op = %h", req.test);
      // Send the transaction to the ECC_in_driver_bfm via the sequencer and ECC_in_driver.
      `uvm_info("SEQ", {"Response:",req.convert2string()},UVM_MEDIUM)
      finish_item(req);
    end

  endtask

endclass: ECC_in_normal_sequence
