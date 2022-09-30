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
class ECC_in_otf_reset_sequence #(
      int AHB_DATA_WIDTH = 32,
      int AHB_ADDR_WIDTH = 32
      )
  extends ECC_in_sequence_base #(
      .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
      .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH)

      );

  `uvm_object_param_utils( ECC_in_otf_reset_sequence #(
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
    begin
      // Construct the transaction
      req=ECC_in_transaction#(
                .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH)
                )::type_id::create("req");
      start_item(req);
      // Randomize the transaction
      if(!req.randomize()) `uvm_fatal("SEQ", "ECC_in_otf_reset_sequence::body()-ECC_in_transaction randomization failed")
      // set the operation
      req.op = otf_reset_op;
      $display("*** ANJANA*** op = %h", req.op);
      // Send the transaction to the ECC_in_driver_bfm via the sequencer and ECC_in_driver.
      finish_item(req);
      `uvm_info("SEQ", {"Response:",req.convert2string()},UVM_MEDIUM)
    end

  endtask

endclass: ECC_in_otf_reset_sequence

