//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
// This sequences randomizes the AES_in transaction and sends it 
// to the UVM driver.
//
// This sequence constructs and randomizes a AES_in_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class AES_in_random_sequence #(
      int AHB_DATA_WIDTH = 32,
      int AHB_ADDR_WIDTH = 32,
      bit BYPASS_HSEL = 0
      )

  extends AES_in_sequence_base #(
      .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
      .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
      .BYPASS_HSEL(BYPASS_HSEL)
      )
;

  `uvm_object_param_utils( AES_in_random_sequence #(
                           AHB_DATA_WIDTH,
                           AHB_ADDR_WIDTH,
                           BYPASS_HSEL
                           )
)

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
  
      // Construct the transaction
      req=AES_in_transaction#(
                .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                .BYPASS_HSEL(BYPASS_HSEL)
                )
::type_id::create("req");
      start_item(req);
      // Randomize the transaction
      if(!req.randomize()) `uvm_fatal("SEQ", "AES_in_random_sequence::body()-AES_in_transaction randomization failed")
      // Send the transaction to the AES_in_driver_bfm via the sequencer and AES_in_driver.
      finish_item(req);
      `uvm_info("SEQ", {"Response:",req.convert2string()},UVM_MEDIUM)

  endtask

endclass: AES_in_random_sequence

// pragma uvmf custom external begin
// pragma uvmf custom external end

