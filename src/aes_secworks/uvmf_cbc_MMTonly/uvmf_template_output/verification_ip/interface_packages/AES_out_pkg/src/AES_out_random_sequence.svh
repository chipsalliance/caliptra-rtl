//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
// This sequences randomizes the AES_out transaction and sends it 
// to the UVM driver.
//
// This sequence constructs and randomizes a AES_out_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class AES_out_random_sequence #(
      int AHB_DATA_WIDTH = 32,
      int AHB_ADDR_WIDTH = 32,
      int OUTPUT_TEXT_WIDTH = 1280,
      bit BYPASS_HSEL = 0
      )

  extends AES_out_sequence_base #(
      .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
      .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
      .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
      .BYPASS_HSEL(BYPASS_HSEL)
      )
;

  `uvm_object_param_utils( AES_out_random_sequence #(
                           AHB_DATA_WIDTH,
                           AHB_ADDR_WIDTH,
                           OUTPUT_TEXT_WIDTH,
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
      req=AES_out_transaction#(
                .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
                .BYPASS_HSEL(BYPASS_HSEL)
                )
::type_id::create("req");
      start_item(req);
      // Randomize the transaction
      if(!req.randomize()) `uvm_fatal("SEQ", "AES_out_random_sequence::body()-AES_out_transaction randomization failed")
      // Send the transaction to the AES_out_driver_bfm via the sequencer and AES_out_driver.
      finish_item(req);
      `uvm_info("SEQ", {"Response:",req.convert2string()},UVM_MEDIUM)

  endtask

endclass: AES_out_random_sequence

// pragma uvmf custom external begin
// pragma uvmf custom external end

