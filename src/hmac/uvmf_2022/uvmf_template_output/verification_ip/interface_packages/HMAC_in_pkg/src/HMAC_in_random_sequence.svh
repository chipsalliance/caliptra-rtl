//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
// This sequences randomizes the HMAC_in transaction and sends it 
// to the UVM driver.
//
// This sequence constructs and randomizes a HMAC_in_transaction.
// 
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class HMAC_in_random_sequence #(
      int AHB_DATA_WIDTH = 32,
      int AHB_ADDR_WIDTH = 32,
      bit BYPASS_HSEL = 0
      )

  extends HMAC_in_sequence_base #(
      .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
      .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
      .BYPASS_HSEL(BYPASS_HSEL)
      )
;

  `uvm_object_param_utils( HMAC_in_random_sequence #(
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
      int i;
      bit [1023:0] block;
      // Construct the transaction
      req=HMAC_in_transaction#(
                .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                .BYPASS_HSEL(BYPASS_HSEL)
                )
::type_id::create("req");
      start_item(req);
      // Randomize the transaction
      if(!req.randomize()) `uvm_fatal("SEQ", "HMAC_in_random_sequence::body()-HMAC_in_transaction randomization failed")
      
      if ($urandom_range(0, 1) == 0) begin
        req.op = hmac384_op;
      end else begin
          req.op = hmac512_op;
      end

      `uvm_info("SEQ", {"Request:",req.convert2string()},UVM_MEDIUM)
      // Send the transaction to the HMAC_in_driver_bfm via the sequencer and HMAC_in_driver.
      finish_item(req);
      //`uvm_info("SEQ", {"Response:",req.convert2string()},UVM_MEDIUM)

  endtask

endclass: HMAC_in_random_sequence

// pragma uvmf custom external begin
// pragma uvmf custom external end

