//----------------------------------------------------------------------
// Created with uvmf_gen version 2020.2
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION:
// Drives a HMAC_in transaction with op = last_alone_op so the BFM
// exercises the LAST-alone error path.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class HMAC_in_last_alone_error_sequence #(
      int AHB_DATA_WIDTH = 64,
      int AHB_ADDR_WIDTH = 32,
      bit BYPASS_HSEL = 0
      )
  extends HMAC_in_sequence_base #(
      .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
      .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
      .BYPASS_HSEL(BYPASS_HSEL)
      );

  `uvm_object_param_utils( HMAC_in_last_alone_error_sequence #(
                           AHB_DATA_WIDTH,
                           AHB_ADDR_WIDTH,
                           BYPASS_HSEL
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
      req=HMAC_in_transaction#(
                .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                .BYPASS_HSEL(BYPASS_HSEL)
                )::type_id::create("req");
      start_item(req);
      if(!req.randomize()) `uvm_fatal("SEQ", "HMAC_in_last_alone_error_sequence::body()-HMAC_in_transaction randomization failed")
      req.op = last_alone_op;
      finish_item(req);
      `uvm_info("SEQ", {"Response:",req.convert2string()},UVM_MEDIUM)
    end

  endtask

endclass: HMAC_in_last_alone_error_sequence
