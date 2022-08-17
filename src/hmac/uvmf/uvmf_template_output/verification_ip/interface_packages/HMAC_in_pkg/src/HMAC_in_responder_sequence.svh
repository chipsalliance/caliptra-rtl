//----------------------------------------------------------------------
// Created with uvmf_gen version 2021.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This class can be used to provide stimulus when an interface
//              has been configured to run in a responder mode. It
//              will never finish by default, always going back to the driver
//              and driver BFM for the next transaction with which to respond.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class HMAC_in_responder_sequence #(
      int AHB_DATA_WIDTH = 32,
      int AHB_ADDR_WIDTH = 32,
      bit BYPASS_HSEL = 0
      )
  extends HMAC_in_sequence_base #(
      .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
      .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
      .BYPASS_HSEL(BYPASS_HSEL)
      );

  `uvm_object_param_utils( HMAC_in_responder_sequence #(
                           AHB_DATA_WIDTH,
                           AHB_ADDR_WIDTH,
                           BYPASS_HSEL
                           ))

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  function new(string name = "HMAC_in_responder_sequence");
    super.new(name);
  endfunction

  task body();
    req=HMAC_in_transaction#(
                .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                .BYPASS_HSEL(BYPASS_HSEL)
                )::type_id::create("req");
    forever begin
      start_item(req);
      finish_item(req);
      // pragma uvmf custom body begin
      // UVMF_CHANGE_ME : Do something here with the resulting req item.  The
      // finish_item() call above will block until the req transaction is ready
      // to be handled by the responder sequence.
      // If this was an item that required a response, the expectation is
      // that the response should be populated within this transaction now.
      `uvm_info("SEQ",$sformatf("Processed txn: %s",req.convert2string()),UVM_HIGH)
      // pragma uvmf custom body end
    end
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

