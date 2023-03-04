//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
// This file contains the class used as the base class for all sequences
// for this interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class SHA512_out_sequence_base #(
      int AHB_DATA_WIDTH = 32,
      int AHB_ADDR_WIDTH = 32,
      int OUTPUT_TEXT_WIDTH = 512,
      bit BYPASS_HSEL = 0
      )
   extends uvmf_sequence_base #(
                             .REQ(SHA512_out_transaction  #(
                                 .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                                 .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                                 .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
                                 .BYPASS_HSEL(BYPASS_HSEL)
                                 )
),
                             .RSP(SHA512_out_transaction  #(
                                 .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                                 .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                                 .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
                                 .BYPASS_HSEL(BYPASS_HSEL)
                                 )
));

  `uvm_object_param_utils( SHA512_out_sequence_base #(
                           AHB_DATA_WIDTH,
                           AHB_ADDR_WIDTH,
                           OUTPUT_TEXT_WIDTH,
                           BYPASS_HSEL
                           )
)

  // variables
  typedef SHA512_out_transaction #(
                     .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                     .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                     .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
                     .BYPASS_HSEL(BYPASS_HSEL)
                     )
 SHA512_out_transaction_req_t;
  SHA512_out_transaction_req_t req;
  typedef SHA512_out_transaction #(
                     .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                     .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                     .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH),
                     .BYPASS_HSEL(BYPASS_HSEL)
                     )
 SHA512_out_transaction_rsp_t;
  SHA512_out_transaction_rsp_t rsp;

  // Event for identifying when a response was received from the sequencer
  event new_rsp;


  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  // TASK : get_responses()
  // This task recursively gets sequence item responses from the sequencer.
  //
  virtual task get_responses();
    fork
      begin
        // Block until new rsp available
        get_response(rsp);
        // New rsp received.  Indicate to sequence using event.
        ->new_rsp;
        // Display the received response transaction
        `uvm_info("SEQ", {"New response transaction:",rsp.convert2string()}, UVM_MEDIUM)
      end
    join_none
  endtask

  // ****************************************************************************
  // TASK : pre_body()
  // This task is called automatically when start is called with call_pre_post set to 1 (default).
  // By calling get_responses() within pre_body() any derived sequences are automatically 
  // processing response transactions. Only un-comment this call to get_responses() if you
  // have configured the interface driver to utilize the response transaction path by setting
  // the configuration variable "return_transaction_response" to 1. Otherwise it is possible
  // to impact runtime performance and memory utilization.
  //
  virtual task pre_body();
    // pragma uvmf custom pre_body begin
//    get_responses();
    // pragma uvmf custom pre_body end
  endtask

  // ****************************************************************************
  // TASK : body()
  // This task is called automatically when start is called.  This sequence sends
  // a req sequence item to the sequencer identified as an argument in the call
  // to start.
  //
  virtual task body();
    // pragma uvmf custom body begin
  	start_item(req);
  	finish_item(req);
    // pragma uvmf custom body end
  endtask

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new( string name ="");
    super.new( name );
    // pragma uvmf custom new begin
    req = SHA512_out_transaction_req_t::type_id::create("req");
    rsp = SHA512_out_transaction_rsp_t::type_id::create("rsp");
    // pragma uvmf custom new end
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

