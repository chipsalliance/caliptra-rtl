//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
// This file contains the UVM register adapter for the AES_in interface.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class AES_in2reg_adapter #(
      int AHB_DATA_WIDTH = 32,
      int AHB_ADDR_WIDTH = 32,
      bit BYPASS_HSEL = 0
      )
 extends uvm_reg_adapter;

  `uvm_object_param_utils( AES_in2reg_adapter #(
                           AHB_DATA_WIDTH,
                           AHB_ADDR_WIDTH,
                           BYPASS_HSEL
                           )
)
  
  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

  //--------------------------------------------------------------------
  // new
  //--------------------------------------------------------------------
  function new (string name = "AES_in2reg_adapter" );
    super.new(name);
    // pragma uvmf custom new begin
    // UVMF_CHANGE_ME : Configure the adapter regarding byte enables and provides response.

    // Does the protocol the Agent is modeling support byte enables?
    // 0 = NO
    // 1 = YES
    supports_byte_enable = 0;

    // Does the Agent's Driver provide separate response sequence items?
    // i.e. Does the driver call seq_item_port.put() 
    // and do the sequences call get_response()?
    // 0 = NO
    // 1 = YES
    provides_responses = 0;
    // pragma uvmf custom new end

  endfunction: new

  //--------------------------------------------------------------------
  // reg2bus
  //--------------------------------------------------------------------
  virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);

    AES_in_transaction #(
                    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                    .BYPASS_HSEL(BYPASS_HSEL)
                    )
 trans_h = AES_in_transaction #(
                             .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                             .BYPASS_HSEL(BYPASS_HSEL)
                             )
::type_id::create("trans_h");
    
    // pragma uvmf custom reg2bus begin
    // UVMF_CHANGE_ME : Fill in the reg2bus adapter mapping registe fields to protocol fields.

    //Adapt the following for your sequence item type
    // trans_h.op = (rw.kind == UVM_READ) ? WB_READ : WB_WRITE;
    //Copy over address
    // trans_h.addr = rw.addr;
    //Copy over write data
    // trans_h.data = rw.data;

    // pragma uvmf custom reg2bus end
    
    // Return the adapted transaction
    return trans_h;

  endfunction: reg2bus

  //--------------------------------------------------------------------
  // bus2reg
  //--------------------------------------------------------------------
  virtual function void bus2reg(uvm_sequence_item bus_item,
                                ref uvm_reg_bus_op rw);
    AES_in_transaction #(
        .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
        .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
        .BYPASS_HSEL(BYPASS_HSEL)
        )
 trans_h;
    if (!$cast(trans_h, bus_item)) begin
      `uvm_fatal("ADAPT","Provided bus_item is not of the correct type")
      return;
    end
    // pragma uvmf custom bus2reg begin
    // UVMF_CHANGE_ME : Fill in the bus2reg adapter mapping protocol fields to register fields.
    //Adapt the following for your sequence item type
    //Copy over instruction type 
    // rw.kind = (trans_h.op == WB_WRITE) ? UVM_WRITE : UVM_READ;
    //Copy over address
    // rw.addr = trans_h.addr;
    //Copy over read data
    // rw.data = trans_h.data;
    //Check for errors on the bus and return UVM_NOT_OK if there is an error
    // rw.status = UVM_IS_OK;
    // pragma uvmf custom bus2reg end

  endfunction: bus2reg

endclass : AES_in2reg_adapter

// pragma uvmf custom external begin
// pragma uvmf custom external end

