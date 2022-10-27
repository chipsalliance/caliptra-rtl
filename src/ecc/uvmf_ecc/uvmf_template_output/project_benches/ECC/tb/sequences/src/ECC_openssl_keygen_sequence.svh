// ==============================================================================
// =====            Mentor Graphics UK Ltd                                  =====
// =====            Rivergate, London Road, Newbury BERKS RG14 2QB          =====
// ==============================================================================
// ==============================================================================
// This unpublished work contains proprietary information.
// All right reserved. Supplied in confidence and must not be copied, used or disclosed 
// for any purpose without express written permission.
// 2019 @ Copyright Mentor Graphics UK Ltd
// ==============================================================================


`ifndef __ECC_OPENSSL_KEYGEN_SEQUENCE
`define __ECCC_OPENSSL_KEYGEN_SEQUENCE

`include "uvm_macros.svh"

class ECC_openssl_keygen_sequence #(int AHB_DATA_WIDTH = 32,
                            int AHB_ADDR_WIDTH = 32
                            ) extends ECC_bench_sequence_base;

  `uvm_object_utils(ECC_openssl_keygen_sequence) 

  // Define type and handle for reset sequence
  typedef ECC_in_openssl_keygen_sequence #(AHB_DATA_WIDTH, AHB_ADDR_WIDTH) ECC_in_openssl_keygen_sequence_t;
  ECC_in_openssl_keygen_sequence_t ECC_in_openssl_keygen_s;
  
  // constructor
  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual task body();
    //ECC_in_agent_random_seq = ECC_in_random_sequence#()::type_id::create("ECC_in_agent_random_seq");
    ECC_in_openssl_keygen_s = ECC_in_openssl_keygen_sequence#()::type_id::create("ECC_in_openssl_keygen_s");
   
    fork
      ECC_in_agent_config.wait_for_reset();
      ECC_out_agent_config.wait_for_reset();
    join

    //repeat (10) ECC_in_agent_random_seq.start(ECC_in_agent_sequencer);
    repeat (1000) ECC_in_openssl_keygen_s.start(ECC_in_agent_sequencer);
    //repeat (5) ECC_in_agent_random_seq.start(ECC_in_agent_sequencer);
    fork
      ECC_in_agent_config.wait_for_num_clocks(400);    
      ECC_out_agent_config.wait_for_num_clocks(400);
    join
    
  endtask


endclass : ECC_openssl_keygen_sequence

`endif
