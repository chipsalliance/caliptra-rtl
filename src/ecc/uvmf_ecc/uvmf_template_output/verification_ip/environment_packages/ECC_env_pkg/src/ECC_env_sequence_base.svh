//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: This file contains environment level sequences that will
//    be reused from block to top level simulations.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class ECC_env_sequence_base #( 
      type CONFIG_T
      ) extends uvmf_virtual_sequence_base #(.CONFIG_T(CONFIG_T));


  `uvm_object_param_utils( ECC_env_sequence_base #(
                           CONFIG_T
                           ) );

  
// This ECC_env_sequence_base contains a handle to a ECC_env_configuration object 
// named configuration.  This configuration variable contains a handle to each 
// sequencer within each agent within this environment and any sub-environments.
// The configuration object handle is automatically assigned in the pre_body in the
// base class of this sequence.  The configuration handle is retrieved from the
// virtual sequencer that this sequence is started on.
// Available sequencer handles within the environment configuration:

  // Initiator agent sequencers in ECC_environment:
    // configuration.ECC_in_agent_config.sequencer

  // Responder agent sequencers in ECC_environment:
    // configuration.ECC_out_agent_config.sequencer


    typedef ECC_in_random_sequence ECC_in_agent_random_sequence_t;
    ECC_in_agent_random_sequence_t ECC_in_agent_rand_seq;





  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  function new(string name = "" );
    super.new(name);
    ECC_in_agent_rand_seq = ECC_in_agent_random_sequence_t::type_id::create("ECC_in_agent_rand_seq");


  endfunction

  virtual task body();

    if ( configuration.ECC_in_agent_config.sequencer != null )
       repeat (25) ECC_in_agent_rand_seq.start(configuration.ECC_in_agent_config.sequencer);


  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

