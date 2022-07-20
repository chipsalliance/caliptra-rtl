//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.1
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
//
// DESCRIPTION: This analysis component contains analysis_exports for receiving
//   data and analysis_ports for sending data.
// 
//   This analysis component has the following analysis_exports that receive the 
//   listed transaction type.
//   
//   AES_in_agent_ae receives transactions of type  AES_in_transaction #()
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//  AES_sb_ap broadcasts transactions of type AES_out_transaction #()
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class AES_predictor #(
  type CONFIG_T
  )
 extends uvm_component;

  // Factory registration of this class
  `uvm_component_param_utils( AES_predictor #(
                              CONFIG_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;

  
  // Instantiate the analysis exports
  uvm_analysis_imp_AES_in_agent_ae #(AES_in_transaction #(), AES_predictor #(
                              .CONFIG_T(CONFIG_T)
                              )
) AES_in_agent_ae;

  
  // Instantiate the analysis ports
  uvm_analysis_port #(AES_out_transaction #()) AES_sb_ap;


  // Transaction variable for predicted values to be sent out AES_sb_ap
  typedef AES_out_transaction #() AES_sb_ap_output_transaction_t;
  AES_sb_ap_output_transaction_t AES_sb_ap_output_transaction;
  // Code for sending output transaction out through AES_sb_ap
  // AES_sb_ap.write(AES_sb_ap_output_transaction);

  // Define transaction handles for debug visibility 
  AES_in_transaction #() AES_in_agent_ae_debug;


  // pragma uvmf custom class_item_additional begin
  parameter [127:0] TEXT_ARRAY [3 : 0]   = {128'h6bc1bee22e409f96e93d7e117393172a,
                                        128'hae2d8a571e03ac9c9eb76fac45af8e51,
                                        128'h30c81c46a35ce411e5fbc1191a0a52ef,
                                        128'hf69f2445df4f9b17ad2b417be66c3710};
  
  parameter [127:0] EXPECTED_ARRAY [3 : 0]   = {128'h3ad77bb40d7a3660a89ecaf32466ef97,
                                                128'hf5d3d58503b9699de785895a96fdbaaf,
                                                128'h43b1cd7f598ece23881b00e3ed030688,
                                                128'h7b0c785e27e8ad3f8223207104725dd4};
  // pragma uvmf custom class_item_additional end

  // FUNCTION: new
  function new(string name, uvm_component parent);
     super.new(name,parent);
    `uvm_warning("PREDICTOR_REVIEW", "This predictor has been created either through generation or re-generation with merging.  Remove this warning after the predictor has been reviewed.")
  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);

    AES_in_agent_ae = new("AES_in_agent_ae", this);
    AES_sb_ap =new("AES_sb_ap", this );
  // pragma uvmf custom build_phase begin
  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_AES_in_agent_ae
  // Transactions received through AES_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_AES_in_agent_ae(AES_in_transaction #() t);
    // pragma uvmf custom AES_in_agent_ae_predictor begin
    AES_in_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through AES_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    AES_sb_ap_output_transaction = AES_sb_ap_output_transaction_t::type_id::create("AES_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    // `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    // `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The AES_predictor::write_AES_in_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    // `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
  
    case (t.op)
      decipher_op: begin
        AES_sb_ap_output_transaction.result = TEXT_ARRAY[t.test_case_sel];
        `uvm_info("PREDICT",{"AES_OUT: ",AES_sb_ap_output_transaction.convert2string()},UVM_MEDIUM);
      end
      encipher_op: begin
        AES_sb_ap_output_transaction.result = EXPECTED_ARRAY[t.test_case_sel];
        `uvm_info("PREDICT",{"AES_OUT: ",AES_sb_ap_output_transaction.convert2string()},UVM_MEDIUM);
      end
      default: begin
        AES_sb_ap_output_transaction.result = TEXT_ARRAY[t.test_case_sel];
        `uvm_info("PREDICT",{"AES_OUT: ",AES_sb_ap_output_transaction.convert2string()},UVM_MEDIUM);
      end
    endcase
    
    // Code for sending output transaction out through AES_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    AES_sb_ap.write(AES_sb_ap_output_transaction);
    // pragma uvmf custom AES_in_agent_ae_predictor end
  endfunction


endclass 

// pragma uvmf custom external begin
// pragma uvmf custom external end

