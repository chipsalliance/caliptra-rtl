//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
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
//   ECC_in_agent_ae receives transactions of type  ECC_in_transaction #()
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//  ECC_sb_ap broadcasts transactions of type ECC_out_transaction #()
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class ECC_predictor #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( ECC_predictor #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;

  
  // Instantiate the analysis exports
  uvm_analysis_imp_ECC_in_agent_ae #(ECC_in_transaction #(), ECC_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) ECC_in_agent_ae;

  
  // Instantiate the analysis ports
  uvm_analysis_port #(ECC_out_transaction #()) ECC_sb_ap;


  // Transaction variable for predicted values to be sent out ECC_sb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef ECC_out_transaction #() ECC_sb_ap_output_transaction_t;
  ECC_sb_ap_output_transaction_t ECC_sb_ap_output_transaction;
  // Code for sending output transaction out through ECC_sb_ap
  // ECC_sb_ap.write(ECC_sb_ap_output_transaction);

  // Define transaction handles for debug visibility 
  ECC_in_transaction #() ECC_in_agent_ae_debug;


  // pragma uvmf custom class_item_additional begin

  reg [383:0] tmp_data;
  reg [383:0] privkey;
  reg [383:0] pubkey_x;
  reg [383:0] pubkey_y;
  reg [383:0] R;
  reg [383:0] S;
  reg [383:0] verify_R;

  int line_skip;
  int cnt_tmp;
  int fd_r;
  int values_per_test_vector = 8;
  
  string line_read;
  string file_name;

  // pragma uvmf custom class_item_additional end

  // FUNCTION: new
  function new(string name, uvm_component parent);
     super.new(name,parent);
  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);

    ECC_in_agent_ae = new("ECC_in_agent_ae", this);
    ECC_sb_ap =new("ECC_sb_ap", this );
  // pragma uvmf custom build_phase begin
  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_ECC_in_agent_ae
  // Transactions received through ECC_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_ECC_in_agent_ae(ECC_in_transaction #() t);
    // pragma uvmf custom ECC_in_agent_ae_predictor begin
    ECC_in_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through ECC_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    ECC_sb_ap_output_transaction = ECC_sb_ap_output_transaction_t::type_id::create("ECC_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    //`uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    //`uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The ECC_predictor::write_ECC_in_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    //`uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    if ((t.test == ecc_reset_test) || (t.test == ecc_otf_reset_test)) begin
      /*
      $display("**ECC_predictor** test = %0s", t.test.name());
      $display("**ECC_predictor** op = %0s", t.op.name());
      */
      ECC_sb_ap_output_transaction.result_privkey   = 0;
      ECC_sb_ap_output_transaction.result_pubkey_x  = 0;
      ECC_sb_ap_output_transaction.result_pubkey_y  = 0;
      ECC_sb_ap_output_transaction.result_R         = 0;
      ECC_sb_ap_output_transaction.result_S         = 0; 
      ECC_sb_ap_output_transaction.result_verify_R  = 0;
      /*
      $display("**ECC_predictor** privkey = %96x", ECC_sb_ap_output_transaction.result_privkey);
      $display("**ECC_predictor** pubkey_x = %96x", ECC_sb_ap_output_transaction.result_pubkey_x);
      $display("**ECC_predictor** pubkey_y = %96x", ECC_sb_ap_output_transaction.result_pubkey_y);
      $display("**ECC_predictor** result_R = %96x", ECC_sb_ap_output_transaction.result_R);
      $display("**ECC_predictor** result_S = %96x", ECC_sb_ap_output_transaction.result_S);
      $display("**ECC_predictor** verify_R = %96x", ECC_sb_ap_output_transaction.result_verify_R);
      */

    end
    else if (t.test == ecc_normal_test) begin 
      /*
      $display("**ECC_predictor** test = %0s", t.test.name());
      $display("**ECC_predictor** op = %0s", t.op.name());
      */
      file_name = "secp384_testvector.hex";

      // ATTN: Must match the number of fields generated by gen_mm_test_vectors.py script
      values_per_test_vector = 8;

      fd_r = $fopen(file_name, "r");
      if (fd_r == 0)
        //$error("** ECC-in_driver_bfm ** Can't open file %s", file_name);
        `uvm_fatal("PREDICT", "FILE_READ_ERROR: Can't open input vector file")

      // Get hashed message, private key, public key x, public key y, k and R
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", tmp_data); // hashed_msg, not used by predictor
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", privkey);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", pubkey_x);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", pubkey_y);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", tmp_data); // seed, not used by predictor
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", tmp_data); // nonce, not used by predictor
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", R);
      $fgets(line_read, fd_r); 
      $sscanf(line_read, "%h", S);
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%h", tmp_data); // IV, not used by predictor

      $fclose(fd_r);

      if (t.op == key_gen) begin
        ECC_sb_ap_output_transaction.result_privkey   = privkey;
        ECC_sb_ap_output_transaction.result_pubkey_x  = pubkey_x;
        ECC_sb_ap_output_transaction.result_pubkey_y  = pubkey_y;
        ECC_sb_ap_output_transaction.result_R         = 0;
        ECC_sb_ap_output_transaction.result_S         = 0; 
        ECC_sb_ap_output_transaction.result_verify_R  = 0;
      end
      else if (t.op == key_sign) begin
        ECC_sb_ap_output_transaction.result_privkey   = 0;
        ECC_sb_ap_output_transaction.result_pubkey_x  = 0;
        ECC_sb_ap_output_transaction.result_pubkey_y  = 0;
        ECC_sb_ap_output_transaction.result_R         = R;
        ECC_sb_ap_output_transaction.result_S         = S; 
        ECC_sb_ap_output_transaction.result_verify_R  = 0;
      end
      else if (t.op == key_verify) begin
        ECC_sb_ap_output_transaction.result_privkey   = 0;
        ECC_sb_ap_output_transaction.result_pubkey_x  = 0;
        ECC_sb_ap_output_transaction.result_pubkey_y  = 0;
        ECC_sb_ap_output_transaction.result_R         = 0;
        ECC_sb_ap_output_transaction.result_S         = 0; 
        ECC_sb_ap_output_transaction.result_verify_R  = R;
      end

      

     `uvm_info("PREDICT",{"ECC_OUT: ",ECC_sb_ap_output_transaction.convert2string()},UVM_MEDIUM)
    
    end

    // Code for sending output transaction out through ECC_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    ECC_sb_ap.write(ECC_sb_ap_output_transaction);
    // pragma uvmf custom ECC_in_agent_ae_predictor end
  endfunction


endclass 

// pragma uvmf custom external begin
// pragma uvmf custom external end

