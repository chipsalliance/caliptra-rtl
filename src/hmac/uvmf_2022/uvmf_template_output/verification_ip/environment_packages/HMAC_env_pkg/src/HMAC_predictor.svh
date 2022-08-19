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
//   HMAC_in_agent_ae receives transactions of type  HMAC_in_transaction #()
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//  HMAC_sb_ap broadcasts transactions of type HMAC_out_transaction #()
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class HMAC_predictor #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( HMAC_predictor #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;

  
  // Instantiate the analysis exports
  uvm_analysis_imp_HMAC_in_agent_ae #(HMAC_in_transaction #(), HMAC_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) HMAC_in_agent_ae;

  
  // Instantiate the analysis ports
  uvm_analysis_port #(HMAC_out_transaction #()) HMAC_sb_ap;


  // Transaction variable for predicted values to be sent out HMAC_sb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef HMAC_out_transaction #() HMAC_sb_ap_output_transaction_t;
  HMAC_sb_ap_output_transaction_t HMAC_sb_ap_output_transaction;
  // Code for sending output transaction out through HMAC_sb_ap
  // HMAC_sb_ap.write(HMAC_sb_ap_output_transaction);

  // Define transaction handles for debug visibility 
  HMAC_in_transaction #() HMAC_in_agent_ae_debug;


  // pragma uvmf custom class_item_additional begin
  reg [383:0] expected;
  reg [383:0] tmp;
  reg [8:0] test_case_sel;

  int line_skip;
  int cnt_tmp;
  int fd_r;

  string line_read;
  string tmp_str1;
  string tmp_str2;
  string file_name;

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

    HMAC_in_agent_ae = new("HMAC_in_agent_ae", this);
    HMAC_sb_ap =new("HMAC_sb_ap", this );
  // pragma uvmf custom build_phase begin
  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_HMAC_in_agent_ae
  // Transactions received through HMAC_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_HMAC_in_agent_ae(HMAC_in_transaction #() t);
    // pragma uvmf custom HMAC_in_agent_ae_predictor begin
    HMAC_in_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through HMAC_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    HMAC_sb_ap_output_transaction = HMAC_sb_ap_output_transaction_t::type_id::create("HMAC_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    //`uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    //`uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The HMAC_predictor::write_HMAC_in_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    //`uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
 
    //$display("**HMAC_predictor** t.op= %d",t.op);
    //$display("**HMAC_predictor** t.test_case_sel = %d",t.test_case_sel);
    //$display("**HMAC_predictor** t.key_len = %d",t.key_len);

    if (t.op== 2'b00) HMAC_sb_ap_output_transaction.result = 0;
    else begin
      if (t.op == 2'b01) file_name = "../../../../../tb/hmac_vectors_singleblk.txt";
      else               file_name = "../../../../../tb/hmac_vectors_multiblk.txt";

      cnt_tmp = 0;

      if (t.op == 2'b01) test_case_sel = t.test_case_sel;
      else test_case_sel = {8'h00,t.test_case_sel[0]};

      cnt_tmp = 0;
      //file_name = "/home/kupadhyayula/caliptra/ws1/Caliptra/src/hmac/tb/hmac_vectors.txt";
      
      //line_skip = test_case_sel * 5 + 10;
      fd_r = $fopen(file_name, "r");
      if(!fd_r) $display("**HMAC_predictor** Cannot open file %s", file_name);

      //while (cnt_tmp < line_skip) begin
      //  cnt_tmp = cnt_tmp + 1;
      //  $fgets(line_read, fd_r);
      //end
      $fgets(line_read, fd_r);
      $sscanf(line_read, "%s %s %h", tmp_str1, tmp_str2, tmp);
      while (tmp_str1 != "COUNT" || tmp != test_case_sel) begin
        $fgets(line_read, fd_r);
        $sscanf(line_read, "%s %s %h", tmp_str1, tmp_str2, tmp);
      end

      //Get tag:
      $sscanf(line_read, "%s %s %h", tmp_str1, tmp_str2, tmp);
      while (tmp_str1 != "TAG") begin
        $fgets(line_read, fd_r);
        $sscanf(line_read, "%s %s %h", tmp_str1, tmp_str2, tmp);
      end
      expected = tmp;

      HMAC_sb_ap_output_transaction.result = expected;
      `uvm_info("PREDICT",{"HMAC_OUT: ",HMAC_sb_ap_output_transaction.convert2string()},UVM_MEDIUM);

    end

    // Code for sending output transaction out through HMAC_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    HMAC_sb_ap.write(HMAC_sb_ap_output_transaction);
    // pragma uvmf custom HMAC_in_agent_ae_predictor end
  endfunction


endclass 

// pragma uvmf custom external begin
// pragma uvmf custom external end

