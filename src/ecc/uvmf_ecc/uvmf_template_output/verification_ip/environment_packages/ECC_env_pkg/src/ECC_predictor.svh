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
  reg [383:0] privkeyB;
  reg [383:0] dh_sharedkey;

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

  // TASK: run_phase
  // Emit one zero-transaction at simulation start to match the ECC_out
  // monitor's reset-time emission (see ECC_out_monitor_bfm.sv do_monitor
  // rst_n_i==0 branch, which emits a zero-struct after reset deassert).
  // Without this, the in-order scoreboard fires NO_PREDICTED_ENTRY
  // because the expected queue is empty when the reset-actual arrives.
  virtual task run_phase(uvm_phase phase);
    ECC_out_transaction #() reset_txn;
    reset_txn = ECC_out_transaction #()::type_id::create("reset_txn");
    reset_txn.result_privkey   = 0;
    reset_txn.result_pubkey_x  = 0;
    reset_txn.result_pubkey_y  = 0;
    reset_txn.result_R         = 0;
    reset_txn.result_S         = 0;
    reset_txn.result_verify_R  = 0;
    reset_txn.result_sharedkey = 0;
    ECC_sb_ap.write(reset_txn);
  endtask

  // FUNCTION: write_ECC_in_agent_ae
  // Transactions received through ECC_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_ECC_in_agent_ae(ECC_in_transaction #() t);
    // pragma uvmf custom ECC_in_agent_ae_predictor begin
    bit is_nondet;
    bit is_err;
    bit is_p256;
    string kat_file;
    ECC_in_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through ECC_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)

    is_nondet = t.rand_k_en;
    is_err    = (t.err_mode != ERR_NONE);
    is_p256   = (t.curve == ecc_curve_p256);

    // The ECC_in driver_bfm's ecc_random_test path never arms the
    // out-monitor (see comment there). Skip predictor emit for any
    // transaction that would have routed through that path so the
    // scoreboard queues stay balanced (equal length on both sides).
    if (is_nondet || is_err || is_p256 || t.pcr_sign || t.kv_intf || t.pollute_upper || t.zeroize_mid_op) begin
      `uvm_info("PRED", "Skipping expected-output emit (random-axes path)", UVM_HIGH)
      return;
    end

    // Reset/OTF-reset: expected outputs are zeros (existing behavior).
    if ((t.test == ecc_reset_test) || (t.test == ecc_otf_reset_test)) begin
      ECC_sb_ap_output_transaction = ECC_sb_ap_output_transaction_t::type_id::create("ECC_sb_ap_output_transaction");
      ECC_sb_ap_output_transaction.result_privkey    = 0;
      ECC_sb_ap_output_transaction.result_pubkey_x   = 0;
      ECC_sb_ap_output_transaction.result_pubkey_y   = 0;
      ECC_sb_ap_output_transaction.result_R          = 0;
      ECC_sb_ap_output_transaction.result_S          = 0;
      ECC_sb_ap_output_transaction.result_verify_R   = 0;
      ECC_sb_ap_output_transaction.result_sharedkey  = 0;
      ECC_sb_ap.write(ECC_sb_ap_output_transaction);
      return;
    end

    // Legal-det path: select the per-curve KAT file. The driver_bfm reads
    // the same file so the KAT values line up field-by-field.
    kat_file = is_p256 ? "secp256_testvector.hex" : "secp384_testvector.hex";
    ECC_sb_ap_output_transaction = ECC_sb_ap_output_transaction_t::type_id::create("ECC_sb_ap_output_transaction");

    fd_r = $fopen(kat_file, "r");
    if (fd_r == 0)
      `uvm_fatal("PREDICT", {"FILE_READ_ERROR: Can't open input vector file ", kat_file})

    $fgets(line_read, fd_r); $sscanf(line_read, "%h", tmp_data); // hashed_msg
    $fgets(line_read, fd_r); $sscanf(line_read, "%h", privkey);
    $fgets(line_read, fd_r); $sscanf(line_read, "%h", pubkey_x);
    $fgets(line_read, fd_r); $sscanf(line_read, "%h", pubkey_y);
    $fgets(line_read, fd_r); $sscanf(line_read, "%h", tmp_data); // seed
    $fgets(line_read, fd_r); $sscanf(line_read, "%h", tmp_data); // nonce
    $fgets(line_read, fd_r); $sscanf(line_read, "%h", R);
    $fgets(line_read, fd_r); $sscanf(line_read, "%h", S);
    $fgets(line_read, fd_r); $sscanf(line_read, "%h", tmp_data); // IV
    $fgets(line_read, fd_r); $sscanf(line_read, "%h", privkeyB);
    $fgets(line_read, fd_r); $sscanf(line_read, "%h", dh_sharedkey);
    $fclose(fd_r);

    // Op-conditional expected outputs.
    ECC_sb_ap_output_transaction.result_privkey    = (t.op == key_gen)         ? privkey       : 0;
    ECC_sb_ap_output_transaction.result_pubkey_x   = (t.op == key_gen)         ? pubkey_x      : 0;
    ECC_sb_ap_output_transaction.result_pubkey_y   = (t.op == key_gen)         ? pubkey_y      : 0;
    ECC_sb_ap_output_transaction.result_R          = (t.op == key_sign)        ? R             : 0;
    ECC_sb_ap_output_transaction.result_S          = (t.op == key_sign)        ? S             : 0;
    ECC_sb_ap_output_transaction.result_verify_R   = (t.op == key_verify)      ? R             : 0;
    ECC_sb_ap_output_transaction.result_sharedkey  = (t.op == ecdh_sharedkey)  ? dh_sharedkey  : 0;

    `uvm_info("PREDICT",{"ECC_OUT: ",ECC_sb_ap_output_transaction.convert2string()},UVM_MEDIUM)
    ECC_sb_ap.write(ECC_sb_ap_output_transaction);
    // pragma uvmf custom ECC_in_agent_ae_predictor end
  endfunction


endclass 

// pragma uvmf custom external begin
// pragma uvmf custom external end

