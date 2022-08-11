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
//   SHA512_in_agent_ae receives transactions of type  SHA512_in_transaction #()
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//  SHA512_sb_ap broadcasts transactions of type SHA512_out_transaction #()
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class SHA512_predictor #(
  type CONFIG_T
  )
 extends uvm_component;

  // Factory registration of this class
  `uvm_component_param_utils( SHA512_predictor #(
                              CONFIG_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;

  
  // Instantiate the analysis exports
  uvm_analysis_imp_SHA512_in_agent_ae #(SHA512_in_transaction #(), SHA512_predictor #(
                              .CONFIG_T(CONFIG_T)
                              )
) SHA512_in_agent_ae;

  
  // Instantiate the analysis ports
  uvm_analysis_port #(SHA512_out_transaction #()) SHA512_sb_ap;


  // Transaction variable for predicted values to be sent out SHA512_sb_ap
  typedef SHA512_out_transaction #() SHA512_sb_ap_output_transaction_t;
  SHA512_sb_ap_output_transaction_t SHA512_sb_ap_output_transaction;
  // Code for sending output transaction out through SHA512_sb_ap
  // SHA512_sb_ap.write(SHA512_sb_ap_output_transaction);

  // Define transaction handles for debug visibility 
  SHA512_in_transaction #() SHA512_in_agent_ae_debug;


  // pragma uvmf custom class_item_additional begin
  parameter MODE_SHA_512_224     = 2'h0;
  parameter MODE_SHA_512_256     = 2'h1;
  parameter MODE_SHA_384         = 2'h2;
  parameter MODE_SHA_512         = 2'h3;

  reg [511 : 0] expected;
  reg [7   : 0] test_case_sel;

  int block_shift;
  int line_skip;
  int cnt_tmp;
  int fd_r;
  int expected_shift;

  string        line_read;
  string        tmp_str1;
  string        tmp_str2;
  string        file_name;
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

    SHA512_in_agent_ae = new("SHA512_in_agent_ae", this);
    SHA512_sb_ap =new("SHA512_sb_ap", this );
  // pragma uvmf custom build_phase begin
  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_SHA512_in_agent_ae
  // Transactions received through SHA512_in_agent_ae initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  virtual function void write_SHA512_in_agent_ae(SHA512_in_transaction #() t);
    // pragma uvmf custom SHA512_in_agent_ae_predictor begin
    SHA512_in_agent_ae_debug = t;
    `uvm_info("PRED", "Transaction Received through SHA512_in_agent_ae", UVM_MEDIUM)
    `uvm_info("PRED", {"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    SHA512_sb_ap_output_transaction = SHA512_sb_ap_output_transaction_t::type_id::create("SHA512_sb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  
    // `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    // `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "UVMF_CHANGE_ME: The SHA512_predictor::write_SHA512_in_agent_ae function needs to be completed with DUT prediction model",UVM_NONE)
    // `uvm_info("UNIMPLEMENTED_PREDICTOR_MODEL", "******************************************************************************************************",UVM_NONE)
    
    $display("**SHA512_predictor** t.op= %d",t.op);
    $display("**SHA512_predictor** t.test_case_sel = %d",t.test_case_sel);
    if (t.op== 3'b000) SHA512_sb_ap_output_transaction.result = 0;
    else begin
      cnt_tmp = 0;
      block_shift = 0;
      test_case_sel = t.test_case_sel;

      case(t.op[1:0])
        MODE_SHA_512_224: begin
          expected_shift = 512 - 224;
          case(test_case_sel) inside
            [0:127]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA512_224ShortMsg.rsp";
              line_skip = test_case_sel * 4 + 10;
            end
            [128:255]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA512_224LongMsg.rsp";
              line_skip = (test_case_sel - 128) * 4 + 10;
            end
          endcase
        end
        MODE_SHA_512_256: begin
          expected_shift = 256;
          case(test_case_sel) inside
            [0:127]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA512_256ShortMsg.rsp";
              line_skip = test_case_sel * 4 + 10;
            end
            [128:255]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA512_256LongMsg.rsp";
              line_skip = (test_case_sel - 128) * 4 + 10;
            end
          endcase
        end
        MODE_SHA_384:     begin
          expected_shift = 512 - 384;
          case(test_case_sel) inside
            [0:127]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA384ShortMsg.rsp";
              line_skip = test_case_sel * 4 + 10;
            end
            [128:255]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA384LongMsg.rsp";
              line_skip = (test_case_sel - 128) * 4 + 10;
            end
          endcase
        end
        MODE_SHA_512:     begin
          expected_shift = 0;
          case(test_case_sel) inside
            [0:127]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA512ShortMsg.rsp";
              line_skip = test_case_sel * 4 + 10;
            end
            [128:255]: begin
              file_name = "/home/t-stevenlian/AHA_workspaces/sha512_uvm/Caliptra/src/sha512/tb/vectors/SHA512LongMsg.rsp";
              line_skip = (test_case_sel - 128) * 4 + 10;
            end
          endcase
        end
      endcase

      fd_r = $fopen(file_name,"r");
      if(fd_r) $display("**SHA512_in_driver_bfm** file opened successfully!");

      while (cnt_tmp < line_skip) begin
        cnt_tmp = cnt_tmp + 1;
        $fgets(line_read,fd_r);
      end

      // gets expected result
      $sscanf( line_read, "%s %s %h", tmp_str1, tmp_str2, expected);
      expected = expected << expected_shift;
      SHA512_sb_ap_output_transaction.result = expected;
      `uvm_info("PREDICT",{"SHA512_OUT: ",SHA512_sb_ap_output_transaction.convert2string()},UVM_MEDIUM);
    
    end

    // Code for sending output transaction out through SHA512_sb_ap
    // Please note that each broadcasted transaction should be a different object than previously 
    // broadcasted transactions.  Creation of a different object is done by constructing the transaction 
    // using either new() or create().  Broadcasting a transaction object more than once to either the 
    // same subscriber or multiple subscribers will result in unexpected and incorrect behavior.
    SHA512_sb_ap.write(SHA512_sb_ap_output_transaction);
    // pragma uvmf custom SHA512_in_agent_ae_predictor end
  endfunction


endclass 

// pragma uvmf custom external begin
// pragma uvmf custom external end

