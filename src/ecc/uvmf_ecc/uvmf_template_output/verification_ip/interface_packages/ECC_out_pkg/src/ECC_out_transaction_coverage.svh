//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: This class records ECC_out transaction information using
//       a covergroup named ECC_out_transaction_cg.  An instance of this
//       coverage component is instantiated in the uvmf_parameterized_agent
//       if the has_coverage flag is set.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class ECC_out_transaction_coverage #(
      int AHB_ADDR_WIDTH = 32,
      int AHB_DATA_WIDTH = 32,
      int OUTPUT_TEXT_WIDTH = 384
      )
 extends uvm_subscriber #(.T(ECC_out_transaction #(
                                            .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
                                            .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
                                            .OUTPUT_TEXT_WIDTH(OUTPUT_TEXT_WIDTH)
                                            )
));

  `uvm_component_param_utils( ECC_out_transaction_coverage #(
                              AHB_ADDR_WIDTH,
                              AHB_DATA_WIDTH,
                              OUTPUT_TEXT_WIDTH
                              )
)

  T coverage_trans;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  // ****************************************************************************
  covergroup ECC_out_transaction_cg;
    // pragma uvmf custom covergroup begin
    // UVMF_CHANGE_ME : Add coverage bins, crosses, exclusions, etc. according to coverage needs.
    option.auto_bin_max=1024;
    option.per_instance=1;
    result_privkey: coverpoint coverage_trans.result_privkey;
    result_pubkey_x: coverpoint coverage_trans.result_pubkey_x;
    result_pubkey_y: coverpoint coverage_trans.result_pubkey_y;
    result_R: coverpoint coverage_trans.result_R;
    result_S: coverpoint coverage_trans.result_S;
    result_verify_R: coverpoint coverage_trans.result_verify_R;
    // pragma uvmf custom covergroup end
  endgroup

  // ****************************************************************************
  // FUNCTION : new()
  // This function is the standard SystemVerilog constructor.
  //
  function new(string name="", uvm_component parent=null);
    super.new(name,parent);
    ECC_out_transaction_cg=new;
    `uvm_warning("COVERAGE_MODEL_REVIEW", "A covergroup has been constructed which may need review because of either generation or re-generation with merging.  Please note that transaction variables added as a result of re-generation and merging are not automatically added to the covergroup.  Remove this warning after the covergroup has been reviewed.")
  endfunction

  // ****************************************************************************
  // FUNCTION : build_phase()
  // This function is the standard UVM build_phase.
  //
  function void build_phase(uvm_phase phase);
    ECC_out_transaction_cg.set_inst_name($sformatf("ECC_out_transaction_cg_%s",get_full_name()));
  endfunction

  // ****************************************************************************
  // FUNCTION: write (T t)
  // This function is automatically executed when a transaction arrives on the
  // analysis_export.  It copies values from the variables in the transaction 
  // to local variables used to collect functional coverage.  
  //
  virtual function void write (T t);
    `uvm_info("COV","Received transaction",UVM_HIGH);
    coverage_trans = t;
    ECC_out_transaction_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

