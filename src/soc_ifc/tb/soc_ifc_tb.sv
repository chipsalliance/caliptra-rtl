// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
//======================================================================
//
// soc_ifc_tb.sv
// --------
// soc_ifc testbench for the soc_ifc AHb_lite interface controller.
//
// This Testbench no longer works
// Probably should be deprecated and utilize UVMF environment only
//======================================================================


import "DPI-C" function string getenv(input string env_name);

`define AHB64_HI 63:32
`define AHB64_LO 31:0 

`define REG_HIER_BOOT_FSM_PS dut.boot_fsm_ps
`define REG_HIER_PFX dut.i_soc_ifc_reg.field_storage

module soc_ifc_tb
  import soc_ifc_pkg::*;
  import soc_ifc_tb_pkg::*;
  ();


  enum logic {DEBUG_UNLOCKED = 1'b0, DEBUG_LOCKED = 1'b1} debug_state_e;

  // plusargs and other test related
  string soc_ifc_testname; 
  string socreg_method_name = ""; 
  string security_state_testname; 
  int socreg_wrcount = 1;

  string tphase;


  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DEBUG     = 0;

  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  // The DUT address map
  parameter DCCM_SADR             = 32'hf0040000;

  parameter MBOX_ADDR_BASE        = 32'h30020000;
  parameter MBOX_ADDR_LOCK        = MBOX_ADDR_BASE;
  parameter MBOX_ADDR_CMD         = MBOX_ADDR_BASE + 32'h00000008;
  parameter MBOX_ADDR_DLEN        = MBOX_ADDR_BASE + 32'h0000000C;
  parameter MBOX_ADDR_DATAIN      = MBOX_ADDR_BASE + 32'h00000010;
  parameter MBOX_ADDR_DATAOUT     = MBOX_ADDR_BASE + 32'h00000014;
  parameter MBOX_ADDR_EXECUTE     = MBOX_ADDR_BASE + 32'h00000018;
  parameter MBOX_ADDR_STATUS      = MBOX_ADDR_BASE + 32'h0000001c;

  parameter MBOX_DLEN_VAL         = 32'h0000001C;

  parameter MBOX_UDS_ADDR         = SOCIFC_BASE + `SOC_IFC_REG_FUSE_UDS_SEED_0;
  parameter MBOX_FE_ADDR          = SOCIFC_BASE + `SOC_IFC_REG_FUSE_FIELD_ENTROPY_0;
  parameter MBOX_FUSE_DONE_ADDR   = SOCIFC_BASE + `SOC_IFC_REG_CPTRA_FUSE_WR_DONE;

  parameter AHB_ADDR_WIDTH = `CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC); // 18 
  parameter AHB_DATA_WIDTH = `CALIPTRA_AHB_HDATA_SIZE; // 32 
  parameter APB_ADDR_WIDTH = `CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC); // 18 
  parameter APB_DATA_WIDTH = `CALIPTRA_APB_DATA_WIDTH; // 32 
  parameter APB_USER_WIDTH = `CALIPTRA_APB_USER_WIDTH; // 32 


  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  localparam PAUSER_DEFAULT = 32'hffff_ffff;


  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [63 : 0]  cycle_ctr;
  reg [63 : 0]  error_ctr;
  reg [63 : 0]  tc_ctr;
  reg [63 : 0]  temp_ctr;

  reg           clk_tb;
  reg           cptra_pwrgood_tb;
  reg           cptra_rst_b_tb;

  reg [APB_ADDR_WIDTH-1:0]     paddr_i_tb;
  reg                          psel_i_tb;
  reg                          penable_i_tb;
  reg                          pwrite_i_tb;
  reg [APB_DATA_WIDTH-1:0]     pwdata_i_tb;
  reg [APB_USER_WIDTH-1:0]     pauser_i_tb;

  reg [AHB_ADDR_WIDTH-1:0]  haddr_i_tb;
  reg [AHB_DATA_WIDTH-1:0]  hwdata_i_tb;
  reg           hsel_i_tb;
  reg           hwrite_i_tb; 
  reg           hready_i_tb;
  reg [1:0]     htrans_i_tb;
  reg [2:0]     hsize_i_tb;

  wire                         pready_o_tb;
  wire [APB_DATA_WIDTH-1:0]    prdata_o_tb;
  wire                         pslverr_o_tb;

  wire          hresp_o_tb;
  wire          hreadyout_o_tb;
  wire [AHB_DATA_WIDTH-1:0] hrdata_o_tb;

  wire cptra_noncore_rst_b_tb;
  wire cptra_uc_rst_b_tb;

  reg [127 : 0] result_data;
  logic ready_for_fuses;
  logic [31:0]  generic_input_wires0; 
  logic [31:0]  generic_input_wires1; 

  logic clear_obf_secrets;
  logic scan_mode_f; 

  // obfuscation, uds and field entropy for observation
  logic [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key_reg;
  logic [`CLP_OBF_FE_DWORDS-1 :0][31:0] obf_field_entropy;
  logic [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed;


  //SRAM interface for mbox
  logic mbox_sram_cs;
  logic mbox_sram_we;
  logic [MBOX_ADDR_W-1:0] mbox_sram_addr;
  logic [MBOX_DATA_W-1:0] mbox_sram_wdata;
  logic [MBOX_DATA_W-1:0] mbox_sram_rdata;

  logic [0:11][31:0]          cptra_uds_tb;
  logic [0:31][31:0]          cptra_fe_tb;

  //mailbox sram gasket
  mbox_sram_req_t mbox_sram_req;
  mbox_sram_resp_t mbox_sram_resp;


  //MH. Initialize to default device lifecycle later rather than TIE OFF
  security_state_t security_state, tmp_ss;  // '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED};
  logic            gen_input_wire_toggle;  

  logic [31:0]     generic_input_wires0_q; 
  logic [31:0]     generic_input_wires1_q; 

  //MH. Tick timers
  logic [31:0]   cycle_ctr_since_pwrgood;
  logic [31:0]   cycle_ctr_since_rst;

  bit            reg_sva_off = 1'b1;  // Enable only during register assertion checks

  logic [APB_DATA_WIDTH-1:0]    prdata_o_latched;


  always @(negedge clk_tb) begin
    prdata_o_latched <= prdata_o_tb;
  end

  always_comb begin
    mbox_sram_cs = mbox_sram_req.cs;
    mbox_sram_we = mbox_sram_req.we;
    mbox_sram_addr = mbox_sram_req.addr;
    mbox_sram_wdata = mbox_sram_req.wdata;
    mbox_sram_resp.rdata = mbox_sram_rdata;
  end

  assign hready_i_tb = hreadyout_o_tb;

  //bind coverage file
  soc_ifc_cov_bind i_soc_ifc_cov_bind();

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  soc_ifc_top #(
             .AHB_DATA_WIDTH(AHB_DATA_WIDTH), 
             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH), 
             .APB_USER_WIDTH(APB_USER_WIDTH), 
             .APB_ADDR_WIDTH(APB_ADDR_WIDTH), 
             .APB_DATA_WIDTH(APB_DATA_WIDTH)  
            )
            dut (
             .clk(clk_tb),
             .clk_cg(clk_tb),
             .soc_ifc_clk_cg(clk_tb),
             .rdc_clk_cg(clk_tb),

             .cptra_pwrgood(cptra_pwrgood_tb),
             .cptra_rst_b(cptra_rst_b_tb),
             .rdc_clk_dis(),
             .fw_update_rst_window(),

             .ready_for_fuses(ready_for_fuses),
             .ready_for_fw_push(ready_for_fw_push),
             .ready_for_runtime(),

             .mailbox_data_avail(),
             .mailbox_flow_done(),

             .security_state(security_state),

             .generic_input_wires({generic_input_wires1, generic_input_wires0}),
             .BootFSM_BrkPoint(1'b0), // TODO
             .generic_output_wires(),

             .paddr_i(paddr_i_tb),
             .psel_i(psel_i_tb),
             .penable_i(penable_i_tb),
             .pwrite_i(pwrite_i_tb),
             .pwdata_i(pwdata_i_tb),
             .pauser_i(pauser_i_tb),
             .pready_o(pready_o_tb),
             .prdata_o(prdata_o_tb),
             .pslverr_o(pslverr_o_tb),

             .haddr_i(haddr_i_tb),
             .hwdata_i(hwdata_i_tb),
             .hsel_i(hsel_i_tb),
             .hwrite_i(hwrite_i_tb),
             .hready_i(hready_i_tb),
             .htrans_i(htrans_i_tb),
             .hsize_i(hsize_i_tb),

             .hresp_o(hresp_o_tb),
             .hreadyout_o(hreadyout_o_tb),
             .hrdata_o(hrdata_o_tb),

             .cptra_error_fatal(),
             .cptra_error_non_fatal(),
             .trng_req(),

             .soc_ifc_error_intr(),
             .soc_ifc_notif_intr(),
             .sha_error_intr(),
             .sha_notif_intr(),
             .timer_intr(),

             .mbox_sram_req(mbox_sram_req),
             .mbox_sram_resp(mbox_sram_resp),

             .rv_ecc_sts(rv_ecc_sts_t'{default:1'b0}),

             .clear_obf_secrets(clear_obf_secrets), 
             .scan_mode_f(scan_mode_f), 
             .cptra_obf_key('0),
             .cptra_obf_key_reg(cptra_obf_key_reg),
             .obf_field_entropy(obf_field_entropy),
             .obf_uds_seed(obf_uds_seed),

             .nmi_vector(),
             .nmi_intr(),

             .iccm_lock(),
             .iccm_axs_blocked(1'b0), // MH. Tie off here unless need control

             .cptra_noncore_rst_b(cptra_noncore_rst_b_tb),
             .cptra_uc_rst_b(cptra_uc_rst_b_tb),
             .clk_gating_en(),

             .cptra_uncore_dmi_reg_en     ( 1'h0),
             .cptra_uncore_dmi_reg_wr_en  ( 1'h0),
             .cptra_uncore_dmi_reg_rdata  (     ),
             .cptra_uncore_dmi_reg_addr   ( 7'h0),
             .cptra_uncore_dmi_reg_wdata  (32'h0)

            );



  //SRAM for mbox
  caliptra_sram 
  #(
    .DATA_WIDTH(32),
    .DEPTH('h8000)
  )
  mbox_ram1
  (
    .clk_i(clk_tb),
    
    .cs_i(mbox_sram_cs),
    .we_i(mbox_sram_we),
    .addr_i(mbox_sram_addr),
    .wdata_i(mbox_sram_wdata),
    
    .rdata_o(mbox_sram_rdata)
  );


  // Other special and aggregate data type instantiations 
  struct {
    string reg_name;
    WordTransaction wr_trans;
    access_t wr_modifier;
  } pulse_trig_struct;

  event pulse_trig_event;

  WordTransaction pulse_trig_trans = new(); 

  RegScoreboard sb = new();  // scoreboard for checking register operations 

  SocRegisters socregs = new(); // allows for initialization of soc-registers 


  // Tie-offs
  assign scan_mode_f = 1'b0; 
  assign clear_obf_secrets = 1'b0;


  //----------------------------------------------------------------
  // clk_gen
  //
  // Always running clock generator process.
  //----------------------------------------------------------------
  always
    begin : clk_gen
      #CLK_HALF_PERIOD;
      clk_tb = !clk_tb;
    end // clk_gen


  //----------------------------------------------------------------
  // sys_monitor()
  //
  // An always running process that creates a cycle counter and
  // conditionally displays information about the DUT.
  //----------------------------------------------------------------
  always
    begin : sys_monitor
      #(CLK_PERIOD);
      cycle_ctr = cycle_ctr + 1;
    end


  //----------------------------------------------------------------
  // tick_timer 
  // 
  // Counts number of clock ticks since power good and reset
  //----------------------------------------------------------------
  always @(posedge clk_tb or negedge cptra_pwrgood_tb) begin : tick_timer_pwrgood
    if (!cptra_pwrgood_tb)
      cycle_ctr_since_pwrgood <= '0;
    else
      cycle_ctr_since_pwrgood <= cycle_ctr_since_pwrgood + 1'b1; 
  end 

  always @(posedge clk_tb or negedge cptra_rst_b_tb) begin : tick_timer_outofrst
    if (!cptra_rst_b_tb)
      cycle_ctr_since_rst <= '0;
    else
      cycle_ctr_since_rst <= cycle_ctr_since_pwrgood + 1'b1; 
  end


  //----------------------------------------------------------------
  // generic_input_detetor 
  //
  // pulses high when generic input wires change  
  //----------------------------------------------------------------
  always @(posedge clk_tb or negedge cptra_rst_b_tb) begin  : generic_input_detector
    if (!cptra_rst_b_tb) begin
      generic_input_wires0_q <= '0; 
      generic_input_wires1_q <= '0;
    end else begin 
      generic_input_wires0_q <= cptra_noncore_rst_b_tb ? generic_input_wires0 : generic_input_wires0_q; 
      generic_input_wires1_q <= cptra_noncore_rst_b_tb ? generic_input_wires1 : generic_input_wires1_q; 
    end
  end

  assign gen_input_wire_toggle = (generic_input_wires0 != generic_input_wires0_q) | 
                                 (generic_input_wires1 != generic_input_wires1_q);


  //----------------------------------------------------------------
  // pulse_trig_handler 
  //
  // Handles events that relate to pulse triggered action, usually
  // clear after 1 or more cycles (currently for all SoC regs)
  //----------------------------------------------------------------

  always 
    begin : pulse_trig_handler 

      wait (pulse_trig_event.triggered); 
  
      pulse_trig_struct.wr_trans.update_data('0);

      @(posedge clk_tb); 
      // $display ("-- Updating record for address 0x%x", pulse_trig_trans.addr);
      sb.del_entries(pulse_trig_struct.reg_name); 
      sb.record_entry(pulse_trig_trans, SET_DIRECT);
    end 


  //----------------------------------------------------------------
  // Updates registers that have wired connections for status
  //
  // CPTRA SECUIRTY_STATE, FLOW_STATUS, GENERIC_INPUT_WIRES
  //----------------------------------------------------------------

  always_comb update_CPTRA_SECURITY_STATE(scan_mode_f, security_state.debug_locked, security_state.device_lifecycle);
  always_comb update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS);
  always_comb update_CPTRA_GENERIC_INPUT_WIRES(generic_input_wires1_q, 1'b1); 
  always_comb update_CPTRA_GENERIC_INPUT_WIRES(generic_input_wires0_q, 1'b0);
  always_comb update_INTR_BRF_NOTIF_INTERNAL_INTR_R(gen_input_wire_toggle, security_state.debug_locked); 



  //----------------------------------------------------------------
  // reset_dut()
  //
  // Toggle reset to put the DUT into a well known state.
  //----------------------------------------------------------------
  task reset_dut;
    begin
      $display("*** Toggle reset.");

      reset_generic_input_wires(-1, -1);

      cptra_pwrgood_tb = '0;
      cptra_rst_b_tb = 0;

      repeat (5) @(posedge clk_tb);

      socregs.unlock_fuses();

      cptra_pwrgood_tb = 1;

      repeat (5) @(posedge clk_tb);
      
      cptra_rst_b_tb = 1;
      repeat (5) @(posedge clk_tb);
      $display("");
    end
  endtask // reset_dut


  //----------------------------------------------------------------
  // warm_reset_dut()
  //
  // Warm reset DUT into a well known state.
  //----------------------------------------------------------------
  task warm_reset_dut;
    begin
      $display("*** Perform warm reset. ***");

      reset_generic_input_wires(-1, -1);
      reset_flow_status();

      cptra_rst_b_tb = 0;

      repeat (5) @(posedge clk_tb);

      cptra_rst_b_tb = 1;
      repeat (5) @(posedge clk_tb);
      $display("");
    end
  endtask // reset_dut

  //----------------------------------------------------------------
  // load_fuses()
  //
  // Load Fuses (required to get other blocks out of reset)
  //----------------------------------------------------------------
  task load_fuses;
    begin
      for (int i = 0; i < 12; i++)begin
        write_single_word_apb(MBOX_UDS_ADDR + i*4, cptra_uds_tb[i]);
      end
      
      $display ("SoC: Writing obfuscated Field Entropy to fuse bank\n");
      for (int i = 0; i < 32; i++)begin
          write_single_word_apb(MBOX_FE_ADDR + i*4, cptra_fe_tb[i]);
      end
      
      $display ("SoC: Writing fuse done register\n");
      //set fuse done
      write_single_word_apb(MBOX_FUSE_DONE_ADDR, 32'h00000001); 
      
      /*
      wait (ready_for_fw_push == 1'b1);
        
      repeat (5) @(posedge clk_tb);
      // poll for lock register
      wait_unlock_apb();
      repeat (5) @(posedge clk_tb);
        */
    end
  endtask

  //----------------------------------------------------------------
  // display_test_results()
  //
  // Display the accumulated test results.
  //----------------------------------------------------------------
  task display_test_results;
    begin
      if (error_ctr == 0)
        begin
          $display("*** All %02d test cases completed successfully", tc_ctr);
          $display("* TESTCASE PASSED");
        end
      else
        begin
          $display("*** %02d tests completed - %02d test cases did not complete successfully.",
                   tc_ctr, error_ctr);
          $display("* TESTCASE FAILED");
        end
    end
  endtask // display_test_results

  //----------------------------------------------------------------
  // init_sim()
  //
  // Initialize all counters and testbed functionality as well
  // as setting the DUT inputs to defined values.
  //----------------------------------------------------------------
  task init_sim;
    begin
      cycle_ctr     = 0;
      error_ctr     = 0;
      tc_ctr        = 0;
      temp_ctr      = 0;
      result_data   = 0;

      clk_tb        = 0;
      cptra_pwrgood_tb = 0;
      cptra_rst_b_tb    = 0;

      haddr_i_tb      = 'Z;
      hwdata_i_tb     = 'Z;
      hsel_i_tb       = 0;
      hwrite_i_tb     = 0;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      hsize_i_tb      = 3'b011;

      paddr_i_tb      = 'Z;
      psel_i_tb       = 0;
      penable_i_tb    = 0;
      pwrite_i_tb     = 0;
      pwdata_i_tb     = 0;
      pauser_i_tb     = 0;

      //Key for UDS 
      cptra_uds_tb = 384'he4046d05385ab789c6a72866e08350f93f583e2a005ca0faecc32b5cfc323d461c76c107307654db5566a5bd693e227c;

      //Key for FE
      cptra_fe_tb = {256'hb32e2b171b63827034ebb0d1909f7ef1d51c5f82c1bb9bc26bc4ac4dccdee835,
                     256'h7dca6154c2510ae1c87b1b422b02b621bb06cac280023894fcff3406af08ee9b,
                     256'he1dd72419beccddff77c722d992cdcc87e9c7486f56ab406ea608d8c6aeb060c,
                     256'h64cf2785ad1a159147567e39e303370da445247526d95942bf4d7e88057178b0};

    end
  endtask // init_sim

  //----------------------------------------------------------------
  // write_single_word_ahb()
  //
  // Write the given word to the DUT using the AHB-lite interface.
  //----------------------------------------------------------------
  task write_single_word_ahb(input [31 : 0]  address,
                             input [31 : 0] word);

    begin
      hsel_i_tb       <= 1;
      haddr_i_tb      <= address;
      hwrite_i_tb     <= 1;
      htrans_i_tb     <= AHB_HTRANS_NONSEQ;
      hsize_i_tb      <= 3'b010;

      @(posedge clk_tb);
      haddr_i_tb      <= 'Z;
      hwdata_i_tb     <= address[2] ? {word, 32'h0}: {32'h0, word}; 
      hwrite_i_tb     <= 0;
      htrans_i_tb     <= AHB_HTRANS_IDLE;
      wait(hreadyout_o_tb == 1'b1);

      @(posedge clk_tb);
      hsel_i_tb       <= 0;

    end
  endtask // write_single_word_ahb

  //----------------------------------------------------------------
  // write_single_word_apb()
  //
  // Write the given word to the DUT using the AHB-lite interface.
  //----------------------------------------------------------------
  task write_single_word_apb(input [31 : 0] address,
                             input [31 : 0] word);
    begin
      paddr_i_tb      <= address;
      psel_i_tb       <= 1;
      penable_i_tb    <= 0;
      pwrite_i_tb     <= 1;
      pwdata_i_tb     <= word;
      pauser_i_tb     <= '1;
      wait(pready_o_tb == 1'b1);
      
      @(posedge clk_tb);
      penable_i_tb    <= 1;
      wait(pready_o_tb == 1'b1);

      @(posedge clk_tb);
      psel_i_tb       <= 0;
      penable_i_tb    <= 0;
    end
  endtask // write_single_word_apb


  //----------------------------------------------------------------
  // write_single_word_apb_wpauser()
  //
  // Write the given word to the DUT using the APB interface setting pauser.
  //----------------------------------------------------------------
  task write_single_word_apb_wpauser(input [31 : 0] address,
                                     input [31 : 0] word,
                                     input [31 : 0] pauser);
    begin
      paddr_i_tb      <= address;
      psel_i_tb       <= 1;
      penable_i_tb    <= 0;
      pwrite_i_tb     <= 1;
      pwdata_i_tb     <= word;
      pauser_i_tb     <= pauser; 
      wait(pready_o_tb == 1'b1);
      
      @(posedge clk_tb);
      penable_i_tb    <= 1;
      wait(pready_o_tb == 1'b1);

      @(posedge clk_tb);
      psel_i_tb       <= 0;
      penable_i_tb    <= 0;
    end
  endtask // write_single_word_apb_wpauser


  //----------------------------------------------------------------
  // write_block_ahb()
  //
  // Write the given block to the dut.
  //----------------------------------------------------------------
  task write_block_ahb(input [127 : 0] block);
    begin
      write_single_word_ahb(MBOX_ADDR_DATAIN, block[127  :  96]);
      write_single_word_ahb(MBOX_ADDR_DATAIN, block[95   :  64]);
      write_single_word_ahb(MBOX_ADDR_DATAIN, block[63   :  32]);
      write_single_word_ahb(MBOX_ADDR_DATAIN, block[31   :   0]);
    end
  endtask // write_block_ahb

  //----------------------------------------------------------------
  // write_block_apb()
  //
  // Write the given block to the dut.
  //----------------------------------------------------------------
  task write_block_apb(input [127 : 0] block);
    begin
      write_single_word_apb(MBOX_ADDR_DATAIN, block[127  :  96]);
      write_single_word_apb(MBOX_ADDR_DATAIN, block[95   :  64]);
      write_single_word_apb(MBOX_ADDR_DATAIN, block[63   :  32]);
      write_single_word_apb(MBOX_ADDR_DATAIN, block[31   :   0]);
    end
  endtask // write_block_apb


  //----------------------------------------------------------------
  // read_word()
  //
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_single_word_ahb(input [31 : 0]  address);
    begin
      hsel_i_tb       <= 1;
      haddr_i_tb      <= address;
      hwrite_i_tb     <= 0;
      htrans_i_tb     <= AHB_HTRANS_NONSEQ;
      hsize_i_tb      <= 3'b010;

      @(posedge clk_tb);
      hwdata_i_tb     <= 0;
      haddr_i_tb      <= 'Z;
      htrans_i_tb     <= AHB_HTRANS_IDLE;
      wait(hreadyout_o_tb == 1'b1);

      @(posedge clk_tb);
      hsel_i_tb       <= 0;

    end
  endtask // read_single_word_ahb

  task read_single_word_apb(input [31 : 0] address);
    begin
      paddr_i_tb      <= address;
      psel_i_tb       <= 1;
      penable_i_tb    <= 0;
      pwrite_i_tb     <= 0;
      pwdata_i_tb     <= 0;
      pauser_i_tb     <= '1;
      wait(pready_o_tb == 1'b1);

      @(posedge clk_tb);
      penable_i_tb    <= 1;
      wait(pready_o_tb == 1'b1);

      @(posedge clk_tb);
      psel_i_tb       <= 0;
      penable_i_tb    <= 0;
    end
  endtask // read_single_word_apb

  //----------------------------------------------------------------
  // read_single_word_apb_wpauser()
  //
  // Read the given word to the DUT using the APB interface setting pauser.
  //----------------------------------------------------------------
  task read_single_word_apb_wpauser(input [31 : 0] address,
                                     input [31 : 0] word,
                                     input [31 : 0] pauser);
    begin
      paddr_i_tb      <= address;
      psel_i_tb       <= 1;
      penable_i_tb    <= 0;
      pwrite_i_tb     <= 0;
      pwdata_i_tb     <= 0;
      pauser_i_tb     <= pauser; 
      wait(pready_o_tb == 1'b1);

      @(posedge clk_tb);
      penable_i_tb    <= 1;
      wait(pready_o_tb == 1'b1);

      @(posedge clk_tb);
      psel_i_tb       <= 0;
      penable_i_tb    <= 0;
    end
  endtask // read_single_word_apb_wpauser

  //----------------------------------------------------------------
  // read_result_ahb()
  //
  // Read the result block in the dut.
  //----------------------------------------------------------------
  task read_result_ahb(output [127:0]  r_data);
    begin
      
      read_single_word_ahb(MBOX_ADDR_DATAOUT);
      r_data[127 : 96] = MBOX_ADDR_DATAOUT[2] ? hrdata_o_tb[`AHB64_HI] : hrdata_o_tb[`AHB64_LO]; 
      read_single_word_ahb(MBOX_ADDR_DATAOUT);
      r_data[95  : 64] = MBOX_ADDR_DATAOUT[2] ? hrdata_o_tb[`AHB64_HI] : hrdata_o_tb[`AHB64_LO]; 
      read_single_word_ahb(MBOX_ADDR_DATAOUT);
      r_data[63  : 32] = MBOX_ADDR_DATAOUT[2] ? hrdata_o_tb[`AHB64_HI] : hrdata_o_tb[`AHB64_LO]; 
      read_single_word_ahb(MBOX_ADDR_DATAOUT);
      r_data[31  :  0] = MBOX_ADDR_DATAOUT[2] ? hrdata_o_tb[`AHB64_HI] : hrdata_o_tb[`AHB64_LO]; 
    end
  endtask // read_result_ahb

  //----------------------------------------------------------------
  // read_result_apb()
  //
  // Read the result block in the dut.
  //----------------------------------------------------------------
  task read_result_apb(output [127:0]  r_data);
    begin

      read_single_word_apb(MBOX_ADDR_DATAOUT);
      r_data[127:96] = prdata_o_tb;
      read_single_word_apb(MBOX_ADDR_DATAOUT);
      r_data[ 95:64] = prdata_o_tb;
      read_single_word_apb(MBOX_ADDR_DATAOUT);
      r_data[ 63:32] = prdata_o_tb;
      read_single_word_apb(MBOX_ADDR_DATAOUT);
      r_data[ 31: 0] = prdata_o_tb;
  
    end
  endtask // read_result_apb

  //----------------------------------------------------------------
  // wait_unlock_ahb()
  //
  // wait for the mailbox to unlock before send in anything
  //----------------------------------------------------------------
  task wait_unlock_ahb;
      
    automatic logic [31:0] valid_hrdata;

    begin
      read_single_word_ahb(MBOX_ADDR_LOCK);
      valid_hrdata =  MBOX_ADDR_LOCK[2] ?  hrdata_o_tb[`AHB64_HI] :hrdata_o_tb[`AHB64_LO]; 
      while (valid_hrdata != 0) 
        begin
          read_single_word_ahb(MBOX_ADDR_LOCK);
          valid_hrdata =  MBOX_ADDR_LOCK[2] ?  hrdata_o_tb[`AHB64_HI] :hrdata_o_tb[`AHB64_LO]; 
        end
    end
  endtask // wait_unlock_ahb

  //----------------------------------------------------------------
  // wait_unlock_apb()
  //
  // wait for the mailbox to unlock before send in anything
  //----------------------------------------------------------------
  task wait_unlock_apb;
    begin
      read_single_word_apb(MBOX_ADDR_LOCK);
      while (prdata_o_tb != 0)
        begin
          read_single_word_apb(MBOX_ADDR_LOCK);
        end
    end
  endtask // wait_unlock_apb



  //----------------------------------------------------------------
  // reset_generic_input_wires()
  //
  // sets the generic_input_wires to a predetermined or random value
  //----------------------------------------------------------------
  task reset_generic_input_wires(input int v0, int v1);

    begin
      generic_input_wires0 = (v0 < 0) ? $urandom() : v0;
      generic_input_wires1 = (v1 < 0) ? $urandom() : v1;
      repeat (2) @(posedge clk_tb);
      set_initval("CPTRA_GENERIC_INPUT_WIRES0", generic_input_wires0_q); 
      set_initval("CPTRA_GENERIC_INPUT_WIRES1", generic_input_wires1_q); 
      update_CPTRA_GENERIC_INPUT_WIRES(generic_input_wires0_q, 1'b0); 
      update_CPTRA_GENERIC_INPUT_WIRES(generic_input_wires1_q, 1'b1); 

      @(posedge clk_tb);
    end

  endtask


  //----------------------------------------------------------------
  // reset_flow_status()
  //
  // resets flow status w/appropriate value of ready_for_fuse (0) 
  //----------------------------------------------------------------
  task reset_flow_status();

    begin
      set_initval("CPTRA_FLOW_STATUS", '0); 
      update_CPTRA_FLOW_STATUS('0, `REG_HIER_BOOT_FSM_PS);
    end

  endtask


  //----------------------------------------------------------------
  // mbox_ahb_test()
  //
  // mailbox ahb test for single block
  //----------------------------------------------------------------
  task mbox_ahb_test (input [7 : 0]   tc_number,
                      input [127 : 0] block
                      );
    reg [31  : 0] start_time;
    reg [31 : 0] end_time;
    
    begin
      $display("*** TC %0d mailbox test started.", tc_number);
      tc_ctr = tc_ctr + 1;
      start_time = cycle_ctr;

      // poll for lock register
      wait_unlock_ahb();

      //write to MBOX_ADDR_CMD
      write_single_word_ahb(MBOX_ADDR_CMD, 32'hDEADBEEF);

      // write to MBOX_ADDR_DLEN
      write_single_word_ahb(MBOX_ADDR_DLEN, 32'h00000010);

      // write a block in
      write_block_ahb(block);
      @(posedge clk_tb);
      
      // execute
      write_single_word_ahb(MBOX_ADDR_EXECUTE, 32'h00000001);
      repeat (20) @(posedge clk_tb);

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);
      read_result_apb(result_data);

      //set status
      write_single_word_apb(MBOX_ADDR_STATUS, 32'h00000002);

      // reset excecute
      write_single_word_ahb(MBOX_ADDR_EXECUTE, 32'h00000000);

      if (result_data == block)
        begin
          $display("*** TC %0d successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d NOT successful.", tc_number);
          $display("Expected: 0x%032x", block);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // mbox_ahb_test

  //----------------------------------------------------------------
  // mbox_apb_test()
  //
  // mailbox apb test for single block
  //----------------------------------------------------------------
  task mbox_apb_test (input [7 : 0]   tc_number,
                      input [127 : 0] block
                      );
    reg [31  : 0] start_time;
    reg [31 : 0] end_time;
    
    begin
      $display("*** TC %0d mailbox test started.", tc_number);
      tc_ctr = tc_ctr + 1;
      start_time = cycle_ctr;

      // poll for lock register
      wait_unlock_apb();

      //write to MBOX_ADDR_CMD
      write_single_word_apb(MBOX_ADDR_CMD, 32'hDEADBEEF);

      // write to MBOX_ADDR_DLEN
      write_single_word_apb(MBOX_ADDR_DLEN, 32'h00000010);

      // write a block in
      write_block_apb(block);
      @(posedge clk_tb);
      
      // execute
      write_single_word_apb(MBOX_ADDR_EXECUTE, 32'h00000001);
      repeat (20) @(posedge clk_tb);

      // wait_ready();

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);
      read_result_ahb(result_data);

      //set status
      write_single_word_ahb(MBOX_ADDR_STATUS, 32'h00000002);

      // reset excecute
      write_single_word_apb(MBOX_ADDR_EXECUTE, 32'h00000000);

      if (result_data == block)
        begin
          $display("*** TC %0d successful.", tc_number);
          $display("");
        end
      else
        begin
          $display("*** ERROR: TC %0d NOT successful.", tc_number);
          $display("Expected: 0x%032x", block);
          $display("Got:      0x%032x", result_data);
          $display("");

          error_ctr = error_ctr + 1;
        end
    end
  endtask // mbox_apb_test

  //----------------------------------------------------------------
  // mbox_test()
  //----------------------------------------------------------------
  task mbox_test;
    reg [127 : 0] ahb_message_1;
    reg [127 : 0] apb_message_1;

    begin
      ahb_message_1 = 128'h11111111222222223333333344444444;

      apb_message_1 = 128'h66666666777777778888888899999999;


      $display("mailbox ahb test");
      $display("---------------------");
      mbox_ahb_test(8'h01, ahb_message_1);

      $display("mailbox apb test");
      $display("---------------------");
      mbox_apb_test(8'h01, apb_message_1);


    end
  endtask // mbox_test


  //----------------------------------------------------------------
  // sim_dut_init();
  // 
  // common sim and dut initialization routines for register tests 
  //----------------------------------------------------------------
  task sim_dut_init;

    // int sscode = -1;
    string ssname = "UNSET"; 

    begin
      // sscode = int'(security_state);
      // if (!((sscode >= 0)  || (sscode <= 7))) 
      //   $error("Have to explictily set security_state for soc_ifc_top for test to run!");

      ssname = get_ss_name(int'(security_state)); 
      if ((ssname == "") || (ssname == "UNSET"))
        $error("Have to explictily set security_state for soc_ifc_top for test to run!");

      else begin
        init_sim();
        reset_dut();

        wait (ready_for_fuses == 1'b1);
        update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS);
        // set_initval("CPTRA_FLOW_STATUS", 32'h4000_0000); 
        // update_exp_regval("CPTRA_FLOW_STATUS", 32'h4000_0000, SET_DIRECT); 

        repeat (5) @(posedge clk_tb);
      end
    end

  endtask // sim_dut_init

  
  //----------------------------------------------------------------
  // simulate_caliptra_boot();
  //
  // Set boot fuse write and boot status over APB 
  //----------------------------------------------------------------
  task simulate_caliptra_boot;
      // Enable release of Caliptra core from reset & simulate FW boot
      write_single_word_apb(socregs.get_addr("CPTRA_FUSE_WR_DONE"), 32'h1); 
      update_exp_regval("CPTRA_FUSE_WR_DONE", 32'h1, SET_APB);
      socregs.lock_fuses();

      repeat (3) @(posedge clk_tb); 
      write_single_word_apb(socregs.get_addr("CPTRA_BOOTFSM_GO"), 32'h1); 
      update_exp_regval("CPTRA_BOOTFSM_GO", 32'h1, SET_APB);

      repeat (20) @(posedge clk_tb); // simulate FW boot

  endtask // simulate_caliptra_boot



  //----------------------------------------------------------------
  // write_regs()
  //
  // Utility for tracking/writing to list of registers over APB/AHB
  //----------------------------------------------------------------
  task write_regs(input access_t modifier, strq_t reglist, int tid, int wait_cycles);
    string rname;
    word_addr_t addr;
    WordTransaction wrtrans;

    int tid_autoinc; 

    begin
      wrtrans = new();

      if (tid < 0) begin
        tid_autoinc = 1;
        tid = 0;
      end 

      $display("");

      foreach (reglist[i]) begin 
        rname = reglist[i];
        addr = socregs.get_addr(rname); 
        if (tid_autoinc) 
          tid += 1;
        wrtrans.update(addr, 0, tid); 
        wrtrans.randomize();
        if (modifier == SET_AHB) begin
          write_single_word_ahb(addr, wrtrans.data); 
          $display("Write over AHB: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, wrtrans.data);
        end else if (modifier == SET_APB) begin
          write_single_word_apb(addr, wrtrans.data); 
          $display("Write over APB: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, wrtrans.data);
        end else 
          $error("TB ERROR. Unsupported access modifier %s", modifier.name()); 

        sb.record_entry(wrtrans, modifier);
        if (wait_cycles == 0)
          @(posedge clk_tb);
        else
          repeat (wait_cycles) @(posedge clk_tb);
      end
    end
  endtask // write_regs


  //-----------------------------------------------------------------------------
  // read_reg_chk_inrange()
  //
  // Utility for reading single register over APB/AHB and check if within range.
  // NOTE. Wait times must be added explcitly outside routine
  //-----------------------------------------------------------------------------
  task read_reg_chk_inrange(input access_t modifier, string rname, int tid, int minval, int maxval); 

    word_addr_t addr;
    WordTransaction rdtrans;
    automatic logic [31:0] valid_hrdata; 

    begin
      rdtrans = new();
      addr = socregs.get_addr(rname);  

      if (modifier == GET_AHB) begin 
          read_single_word_ahb(addr);
          valid_hrdata =  addr[2] ?  hrdata_o_tb[`AHB64_HI] :hrdata_o_tb[`AHB64_LO]; 
          $display(" Read over AHB: addr =  %-40s (0x%08x), data = 0x%08x", rname, addr, valid_hrdata); 
          rdtrans.update(addr, valid_hrdata, tid); 
      end else if (modifier == GET_APB) begin
        read_single_word_apb(addr);
        $display(" Read over APB: addr =  %-40s (0x%08x), data = 0x%08x", rname, addr, prdata_o_tb); 
        rdtrans.update_byname(rname, prdata_o_tb,  tid); 
        end else 
          $error("TB ERROR. Unsupported access modifier %s", modifier.name()); 

      sb.record_entry(rdtrans, SET_DIRECT);
      sb.check_entry_inrange(rdtrans, minval, maxval); 
    end

  endtask // read_reg_chk_inrange


  //----------------------------------------------------------------
  // write_reg_trans()
  //
  // Utility for tracking/writing transaction to a register over APB/AHB
  // NOTE. Wait times must be added explcitly outside routine
  //----------------------------------------------------------------
  task write_reg_trans(access_t modifier, WordTransaction wrtrans, logic [31:0] pauser=PAUSER_DEFAULT);
    string rname;
    word_addr_t addr;

    begin
        addr = wrtrans.addr;
        rname = socregs.get_name(addr); 

        if (modifier == SET_AHB) begin
          write_single_word_ahb(addr, wrtrans.data); 
          $display("Write over AHB: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, wrtrans.data);
        end else if (modifier == SET_APB) begin
          if (pauser != PAUSER_DEFAULT) begin
            write_single_word_apb_wpauser(addr, wrtrans.data, pauser); 
            $display("Write over APB with non-default pauser: addr = %-40s (0x%08x), data = 0x%08x", 
              rname, addr, wrtrans.data);
          end else begin
            write_single_word_apb(addr, wrtrans.data); 
            $display("Write over APB: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, wrtrans.data);
          end
        end else 
          $error("TB ERROR. Unsupported access modifier %s", modifier.name()); 

        sb.record_entry(wrtrans, modifier);
      end
    endtask // write_reg_trans


 //----------------------------------------------------------------
  // read_reg_trans()
  //
  // Utility for reading transaction to a register over APB/AHB
  // NOTES. 1. No scoreboard checking 
  //        2. Wait times must be added explcitly outside routine
  //----------------------------------------------------------------
  task read_reg_trans(input access_t modifier, 
                      inout WordTransaction rdtrans, 
                      input logic [31:0] pauser=PAUSER_DEFAULT); 
    string rname;
    word_addr_t addr;
    automatic logic [31:0] valid_hrdata; 

    begin
        addr = rdtrans.addr;
        rname = socregs.get_name(addr); 

        if (modifier == GET_AHB) begin
          read_single_word_ahb(addr); 
          valid_hrdata =  addr[2] ?  hrdata_o_tb[`AHB64_HI] :hrdata_o_tb[`AHB64_LO]; 
          rdtrans.data = valid_hrdata; 
          $display(" Read over AHB: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, rdtrans.data);
        end else if (modifier == GET_APB) begin
          if (pauser != PAUSER_DEFAULT) begin
            read_single_word_apb_wpauser(addr, rdtrans.data, pauser); 
            rdtrans.data = prdata_o_tb;
            $display(" Read over APB with explicit pauser: addr = %-40s (0x%08x), data = 0x%08x", 
              rname, addr, rdtrans.data);
          end else begin
            read_single_word_apb(addr); 
            rdtrans.data = prdata_o_tb;
            $display(" Read over APB: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, rdtrans.data);
          end
        end else 
          $error("TB ERROR. Unsupported access modifier %s", modifier.name()); 

        // sb.check_entry(rdtrans)
    end
  endtask // read_reg_trans


  //----------------------------------------------------------------
  // read_regs()
  //
  // Utility for tracking/reading from list of registers over APB/AHB
  //----------------------------------------------------------------
  task read_regs(input access_t modifier, strq_t reglist, int tid, int wait_cycles);
    string rname;
    word_addr_t addr;
    WordTransaction rdtrans;

    int tid_autoinc; 
    automatic logic [31:0] valid_hrdata; 

    begin
      rdtrans = new();

      if (tid < 0) begin
        tid_autoinc = 1;
        tid = 0;
      end 

      $display("");

      foreach (reglist[i]) begin 
        rname = reglist[i];
        addr = socregs.get_addr(rname); 
        if (tid_autoinc) 
          tid += 1;

        if (modifier == GET_AHB) begin
          read_single_word_ahb(addr);
          valid_hrdata =  addr[2] ?  hrdata_o_tb[`AHB64_HI] :hrdata_o_tb[`AHB64_LO]; 
          $display(" Read over AHB: addr =  %-40s (0x%08x), data = 0x%08x on cycle %08d", rname, addr, valid_hrdata, cycle_ctr); 
          rdtrans.update(addr, valid_hrdata, tid); 
        end else if (modifier == GET_APB) begin
          read_single_word_apb(addr);
          // $display(" Read over APB: addr =  %-40s (0x%08x), data = 0x%08x at time %12t (cycle %08d)", rname, addr, prdata_o_latched, $realtime, cycle_ctr); // used to be   prdata_o_tb
          $display(" Read over APB: addr =  %-40s (0x%08x), data = 0x%08x on cycle %08d", rname, addr, prdata_o_tb, cycle_ctr); // used to be   prdata_o_tb
          // rdtrans.update(addr, prdata_o_latched, tid);  // used to be prdata_o_tb
          rdtrans.update(addr, prdata_o_tb, tid);  
        end else 
          $error("TB ERROR. Unsupported access modifier %s", modifier.name()); 

        sb.check_entry(rdtrans);
        if (wait_cycles == 0)
          @(posedge clk_tb);
        else
          repeat (wait_cycles) @(posedge clk_tb);

      end
    end
  endtask // read_regs


  //----------------------------------------------------------------
  // write_read_regs() 
  //
  // Utility for tracking/reading from list of registers over APB/AHB
  //----------------------------------------------------------------
  task write_read_regs(input access_t wr_modifier, access_t rd_modifier, strq_t reglist, int tid, int wait_cycles);

    string rname;
    word_addr_t addr;
    WordTransaction rdtrans;
    WordTransaction wrtrans;

    int tid_autoinc; 
    automatic logic [31:0] valid_hrdata; 

    begin
      wrtrans = new();
      rdtrans = new();

      if (tid < 0) begin
        tid_autoinc = 1;
        tid = 0;
      end 

      $display("");

      foreach (reglist[i]) begin 
        $display("");
        rname = reglist[i];
        addr = socregs.get_addr(rname); 
        if (tid_autoinc) 
          tid += 1;

        // write phase
        wrtrans.update(addr, 0, tid); 
        wrtrans.randomize();

        if (wr_modifier == SET_AHB) begin
          write_single_word_ahb(addr, wrtrans.data); 
          $display("Write over AHB: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, wrtrans.data);
        end else if (wr_modifier == SET_APB) begin
          write_single_word_apb(addr, wrtrans.data); 
          $display("Write over APB: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, wrtrans.data);
        end else 
          $error("TB ERROR. Unsupported access modifier %s", wr_modifier.name()); 

        // TODO. Make sure this is superfluous (implemented in package) before deleting
        // Currently only pulsed register assumed to have cross-register modifications
        if (is_pulsed_reg(rname)) begin
          sb.record_entry(wrtrans, wr_modifier);
          pulse_trig_trans.copy_from(wrtrans);
          pulse_trig_struct = '{
            reg_name: rname, 
            wr_trans: pulse_trig_trans,
            wr_modifier: wr_modifier
          };
          -> pulse_trig_event; 

        end else 
          sb.record_entry(wrtrans, wr_modifier);

        // read phase
        if (rd_modifier == GET_AHB) begin
          read_single_word_ahb(addr);
          valid_hrdata = addr[2] ? hrdata_o_tb[`AHB64_HI] : hrdata_o_tb[`AHB64_LO]; 
          $display(" Read over AHB: addr =  %-40s (0x%08x), data = 0x%08x", rname, addr, valid_hrdata); 
          rdtrans.update(addr, valid_hrdata, tid); 
        end else if (rd_modifier == GET_APB) begin
          read_single_word_apb(addr);
          $display(" Read over APB: addr =  %-40s (0x%08x), data = 0x%08x", rname, addr, prdata_o_tb); 
          rdtrans.update(addr, prdata_o_tb, tid); 
        end else 
          $error("TB ERROR. Unsupported access rd_modifier %s", rd_modifier.name()); 

        sb.check_entry(rdtrans);

        if (wait_cycles == 0)
          @(posedge clk_tb);
        else
          repeat (wait_cycles) @(posedge clk_tb);
      end

    end

  endtask // write_read_regs

  //================================================================
  // Function Definitions
  //================================================================


  //----------------------------------------------------------------
  // set_security_state()
  //
  // sets the security state explicily to any value between 0..7
  //----------------------------------------------------------------
  function automatic void set_security_state(input security_state_t ss);

      dword_t intr_notif_val; 

      begin
          security_state = '{device_lifecycle: ss.device_lifecycle, debug_locked: ss.debug_locked};

          // TODO. Has hardwired mask bit positions in here. Ideally they should be pulled from tb package. 
          //       Eg: in update_CPTRA_SECURITY_STATE(...)
          set_initval("CPTRA_SECURITY_STATE", ss & 32'h7);  
          update_exp_regval("CPTRA_SECURITY_STATE", ss & 32'h7, SET_DIRECT); 

          intr_notif_val = get_initval("INTR_BRF_NOTIF_INTERNAL_INTR_R") & 32'hffff_fffb | ss.debug_locked & 32'h4;
          set_initval("INTR_BRF_NOTIF_INTERNAL_INTR_R", intr_notif_val); 
          update_exp_regval("INTR_BRF_NOTIF_INTERNAL_INTR_R", intr_notif_val, SET_DIRECT);  
      end
  endfunction // set_security_state


  //----------------------------------------------------------------
  // set_security_state_byname()
  //
  // sets security state by name, eg: "DEBUG_LOCKED_PRODUCTION", "RANDOM" 
  //----------------------------------------------------------------
  function automatic security_state_t set_security_state_byname(input string ss_name="RANDOM");         

    bit [2:0] ss_code;

    begin
      ss_code = (ss_name == "RANDOM") ? $urandom_range(0, 7) : get_ss_code(ss_name);
      set_security_state(security_state_t'(ss_code)); 
      return security_state_t'(ss_code); 
    end
  endfunction // set_security_state_byname 


//----------------------------------------------------------------
// Following tests in include files should ideally be in packages 
// or as programs. For now, this is the only modularization for 
// directed tests planned.
//----------------------------------------------------------------
  `include "fuse_reg_lifecycle_test.svh"   
  `include "fuse_reg_perm_test.svh"     
  `include "fuse_reg_pauser_test.svh"     
  `include "fuse_reg_test.svh"     
  `include "single_soc_reg_test.svh"   
  `include "soc_reg_reset_test.svh"     
  `include "soc_reg_test.svh"     
  `include "rvtime_reg_test.svh"     
  `include "soc_reg_invalid_test.svh"     
  `include "soc_reg_intrblk_test.svh" 
  `include "sha_acc_intrblk_test.svh"
//----------------------------------------------------------------



  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------        

  initial begin : main

    // common initialization steps for all tests 

    generic_input_wires0 = 32'h0; 
    generic_input_wires1 = 32'h0; 

    $write("PLAYBOOK_RANDOM_SEED = %s\n", getenv("PLAYBOOK_RANDOM_SEED"));

    if ($value$plusargs("SOC_IFC_TEST=%s", soc_ifc_testname)) 
      begin : alternate_test
        $display("    =================================================================");
        $display("    Running SOC_IFC_TEST = %s", soc_ifc_testname);
        $display("    =================================================================");

        if (soc_ifc_testname == "soc_reg_pwron_test") begin 
          if (!($value$plusargs("SECURITY_STATE=%s", security_state_testname)))
            security_state_testname = "RANDOM";
          soc_reg_pwron_test(security_state_testname);

        end else if (soc_ifc_testname == "soc_reg_wrmrst_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          soc_reg_wrmrst_test();

        end else if (soc_ifc_testname == "fuse_reg_prod_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          fuse_reg_test();

        end else if (soc_ifc_testname == "fuse_reg_lifecycle_test") begin 
          if ($value$plusargs("SECURITY_STATE=%s", security_state_testname)) 
            fuse_reg_lifecycle_test(security_state_testname);
          else
            fuse_reg_lifecycle_test("RANDOM"); 
 
        end else if (soc_ifc_testname == "soc_reg_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          soc_reg_test();

        end else if (soc_ifc_testname == "rvtime_reg_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          rvtime_reg_test();

        end else if (soc_ifc_testname == "soc_reg_invalid_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          soc_reg_invalid_test();

        end else if (soc_ifc_testname == "soc_reg_intrblk_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          soc_reg_intrblk_test();

        end else if (soc_ifc_testname == "sha_acc_intrblk_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          sha_acc_intrblk_test();

        end else if (soc_ifc_testname == "single_socreg_test") begin 
          if (!($value$plusargs("SOCREG_METHOD_NAME=%s", socreg_method_name))) 
            $display("ERROR with testing one soc_register; must provide method & name for +scoreg_method_name,eg. APB.CPTRA_TIMER_CONFIG");
          else begin
            $value$plusargs("SOCREG_WRCOUNT=%d", socreg_wrcount);
            set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
            sim_dut_init();
            single_socreg_test(socreg_method_name, socreg_wrcount);
          end

        end else if (soc_ifc_testname == "fuse_reg_perm_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          fuse_reg_perm_test();

        end else if (soc_ifc_testname == "fuse_reg_pauser_test") begin 
          set_security_state_byname("RANDOM");
          sim_dut_init();
          fuse_reg_pauser_test();

        end 
   
        @(posedge clk_tb);
        display_test_results();

        $display("\n*** '%s' test simulation done. ***", soc_ifc_testname);
        $finish;
      end  // alternate_test

    else 
      begin : default_test  // Keeping original default test structure 

        $display("    ==============================");  
        $display("   -= Testbench for MBOX started =-");
        $display("    ==============================");
        $display("");

        set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});

        init_sim();
        reset_dut();

        wait (ready_for_fuses == 1'b1);
        //load_fuses();
        write_single_word_apb(MBOX_FUSE_DONE_ADDR, 32'h00000001);
        repeat (5) @(posedge clk_tb);
        
        mbox_test();

        display_test_results();
        
        $display("");
        $display("*** MBOX simulation done. ***");
        $finish;
      end // default_test 
  end // main
endmodule // soc_ifc_tb
