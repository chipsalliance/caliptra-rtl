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

`define FORLOOP_COMB(x) always_comb for (int j = 0; j < x; j++) 
`define STR_RMPFX(astr, bstr) astr.substr(bstr.len(), astr.len() - 1).atoi()



module soc_ifc_tb
  import soc_ifc_pkg::*;
  import mbox_pkg::*;
  import soc_ifc_tb_pkg::*;
  import axi_pkg::*;
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
  `ifndef VERILATOR
  int MAX_CYCLES;
  initial begin
    // To use this from the command line, add "+CLP_MAX_CYCLES=<value>"
    // to override the sim timeout
    if ($value$plusargs("CLP_MAX_CYCLES=%d", MAX_CYCLES)) begin
        $info("Received argument +CLP_MAX_CYCLES, with value %d", MAX_CYCLES);
    end
    else begin
        MAX_CYCLES = 20_000_000;
        $info("No argument provided for CLP_MAX_CYCLES, defaulting to %d", MAX_CYCLES);
    end
  end
  `else
  parameter MAX_CYCLES = 20_000_000;
  `endif

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
  //TODO: Delete APB parameters
  parameter APB_ADDR_WIDTH = 18; 
  parameter APB_DATA_WIDTH = 32; 
  parameter APB_USER_WIDTH = 32; 

  parameter AXI_ADDR_WIDTH = `CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC); // 18;
  parameter AXI_DATA_WIDTH = `CALIPTRA_AXI_DATA_WIDTH; // 32
  parameter AXI_ID_WIDTH   = `CALIPTRA_AXI_ID_WIDTH; // 32
  parameter AXI_USER_WIDTH = `CALIPTRA_AXI_USER_WIDTH; // 32
  parameter AXIM_ADDR_WIDTH = `CALIPTRA_AXI_DMA_ADDR_WIDTH; // 48
  parameter AXIM_DATA_WIDTH = CPTRA_AXI_DMA_DATA_WIDTH;
  parameter AXIM_ID_WIDTH   = CPTRA_AXI_DMA_ID_WIDTH;
  parameter AXIM_USER_WIDTH = CPTRA_AXI_DMA_USER_WIDTH;

  parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  localparam AXI_USER_DEFAULT = 32'hffff_ffff;


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
  reg [AXI_USER_WIDTH-1:0]     axi_user_i_tb;

  reg [AHB_ADDR_WIDTH-1:0]  haddr_i_tb;
  reg [AHB_DATA_WIDTH-1:0]  hwdata_i_tb;
  reg           hsel_i_tb;
  reg           hwrite_i_tb; 
  reg           hready_i_tb;
  reg [1:0]     htrans_i_tb;
  reg [2:0]     hsize_i_tb;

  reg                                 cptra_obf_field_entropy_vld;
  reg [`CLP_OBF_FE_DWORDS-1 :0][31:0] cptra_obf_field_entropy;

  reg                                 cptra_obf_uds_seed_vld;
  reg [`CLP_OBF_UDS_DWORDS-1:0][31:0] cptra_obf_uds_seed;

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
  logic ready_for_mb_processing;
  logic [31:0]  generic_input_wires0; 
  logic [31:0]  generic_input_wires1; 

  logic clear_obf_secrets;
  logic scan_mode; 

 logic aes_input_ready;
 logic aes_output_valid;
 logic aes_status_idle;
 logic aes_req_dv;
 logic aes_req_hold;
 soc_ifc_req_t aes_req_data;
 logic [SOC_IFC_DATA_W-1:0] aes_rdata;
 logic aes_error; 


 assign aes_input_ready = '0; // FIXME - when doing AES val either connect or remove fixme and keep unconnected
 assign aes_output_valid = '0; // FIXME - when doing AES val either connect or remove fixme and keep unconnected
 assign aes_status_idle = '0; // FIXME - when doing AES val either connect or remove fixme and keep unconnected
 assign aes_req_hold = '0; // FIXME - when doing AES val either connect or remove fixme and keep unconnected
 assign aes_rdata = '0; // FIXME - when doing AES val either connect or remove fixme and keep unconnected
 assign aes_error = '0; // FIXME - when doing AES val either connect or remove fixme and keep unconnected 

  // obfuscation, uds and field entropy for observation
  logic [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key_reg;
  logic [`CLP_OBF_FE_DWORDS-1 :0][31:0] obf_field_entropy;
  logic [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed;

/*
  logic [63:0] strap_ss_caliptra_base_addr;
  logic [63:0] strap_ss_mci_base_addr;
  logic [63:0] strap_ss_recovery_ifc_base_addr;
  logic [63:0] strap_ss_otp_fc_base_addr;
  logic [63:0] strap_ss_uds_seed_base_addr;
  logic [31:0] strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset;
  logic [31:0] strap_ss_num_of_prod_debug_unlock_auth_pk_hashes;
  logic [31:0] strap_ss_strap_generic_0;
  logic [31:0] strap_ss_strap_generic_1;
  logic [31:0] strap_ss_strap_generic_2;
  logic [31:0] strap_ss_strap_generic_3;
  logic        ss_debug_intent;
  logic       cptra_ss_debug_intent;

  logic        ss_dbg_manuf_enable;
  logic [63:0] ss_soc_dbg_unlock_level;

  logic [127:0] ss_generic_fw_exec_ctrl;
*/
  //SRAM interface for mbox
  logic mbox_sram_cs;
  logic mbox_sram_we;
  logic [CPTRA_MBOX_ADDR_W-1:0] mbox_sram_addr;
  logic [CPTRA_MBOX_DATA_W-1:0] mbox_sram_wdata;
  logic [CPTRA_MBOX_DATA_W-1:0] mbox_sram_rdata;

  logic [0:15][31:0]          cptra_uds_tb;
  logic [0:7][31:0]          cptra_fe_tb;

  logic     cptra_uds_vld_tb;
  logic     cptra_fe_vld_tb;  

  //mailbox sram gasket
  cptra_mbox_sram_req_t mbox_sram_req;
  cptra_mbox_sram_resp_t mbox_sram_resp;


  //MH. Initialize to default device lifecycle later rather than TIE OFF
  security_state_t security_state, tmp_ss;  // '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED};
  logic            gen_input_wire_toggle;  

  logic [31:0]     generic_input_wires0_q; 
  logic [31:0]     generic_input_wires1_q; 

  //MH. Tick timers
  logic [31:0]   cycle_ctr_since_pwrgood;
  logic [31:0]   cycle_ctr_since_rst;

  bit            reg_sva_off = 1'b1;  // Enable only during register assertion checks

  logic         mailbox_data_avail_tb;

  always_comb begin
    subsystem_mode_tb = dut.soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.SUBSYSTEM_MODE_en;
    $display("Subsystem Mode updated: 0x%0x", subsystem_mode_tb);
  end


  typedef enum logic {
    read = 0,
    write = 1
  } rw_e;

  typedef enum logic {
    MGR = 0, 
    SUB = 1 
  } mgr_sub_e;

  typedef enum logic {
    FAIL = 0, 
    PASS = 1
  } exp_txn_sts_e;

  always_comb begin
    mbox_sram_cs = mbox_sram_req.cs;
    mbox_sram_we = mbox_sram_req.we;
    mbox_sram_addr = mbox_sram_req.addr;
    mbox_sram_wdata = mbox_sram_req.wdata;
    mbox_sram_resp.rdata = mbox_sram_rdata;
  end

  assign hready_i_tb = hreadyout_o_tb;

  // AXI Interface
  axi_if #(
      .AW(AXIM_ADDR_WIDTH),
      .DW(AXIM_DATA_WIDTH),
      .IW(AXIM_ID_WIDTH),
      .UW(AXIM_USER_WIDTH)
  ) m_axi_if (.clk(clk_tb), .rst_n(cptra_rst_b_tb));

  // AXI Interface
  axi_if #(
      .AW(AXI_ADDR_WIDTH),
      .DW(AXI_DATA_WIDTH),
      .IW(AXI_ID_WIDTH),
      .UW(AXI_USER_WIDTH)
  ) s_axi_if (.clk(clk_tb), .rst_n(cptra_rst_b_tb));

  //bind coverage file
  soc_ifc_cov_bind i_soc_ifc_cov_bind();

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  soc_ifc_top #(
             .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
             .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
             .AXI_ID_WIDTH(AXI_ID_WIDTH),
             .AXI_USER_WIDTH(AXI_USER_WIDTH),
             .AXIM_ADDR_WIDTH(AXIM_ADDR_WIDTH),
             .AXIM_DATA_WIDTH(AXIM_DATA_WIDTH),
             .AXIM_ID_WIDTH(AXIM_ID_WIDTH),
             .AXIM_USER_WIDTH(AXIM_USER_WIDTH),
             .AHB_DATA_WIDTH(AHB_DATA_WIDTH), 
             .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH) 
            )
            dut (
             .clk(clk_tb),
             .clk_cg(clk_tb),
             .soc_ifc_clk_cg(clk_tb),
             .rdc_clk_cg(clk_tb),

             .cptra_pwrgood(cptra_pwrgood_tb),
             .cptra_rst_b(cptra_rst_b_tb),


             .ready_for_fuses(ready_for_fuses),
             .ready_for_mb_processing(ready_for_mb_processing),
             .ready_for_runtime(),

             .mailbox_data_avail(mailbox_data_avail_tb),
             .mailbox_flow_done(),

             .aes_input_ready,
             .aes_output_valid,
             .aes_status_idle,
             .aes_req_dv,
             .aes_req_hold,
             .aes_req_data,
             .aes_rdata,
             .aes_error, 

             .recovery_data_avail(1'b0),
             .recovery_image_activated(1'b0),
             
             .security_state(security_state),

             .generic_input_wires({generic_input_wires1, generic_input_wires0}),
             .BootFSM_BrkPoint(1'b0), // TODO
             .generic_output_wires(),

             .s_axi_w_if(s_axi_if.w_sub),
             .s_axi_r_if(s_axi_if.r_sub),

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

             .m_axi_w_if(m_axi_if.w_mgr),
             .m_axi_r_if(m_axi_if.r_mgr),

             .cptra_error_fatal(),
             .cptra_error_non_fatal(),
             .trng_req(),

             .soc_ifc_error_intr(),
             .soc_ifc_notif_intr(),
             .sha_error_intr(),
             .sha_notif_intr(),
             .dma_error_intr(),
             .dma_notif_intr(),
             .timer_intr(),

             .mbox_sram_req(mbox_sram_req),
             .mbox_sram_resp(mbox_sram_resp),

             .rv_ecc_sts(rv_ecc_sts_t'{default:1'b0}),

             .clear_obf_secrets(clear_obf_secrets), 
             .scan_mode(scan_mode), 
             .cptra_obf_key('0),
             .cptra_obf_key_reg(cptra_obf_key_reg),
             .cptra_obf_field_entropy_vld(cptra_fe_vld_tb),
             .cptra_obf_field_entropy(cptra_fe_tb),
             .obf_field_entropy(obf_field_entropy),
             .cptra_obf_uds_seed_vld(cptra_uds_vld_tb),
             .cptra_obf_uds_seed(cptra_uds_tb),
             .obf_uds_seed(obf_uds_seed),

             .strap_ss_caliptra_base_addr(strap_ss_caliptra_base_addr_tb),
             .strap_ss_mci_base_addr(strap_ss_mci_base_addr_tb),
             .strap_ss_recovery_ifc_base_addr(strap_ss_recovery_ifc_base_addr_tb),
             .strap_ss_external_staging_area_base_addr(strap_ss_external_staging_area_base_addr_tb),
             .strap_ss_otp_fc_base_addr(strap_ss_otp_fc_base_addr_tb),
             .strap_ss_uds_seed_base_addr(strap_ss_uds_seed_base_addr_tb),
             .strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset(strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_tb),
             .strap_ss_num_of_prod_debug_unlock_auth_pk_hashes(strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_tb),
             .strap_ss_strap_generic_0(strap_ss_strap_generic_0_tb),
             .strap_ss_strap_generic_1(strap_ss_strap_generic_1_tb),
             .strap_ss_strap_generic_2(strap_ss_strap_generic_2_tb),
             .strap_ss_strap_generic_3(strap_ss_strap_generic_3_tb),
             .strap_ss_caliptra_dma_axi_user(strap_ss_caliptra_dma_axi_user_tb),
             .ss_debug_intent(ss_debug_intent_tb),
             .cptra_ss_debug_intent(cptra_ss_debug_intent_tb),

             .ss_dbg_manuf_enable(),
             .ss_soc_dbg_unlock_level(),

             .ss_generic_fw_exec_ctrl(),

             .nmi_vector(),
             .nmi_intr(),

             .iccm_lock(),
             .iccm_axs_blocked(1'b0), // MH. Tie off here unless need control

             .cptra_noncore_rst_b(cptra_noncore_rst_b_tb),
             .cptra_uc_rst_b(cptra_uc_rst_b_tb),
             .clk_gating_en(),
             .rdc_clk_dis(),
             .fw_update_rst_window(),

             .crypto_error('0),

             .cptra_uncore_dmi_reg_en     ( 1'h0),
             .cptra_uncore_dmi_reg_wr_en  ( 1'h0),
             .cptra_uncore_dmi_reg_rdata  (     ),
             .cptra_uncore_dmi_reg_addr   ( 7'h0),
             .cptra_uncore_dmi_reg_wdata  (32'h0)

            );



  //SRAM for mbox
  initial begin
    mbox_ram1.ram = '{default:8'h0};
  end

  caliptra_sram 
  #(
    .DATA_WIDTH(CPTRA_MBOX_DATA_W),
    //.DATA_WIDTH(32),
    .DEPTH(CPTRA_MBOX_DEPTH)
    //.DEPTH('h8000)
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
  assign scan_mode = 1'b0; 
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
      if (cycle_ctr == MAX_CYCLES ) begin
        $error("Hit max cycle count (%0d) .. stopping",cycle_ctr);
        $finish;
      end
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
  // CPTRA SECUIRTY_STATE, FLOW_STATUS, GENERIC_INPUT_WIRES, SS_CPTRA_DMA_AXI_USER
  //----------------------------------------------------------------

  always_comb update_CPTRA_SECURITY_STATE(scan_mode, security_state.debug_locked, security_state.device_lifecycle);
  always_comb update_CPTRA_FLOW_STATUS(ready_for_fuses, `REG_HIER_BOOT_FSM_PS);
  always_comb update_CPTRA_GENERIC_INPUT_WIRES(generic_input_wires1_q, 1'b1); 
  always_comb update_CPTRA_GENERIC_INPUT_WIRES(generic_input_wires0_q, 1'b0);
  always_comb update_INTR_BRF_NOTIF_INTERNAL_INTR_R(gen_input_wire_toggle, security_state.debug_locked); 
  always_comb update_CPTRA_HW_CONFIG();


  //----------------------------------------------------------------
  // reset_dut()
  //
  // Toggle reset to put the DUT into a well known state.
  //----------------------------------------------------------------
  task reset_dut;
    begin
      $display("*** Toggle reset.");

      //set_generic_input_wires(-1, -1);

      cptra_pwrgood_tb = '0;
      cptra_rst_b_tb = 0;

      //subsystem_mode_tb = dut.soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.SUBSYSTEM_MODE_en;
      //$display("Subsystem Mode: 0x%0x", subsystem_mode_tb);

      set_initval("CPTRA_GENERIC_INPUT_WIRES0", generic_input_wires0);  // The init val will take effect 
      set_initval("CPTRA_GENERIC_INPUT_WIRES1", generic_input_wires1);  // after reset deassertion 

      repeat (5) @(posedge clk_tb);
      $display("Waited 5 clock cycles");

      socregs.unlock_fuses();
      $display("Fuses unlocked");

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

      set_generic_input_wires(-1, -1);
      reset_flow_status();

      cptra_rst_b_tb = 0;

      repeat (5) @(posedge clk_tb);

      cptra_rst_b_tb = 1;
      repeat (5) @(posedge clk_tb);
      $display("*** Warm reset complete. ***");
    end
  endtask // reset_dut

  //----------------------------------------------------------------
  // load_fuses()
  //
  // Load Fuses (required to get other blocks out of reset)
  //----------------------------------------------------------------
  task load_fuses;
    begin
      $display("Loading Fuses");
      for (int i = 0; i < `CLP_OBF_UDS_DWORDS; i++)begin
        //$display("Loading fuse #%d", i);
        //$display(cptra_uds_tb[i]);
        //write_single_word_apb(MBOX_UDS_ADDR + i*4, cptra_uds_tb[i]);
        write_single_word_axi_sub(MBOX_UDS_ADDR + i*4, cptra_uds_tb[i]);
      end     
      $display ("SoC: Writing obfuscated Field Entropy to fuse bank\n");
      for (int i = 0; i < `CLP_OBF_FE_DWORDS; i++)begin
          //write_single_word_apb(MBOX_FE_ADDR + i*4, cptra_fe_tb[i]);
          write_single_word_axi_sub(MBOX_FE_ADDR + i*4, cptra_fe_tb[i]);
      end
      
      $display ("SoC: Writing fuse done register\n");
      //set fuse done
      //write_single_word_apb(MBOX_FUSE_DONE_ADDR, 32'h00000001); 
      write_single_word_axi_sub(MBOX_FUSE_DONE_ADDR, 32'h00000001); 
      
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

      //paddr_i_tb      = 'Z;
      //psel_i_tb       = 0;
      //penable_i_tb    = 0;
      //pwrite_i_tb     = 0;
      //pwdata_i_tb     = 0;
     // axi_user_i_tb     = 0;

      //reset w_mgr
      m_axi_if.awready = 0;
      m_axi_if.wready = 0;
      m_axi_if.bvalid = 0;
      m_axi_if.bid = 0;
      m_axi_if.bresp = 0;

      //reset r_mgr
      m_axi_if.arready = 0;
      m_axi_if.rdata = 0;
      m_axi_if.rresp = 0;
      m_axi_if.rid = 0;
      m_axi_if.rlast = 0;
      m_axi_if.rvalid = 0;
      
      //reset w_sub
      s_axi_if.awaddr = 0;
      s_axi_if.awburst = 0;
      s_axi_if.awsize = 0;
      s_axi_if.awlen = 0;
      s_axi_if.awuser = 0;
      s_axi_if.awid = 0;
      s_axi_if.awlock = 0;
      s_axi_if.awvalid = 0;
      s_axi_if.wdata = 0;
      s_axi_if.wstrb = 0;
      s_axi_if.wvalid = 0;
      s_axi_if.wlast = 0;
      s_axi_if.bready = 0;

      //reset r_sub
      s_axi_if.araddr = 0;
      s_axi_if.arburst = 0;
      s_axi_if.arsize = 0;
      s_axi_if.arlen = 0;
      s_axi_if.aruser = 0;
      s_axi_if.arid = 0;
      s_axi_if.arlock = 0;
      s_axi_if.arvalid = 0;
      s_axi_if.rready = 0;

      //Key for UDS 
      //cptra_uds_tb = {256'hb32e2b171b63827034ebb0d1909f7ef1d51c5f82c1bb9bc26bc4ac4dccdee835,
      //                256'h7dca6154c2510ae1c87b1b422b02b621bb06cac280023894fcff3406af08ee9b,
      //                256'he1dd72419beccddff77c722d992cdcc87e9c7486f56ab406ea608d8c6aeb060c,
      //                256'h64cf2785ad1a159147567e39e303370da445247526d95942bf4d7e88057178b0};
      cptra_uds_tb = 512'hb32e2b171b63827034ebb0d1909f7ef1d51c5f82c1bb9bc26bc4ac4dccdee8357dca6154c2510ae1c87b1b422b02b621bb06cac280023894fcff3406af08ee9b;
      cptra_uds_vld_tb = 1'b1;
      
      //Key for FE
      cptra_fe_tb = 256'he4046d05385ab789c6a72866e08350f93f583e2a005ca0faecc32b5cfc323d46;
      cptra_fe_vld_tb = 1'b1;

      // SS Straps
      ss_debug_intent_tb = 1'b0;
      strap_ss_caliptra_dma_axi_user_tb = AXI_USER_DEFAULT;
      strap_ss_caliptra_base_addr_tb = '0;
      strap_ss_mci_base_addr_tb = '0;
      strap_ss_recovery_ifc_base_addr_tb = '0;
      strap_ss_external_staging_area_base_addr_tb = '0;
      strap_ss_otp_fc_base_addr_tb = '0;
      strap_ss_uds_seed_base_addr_tb = '0;
      strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_tb = '0;
      strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_tb = '0;
      strap_ss_strap_generic_0_tb = '0;
      strap_ss_strap_generic_1_tb = '0;
      strap_ss_strap_generic_2_tb = '0;
      strap_ss_strap_generic_3_tb = '0;


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
  // axi_txn_check())
  //
  // Check if the AXI transaction was successful.
  //----------------------------------------------------------------
  task axi_txn_check(input axi_resp_e resp, input rw_e rw, input exp_txn_sts_e exp_txn_sts = PASS);
    begin
      logic error;
      if (((resp == AXI_RESP_SLVERR) | (resp == AXI_RESP_DECERR)) & (exp_txn_sts == PASS)) begin
        error = 1;
        error_ctr += 1;
      end
      else begin
        error = 0;
        $display("AXI txn was successful");
      end 
      $display("AXN txn tcheck");
      if (error & (rw == read) & (exp_txn_sts == PASS)) begin //read     
        $error("AXI Read error");
      end
      else if (error & (rw == write) & (exp_txn_sts == PASS)) begin //write
        $error("AXI Write error");
      end
    end
  endtask

  //----------------------------------------------------------------
  // write_single_word_axi())
  //
  // Write the given word to the DUT using the AXI interface.
  //----------------------------------------------------------------
  task write_single_word_axi_sub(input [31 : 0] address,
                                 input [31 : 0] word, 
                                 input exp_txn_sts_e exp_txn_sts = PASS);
    begin
      axi_resp_e resp;
      logic [AXI_USER_WIDTH-1:0] resp_user;
      $display("AXI Write transaction to address 0x%x", address);
      s_axi_if.axi_write_single(
        .addr(address),
        .user('hFFFFFFFF),
        .id(0),
        .lock(0),
        .data(word),
        .write_user(0),
        .resp(resp),
        .resp_user(resp_user));
      //$display("Checking if AXI write was successful");
      axi_txn_check(resp, write, exp_txn_sts);
      //$display("Done writing to address 0x%x", address);
    end
  endtask

  //----------------------------------------------------------------
  // write_single_word_axi_user_sub())
  //
  // Write the given word to the DUT using the AXI interface setting axi_user.
  //----------------------------------------------------------------
  task write_single_word_axi_user_sub(input [31 : 0] address,
                                 input [31 : 0] word, 
                                 input [31 : 0] axi_user,
                                 input exp_txn_sts_e exp_txn_sts = PASS);
    begin
      axi_resp_e resp;
      logic [AXI_USER_WIDTH-1:0] resp_user;
      //$display("AXI Write transaction");
      s_axi_if.axi_write_single(
      .addr(address),
      .user(axi_user),
      .id(0),
      .lock(0),
      .data(word),
      .write_user(0),
      .resp(resp),
      .resp_user(resp_user));
      //$display("Checking if AXI write was successful");
      axi_txn_check(resp, write, exp_txn_sts);
    end
  endtask

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
  // write_block_axi_sub()
  //
  // Write the given block to the dut.
  //----------------------------------------------------------------
  task write_block_axi_sub(input [127 : 0] block);
    begin
      write_single_word_axi_sub(MBOX_ADDR_DATAIN, block[127  :  96]);
      write_single_word_axi_sub(MBOX_ADDR_DATAIN, block[95   :  64]);
      write_single_word_axi_sub(MBOX_ADDR_DATAIN, block[63   :  32]);
      write_single_word_axi_sub(MBOX_ADDR_DATAIN, block[31   :   0]);
    end
  endtask // write_block_axi_sub



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
  
  //----------------------------------------------------------------
  // read_single_word_axi())
  //
  // Read the given word to the DUT using the AXI interface.
  //----------------------------------------------------------------
  task read_single_word_axi_sub(input [31 : 0] address,
                                output [31 : 0] rdata, 
                                input exp_txn_sts_e exp_txn_sts = PASS);
    begin
      axi_resp_e resp;
      logic [AXI_USER_WIDTH-1:0] resp_user;
      s_axi_if.axi_read_single(
        .addr(address),
        .user('hFFFFFFFF),
        .id(0),
        .lock(0),
        .data(rdata),
        .resp_user(resp_user),
        .resp(resp));
      //$display("AXi SUB read complete");
      //$display("Checking if AXI read was successful");
      axi_txn_check(resp, read, exp_txn_sts);
      //$display("AXI txn check complete");
    end
  endtask // read_single_word_axi_sub

  //----------------------------------------------------------------
  // read_single_word_axi_user_sub()
  //
  // Read the given word to the DUT using the AXI interface setting axi_user.
  //----------------------------------------------------------------
  task read_single_word_axi_user_sub(input [31 : 0] address,
                                     input [31 : 0] word,
                                     input [31 : 0] axi_user,
                                     output [31 : 0] rdata);
    begin
      axi_resp_e resp;
      logic [AXI_USER_WIDTH-1:0] resp_user;
      s_axi_if.axi_read_single(
        .addr(address),
        .user(axi_user),
        .id(0),
        .lock(0),
        .data(rdata),
        .resp_user(resp_user),
        .resp(resp));
      //$display("AXi SUB read complete");
      //$display("Checking if AXI read was successful");
      axi_txn_check(resp, read);
      //$display("AXI txn check complete");
    end
  endtask // read_single_word_axi_user_sub

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
  // read_result_axi_sub()
  //
  // Read the result block in the dut.
  //----------------------------------------------------------------
  task read_result_axi_sub(output [127:0]  r_data);
    begin

      read_single_word_axi_sub(MBOX_ADDR_DATAOUT, r_data[127:96]);
      //r_data[127:96] = ;
      read_single_word_axi_sub(MBOX_ADDR_DATAOUT, r_data[ 95:64]);
      //r_data[ 95:64] = prdata_o_tb;
      read_single_word_axi_sub(MBOX_ADDR_DATAOUT, r_data[ 63:32]);
      //r_data[ 63:32] = prdata_o_tb;
      read_single_word_axi_sub(MBOX_ADDR_DATAOUT, r_data [ 31:0]);
      //r_data[ 31: 0] = prdata_o_tb;
  
    end
  endtask // read_result_axi_sub

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
  // wait_unlock_axi()
  //
  // wait for the mailbox to unlock before send in anything
  //----------------------------------------------------------------
  task wait_unlock_axi();
    logic [31:0] rdata;
    begin
      read_single_word_axi_sub(MBOX_ADDR_LOCK, rdata);
      while (rdata != 0)
        begin
          read_single_word_axi_sub(MBOX_ADDR_LOCK, rdata);
        end
    end
  endtask // wait_unlock_axi

  //----------------------------------------------------------------
  // set_generic_input_wires()
  //
  // sets the generic_input_wires to a predetermined or random value
  //----------------------------------------------------------------
  task set_generic_input_wires(input int v0, int v1);

    begin
      generic_input_wires0 = (v0 < 0) ? $urandom() : v0;
      generic_input_wires1 = (v1 < 0) ? $urandom() : v1;
      repeat (2) @(posedge clk_tb);
      update_CPTRA_GENERIC_INPUT_WIRES(generic_input_wires0_q, 1'b0); 
      update_CPTRA_GENERIC_INPUT_WIRES(generic_input_wires1_q, 1'b1); 
    end

  endtask // set_generic_input_wires


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
    logic [31:0] read_data;
    
    begin
      $display("*** TC %0d mailbox AHB test started.", tc_number);
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

      // wait for mailbox_data_avail
      wait(mailbox_data_avail_tb == 1);

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);

      // SOC read MBOX_ADDR_CMD
      read_single_word_axi_sub(MBOX_ADDR_CMD, read_data);

      // SOC read MBOX_ADDR_DLEN
      read_single_word_axi_sub(MBOX_ADDR_DLEN, read_data);

      // SOC read block data
      read_result_axi_sub(result_data);

      //set status
      write_single_word_axi_sub(MBOX_ADDR_STATUS, 32'h00000002);

      // read status 
      read_single_word_ahb(MBOX_ADDR_STATUS);
      read_data =  MBOX_ADDR_STATUS[2] ?  hrdata_o_tb[`AHB64_HI] :hrdata_o_tb[`AHB64_LO];
      $display("Status = 0x%x", read_data);

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
  // mbox_axi_test()
  //
  // mailbox axi test for single block
  //----------------------------------------------------------------
  task mbox_axi_test (input [7 : 0]   tc_number,
                      input [127 : 0] block
    );
    reg [63 : 0] start_time;
    reg [63 : 0] end_time;

    begin
      $display("*** TC %0d mailbox test started.", tc_number);
      tc_ctr = tc_ctr + 1;
      start_time = cycle_ctr;

      // poll for lock register
      wait_unlock_axi();

      //write to MBOX_ADDR_CMD
      write_single_word_axi_sub(MBOX_ADDR_CMD, 32'hDEADBEEF);

      // write to MBOX_ADDR_DLEN
      write_single_word_axi_sub(MBOX_ADDR_DLEN, 32'h00000010);

      // write a block in
      write_block_axi_sub(block);
      @(posedge clk_tb);

      // execute
      write_single_word_axi_sub(MBOX_ADDR_EXECUTE, 32'h00000001);
      repeat (20) @(posedge clk_tb);

      // wait_ready();

      end_time = cycle_ctr - start_time;
      $display("*** Single block test processing time = %01d cycles", end_time);

      // uC read MBOX_ADDR_CMD
      read_single_word_ahb(MBOX_ADDR_CMD);

      // uC read MBOX_ADDR_DLEN
      read_single_word_ahb(MBOX_ADDR_DLEN);

      // uC read MBOX_ADDR_DATAOUT
      read_result_ahb(result_data);

      //set status
      write_single_word_ahb(MBOX_ADDR_STATUS, 32'h00000002);

      // reset excecute
      write_single_word_axi_sub(MBOX_ADDR_EXECUTE, 32'h00000000);

      if (result_data == block)begin
        $display("*** TC %0d successful.", tc_number);
        $display("");
      end
      else begin
        $display("*** ERROR: TC %0d NOT successful.", tc_number);
        $display("Expected: 0x%032x", block);
        $display("Got:      0x%032x", result_data);
        $display("");

        error_ctr = error_ctr + 1;
      end
    end
  endtask // mbox_axi_test

    //----------------------------------------------------------------
  // mbox_test()
  //----------------------------------------------------------------
  task mbox_test;
    reg [127 : 0] ahb_message_1;
    reg [127 : 0] axi_message_1;

    begin
      ahb_message_1 = 128'h11111111222222223333333344444444;

      //apb_message_1 = 128'h66666666777777778888888899999999;
      axi_message_1 = 128'h66666666777777778888888899999999;


      $display("mailbox ahb test");
      $display("---------------------");
      mbox_ahb_test(8'h01, ahb_message_1);

      $display("mailbox axi test");
      $display("---------------------");
      //mbox_apb_test(8'h01, apb_message_1);
      mbox_axi_test(8'h01, axi_message_1);


    end
  endtask // mbox_test


  //----------------------------------------------------------------
  // sim_dut_init();
  // 
  // common sim and dut initialization routines for register tests 
  //----------------------------------------------------------------
  task sim_dut_init(input logic debug = 1'b0, input logic drive_straps = 1'b0);

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
        if (debug)
          ss_debug_intent_tb = 1'b1;
        if (drive_straps) begin
          strap_ss_caliptra_base_addr_tb = {$urandom, $urandom};
          strap_ss_mci_base_addr_tb = {$urandom, $urandom};
          strap_ss_recovery_ifc_base_addr_tb = {$urandom, $urandom};
          strap_ss_external_staging_area_base_addr_tb = {$urandom, $urandom};
          strap_ss_otp_fc_base_addr_tb = {$urandom, $urandom};
          strap_ss_uds_seed_base_addr_tb = {$urandom, $urandom};
          strap_ss_prod_debug_unlock_auth_pk_hash_reg_bank_offset_tb = $urandom;
          strap_ss_num_of_prod_debug_unlock_auth_pk_hashes_tb = $urandom;
          strap_ss_strap_generic_0_tb = $urandom;
          strap_ss_strap_generic_1_tb = $urandom;
          strap_ss_strap_generic_2_tb = $urandom;
          strap_ss_strap_generic_3_tb = $urandom;
          strap_ss_caliptra_dma_axi_user_tb = $urandom;
        end
        reset_dut();

        wait (ready_for_fuses == 1'b1);
        update_CPTRA_FLOW_STATUS(int'(ready_for_fuses), `REG_HIER_BOOT_FSM_PS);
        // set_initval("CPTRA_FLOW_STATUS", 32'h4000_0000); 
        // update_exp_regval("CPTRA_FLOW_STATUS", 32'h4000_0000, SET_DIRECT); 

        repeat (5) @(posedge clk_tb);
      end
    end

  endtask // sim_dut_init

  
  //----------------------------------------------------------------
  // simulate_caliptra_boot();
  //
  // Set boot fuse write and boot status over AXI 
  //----------------------------------------------------------------
  task simulate_caliptra_boot;
    begin
      $display("*** Perform caliptra boot simulation by writing CPTRA_FUSE_WR_DONE and CPTRA_BOOTFSM_GO. ***");
      // Enable release of Caliptra core from reset & simulate FW boot
      wait(ready_for_fuses == 1'b1);
      write_single_word_axi_sub(socregs.get_addr("CPTRA_FUSE_WR_DONE"), 32'h1); 
      //$display("Done writing CPTRA_FUSE_WR_DONE");
      update_exp_regval("CPTRA_FUSE_WR_DONE", 32'h1, SET_AXI);
      socregs.lock_fuses();

      repeat (3) @(posedge clk_tb); 
      write_single_word_axi_sub(socregs.get_addr("CPTRA_BOOTFSM_GO"), 32'h1); 
      update_exp_regval("CPTRA_BOOTFSM_GO", 32'h1, SET_AXI);

      repeat (20) @(posedge clk_tb); // simulate FW boot
      $display("*** Done caliptra boot simulation. ***");
    end
  endtask // simulate_caliptra_boot



  //----------------------------------------------------------------
  // write_regs()
  //
  // Utility for tracking/writing to list of registers over AXI/AHB
  //----------------------------------------------------------------
  task write_regs(input access_t modifier, strq_t reglist, int tid, int wait_cycles, input exp_txn_sts_e exp_txn_sts=PASS);
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
        end else if (modifier == SET_AXI) begin
          write_single_word_axi_sub(addr, wrtrans.data, exp_txn_sts); 
          $display("Write over AXI: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, wrtrans.data);
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
  // Utility for reading single register over AXI/AHB and check if within range.
  // NOTE. Wait times must be added explcitly outside routine
  //-----------------------------------------------------------------------------
  task read_reg_chk_inrange(input access_t modifier, string rname, int tid, int minval, int maxval, input exp_txn_sts_e exp_txn_sts = PASS); 

    word_addr_t addr;
    WordTransaction rdtrans;
    automatic logic [31:0] valid_hrdata; 
    automatic logic [31:0] valid_axi_rdata;

    begin
      rdtrans = new();
      addr = socregs.get_addr(rname);  

      if (modifier == GET_AHB) begin 
          read_single_word_ahb(addr);
          valid_hrdata =  addr[2] ?  hrdata_o_tb[`AHB64_HI] :hrdata_o_tb[`AHB64_LO]; 
          $display(" Read over AHB: addr =  %-40s (0x%08x), data = 0x%08x", rname, addr, valid_hrdata); 
          rdtrans.update(addr, valid_hrdata, tid); 
      end else if (modifier == GET_AXI) begin
        read_single_word_axi_sub(addr, valid_axi_rdata, exp_txn_sts);
        $display(" Read over AXI: addr =  %-40s (0x%08x), data = 0x%08x", rname, addr, valid_axi_rdata); 
        rdtrans.update_byname(rname, valid_axi_rdata,  tid); 
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
  task write_reg_trans(access_t modifier, WordTransaction wrtrans, logic [31:0] axi_user=AXI_USER_DEFAULT, string pfx="DEFAULT", input exp_txn_sts_e exp_sts=PASS);
    string rname;
    word_addr_t addr;

    begin
        addr = wrtrans.addr;
        rname = socregs.get_name(addr); 

        if (modifier == SET_AHB) begin
          write_single_word_ahb(addr, wrtrans.data); 
          $display("Write over AHB: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, wrtrans.data);
        end else if (modifier == SET_AXI) begin
          if (axi_user != AXI_USER_DEFAULT) begin
            write_single_word_axi_user_sub(addr, wrtrans.data, axi_user, exp_sts); 
            $display("Write over AXI with non-default axi_user: addr = %-40s (0x%08x), data = 0x%08x", 
              rname, addr, wrtrans.data);
          end else begin
            write_single_word_axi_sub(addr, wrtrans.data, exp_sts); 
            $display("Write over AXI: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, wrtrans.data);
          end
        end else 
          $error("TB ERROR. Unsupported access modifier %s", modifier.name()); 

        sb.record_entry(wrtrans, modifier, pfx);
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
                      input logic [31:0] axi_user=AXI_USER_DEFAULT); 
    string rname;
    word_addr_t addr;
    automatic logic [31:0] valid_hrdata; 
    automatic logic [31:0] valid_rdata;

    begin
        addr = rdtrans.addr;
        rname = socregs.get_name(addr); 

        if (modifier == GET_AHB) begin
          read_single_word_ahb(addr); 
          valid_hrdata =  addr[2] ?  hrdata_o_tb[`AHB64_HI] :hrdata_o_tb[`AHB64_LO]; 
          rdtrans.data = valid_hrdata; 
          $display(" Read over AHB: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, rdtrans.data);
        end else if (modifier == GET_AXI) begin
          if (axi_user != AXI_USER_DEFAULT) begin
            read_single_word_axi_user_sub(addr, rdtrans.data, axi_user, valid_rdata); 
            rdtrans.data = valid_rdata;
            $display(" Read over AXI with explicit axi_user: addr = %-40s (0x%08x), data = 0x%08x", 
              rname, addr, rdtrans.data);
          end else begin
            read_single_word_axi_sub(addr, valid_rdata); 
            rdtrans.data = valid_rdata;
            $display(" Read over AXI: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, rdtrans.data);
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
    automatic logic [31:0] valid_axi_rdata;

    begin
      $display("Read regs");
      rdtrans = new();

      if (tid < 0) begin
        tid_autoinc = 1;
        tid = 0;
      end 

      $display("");

      foreach (reglist[i]) begin 
        rname = reglist[i];
        addr = socregs.get_addr(rname); 
        //$display("Current reg: %s", rname);
        if (tid_autoinc) 
          tid += 1;

        if (modifier == GET_AHB) begin
          read_single_word_ahb(addr);
          valid_hrdata =  addr[2] ?  hrdata_o_tb[`AHB64_HI] :hrdata_o_tb[`AHB64_LO]; 
          $display(" Read over AHB: addr =  %-40s (0x%08x), data = 0x%08x on cycle %08d", rname, addr, valid_hrdata, cycle_ctr); 
          rdtrans.update(addr, valid_hrdata, tid); 
        end else if (modifier == GET_AXI) begin
          //$display("read_regs::AXI SUB read");
          read_single_word_axi_sub(addr, valid_axi_rdata);
          // $display(" Read over APB: addr =  %-40s (0x%08x), data = 0x%08x at time %12t (cycle %08d)", rname, addr, prdata_o_latched, $realtime, cycle_ctr); // used to be   prdata_o_tb
          $display(" Read over AXI: addr =  %-40s (0x%08x), data = 0x%08x on cycle %08d", rname, addr, valid_axi_rdata, cycle_ctr); // used to be   prdata_o_tb
          // rdtrans.update(addr, prdata_o_latched, tid);  // used to be prdata_o_tb
          rdtrans.update(addr, valid_axi_rdata, tid);  
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
    automatic logic [31:0] valid_axi_rdata;

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
        end else if (wr_modifier == SET_AXI) begin
          write_single_word_axi_sub(addr, wrtrans.data); 
          $display("Write over AXI: addr = %-40s (0x%08x), data = 0x%08x", rname, addr, wrtrans.data);
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
        end else if (rd_modifier == GET_AXI) begin
          read_single_word_axi_sub(addr, valid_axi_rdata);
          $display(" Read over AXI: addr =  %-40s (0x%08x), data = 0x%08x", rname, addr, valid_axi_rdata); 
          rdtrans.update(addr, valid_axi_rdata, tid); 
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
  `include "fuse_reg_axi_user_test.svh"     
  `include "fuse_reg_test.svh"   
  `include "fuse_cptra_cap_test.svh"  
  `include "ss_strap_reg_test.svh"     
  `include "ss_strap_reg_lifecycle_test.svh"   
  `include "single_soc_reg_test.svh"   
  `include "soc_reg_reset_test.svh"     
  `include "soc_reg_test.svh"     
  `include "rvtime_reg_test.svh"     
  `include "soc_reg_invalid_test.svh"     
  `include "soc_reg_intrblk_test.svh" 
  `include "sha_acc_intrblk_test.svh"
  `include "debug_unlock_prod_test.svh"
  `include "debug_unlock_manuf_test.svh"
  `include "ss_strap_reg_reset_test.svh"
  `include "ss_soc_dbg_unlock_level_test.svh"
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

        end else if (soc_ifc_testname == "fuse_cptra_cap_reg_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          fuse_cptra_cap_reg_test();

        end else if (soc_ifc_testname == "ss_strap_reg_prod_test") begin 
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init();
          ss_strap_reg_test();

        end else if (soc_ifc_testname == "fuse_reg_lifecycle_test") begin 
          if ($value$plusargs("SECURITY_STATE=%s", security_state_testname)) 
            fuse_reg_lifecycle_test(security_state_testname);
          else
            fuse_reg_lifecycle_test("RANDOM"); 

        end else if (soc_ifc_testname == "ss_strap_reg_lifecycle_test") begin 
          if ($value$plusargs("SECURITY_STATE=%s", security_state_testname)) 
            ss_strap_reg_lifecycle_test(security_state_testname);
          else
            ss_strap_reg_lifecycle_test("RANDOM"); 
   
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
            $display("ERROR with testing one soc_register; must provide method & name for +scoreg_method_name,eg. AXI.CPTRA_TIMER_CONFIG");
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

        end else if (soc_ifc_testname == "fuse_reg_axi_user_test") begin 
          set_security_state_byname("RANDOM");
          sim_dut_init();
          fuse_reg_axi_user_test();

        end else  if (soc_ifc_testname == "debug_unlock_prod_test") begin
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init(.debug(1'b1));
          debug_unlock_prod_test();

        end else  if (soc_ifc_testname == "debug_unlock_manuf_test") begin
          set_security_state('{device_lifecycle: DEVICE_MANUFACTURING, debug_locked: DEBUG_LOCKED});
          sim_dut_init(.debug(1'b1));
          debug_unlock_manuf_test();

        end else if (soc_ifc_testname == "ss_strap_reg_pwron_test") begin
          set_security_state('{device_lifecycle: DEVICE_MANUFACTURING, debug_locked: DEBUG_LOCKED});
          sim_dut_init(.drive_straps(1'b1));
          ss_strap_reg_pwron_test();

        end else if (soc_ifc_testname == "ss_strap_reg_wrmrst_test") begin
          set_security_state('{device_lifecycle: DEVICE_MANUFACTURING, debug_locked: DEBUG_LOCKED});
          sim_dut_init(.drive_straps(1'b1));
          ss_strap_reg_wrmrst_test();

        end else if (soc_ifc_testname == "ss_soc_dbg_unlock_level_test") begin
          set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});
          sim_dut_init(.debug(1'b1));
          ss_soc_dbg_unlock_level_test();

        end

        @(posedge clk_tb);
        display_test_results();

        $display("\n*** '%s' test simulation done. ***", soc_ifc_testname);
        $finish;
      end  // alternate_test

    else 
      begin : default_test  // Keeping original default test structure 

        logic [31:0] rdata;
        $display("    ==============================");  
        $display("   -= Testbench for MBOX started =-");
        $display("    ==============================");
        $display("");

        set_security_state('{device_lifecycle: DEVICE_PRODUCTION, debug_locked: DEBUG_LOCKED});

        $display("Initialize simulation");
        init_sim();
        $display("Reset DUT");
        reset_dut();

        $display("Wait for ready_for_fuses to be asserted");
        wait (ready_for_fuses == 1'b1);
        $display("Ready for fuses has been asserted. Moving on");
        load_fuses();
        //write_single_word_ahb(MBOX_FUSE_DONE_ADDR, 32'h00000001);
        //write_single_word_axi(SUB, MBOX_FUSE_DONE_ADDR, 32'h00000001);
        //read_single_word_axi_sub(MBOX_FUSE_DONE_ADDR, rdata);
        //write_single_word_apb(MBOX_FUSE_DONE_ADDR, 32'h00000001);
        repeat (5) @(posedge clk_tb);
        
        $display("MBOX test");
        mbox_test();

        display_test_results();
        
        $display("");
        $display("*** MBOX simulation done. ***");
        $finish;
      end // default_test 
  end // main
endmodule // soc_ifc_tb
