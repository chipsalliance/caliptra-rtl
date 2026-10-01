//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// Description: This top level module instantiates all synthesizable
//    static content.  This and tb_top.sv are the two top level modules
//    of the simulation.
//
//    This module instantiates the following:
//        DUT: The Design Under Test
//        Interfaces:  Signal bundles that contain signals connected to DUT
//        Driver BFM's: BFM's that actively drive interface signals
//        Monitor BFM's: BFM's that passively monitor interface signals
//
//----------------------------------------------------------------------

//----------------------------------------------------------------------
//

module hdl_top;

import ECC_parameters_pkg::*;
import uvmf_base_pkg_hdl::*;

  // pragma attribute hdl_top partition_module_xrtl
// pragma uvmf custom clock_generator begin
  bit clk;
  // Instantiate a clk driver
  // tbx clkgen
  initial begin
    clk = 0;
    #0ns;
    forever begin
      clk = ~clk;
      #5ns;
    end
  end
// pragma uvmf custom clock_generator end

// pragma uvmf custom reset_generator begin
  bit rst;
  // Instantiate a rst driver
  // tbx clkgen
  initial begin
    rst = 0;
    #200ns;
    rst =  1;
  end
// pragma uvmf custom reset_generator end

  // pragma uvmf custom module_item_additional begin
    import kv_defines_pkg::*;
    import kv_defines_pkg::*;
    wire transaction_flag_out_monitor_top;
    wire [63:0] hrdata_64;
    wire hreadyout_top;
    wire [1:0] op_top;
    wire [2:0] test_top;
    wire ecc_busy;
    int max_operation_cycles = 1000000;
    int max_total_cycles = 20000000;
    int unsigned operation_cycles = 0;
    int unsigned total_cycles = 0;

    initial begin
      if ($value$plusargs("ECC_MAX_OP_CYCLES=%d", max_operation_cycles) &&
          (max_operation_cycles <= 0))
        $fatal(1, "ECC_MAX_OP_CYCLES must be positive");
      if ($value$plusargs("ECC_MAX_CYCLES=%d", max_total_cycles) &&
          (max_total_cycles <= 0))
        $fatal(1, "ECC_MAX_CYCLES must be positive");
      $display("ECC watchdog: operation limit %0d cycles, total limit %0d cycles",
               max_operation_cycles, max_total_cycles);
    end

    always @(posedge clk) begin
      total_cycles++;
      if (!ECC_in_agent_bus.ecc_rst_n || !ecc_busy)
        operation_cycles = 0;
      else
        operation_cycles++;
      if (operation_cycles >= max_operation_cycles)
        $fatal(1, "* TESTCASE FAILED: ECC operation exceeded %0d cycles (op=%0d)",
               max_operation_cycles, op_top);
      if (total_cycles >= max_total_cycles)
        $fatal(1, "* TESTCASE FAILED: ECC simulation exceeded %0d cycles",
               max_total_cycles);
    end

    kv_rd_resp_t [1:0] kv_rd_resp_stub = '{kv_rd_resp_t'(0), kv_rd_resp_t'(0)};
    kv_wr_resp_t       kv_wr_resp_stub = kv_wr_resp_t'(0);

    //PCR Signing
    pcr_signing_t pcr_signing_data_stub = pcr_signing_t'(0);
  // pragma uvmf custom module_item_additional end

  // Instantiate the signal bundle, monitor bfm and driver bfm for each interface.
  // The signal bundle, _if, contains signals to be connected to the DUT.
  // The monitor, monitor_bfm, observes the bus, _if, and captures transactions.
  // The driver, driver_bfm, drives transactions onto the bus, _if.
  ECC_in_if  ECC_in_agent_bus(
     // pragma uvmf custom ECC_in_agent_bus_connections begin
     .clk(clk), .rst_n(rst),
     .hrdata(hrdata_64),
     .hreadyout(hreadyout_top),
     .op(op_top),
     .test(test_top),
     .transaction_flag_out_monitor(transaction_flag_out_monitor_top)
     // pragma uvmf custom ECC_in_agent_bus_connections end
     );
  ECC_out_if  ECC_out_agent_bus(
     // pragma uvmf custom ECC_out_agent_bus_connections begin
     .clk(clk), .rst_n(rst),
     .hrdata(hrdata_64),
     .hreadyout(hreadyout_top),
     .op(op_top),
     .test(test_top),
     .transaction_flag_out_monitor(transaction_flag_out_monitor_top)
     // pragma uvmf custom ECC_out_agent_bus_connections end
     );
  ECC_in_monitor_bfm  ECC_in_agent_mon_bfm(ECC_in_agent_bus.monitor_port);
  ECC_out_monitor_bfm  ECC_out_agent_mon_bfm(ECC_out_agent_bus.monitor_port);
  ECC_in_driver_bfm  ECC_in_agent_drv_bfm(ECC_in_agent_bus.initiator_port);

  // pragma uvmf custom dut_instantiation begin
  // UVMF_CHANGE_ME : Add DUT and connect to signals in _bus interfaces listed above
  // Instantiate your DUT here
  // These DUT's instantiated to show verilog and vhdl instantiation
  // verilog_dut         dut_verilog(   .clk(clk), .rst(rst), .in_signal(vhdl_to_verilog_signal), .out_signal(verilog_to_vhdl_signal));
  // vhdl_dut            dut_vhdl   (   .clk(clk), .rst(rst), .in_signal(verilog_to_vhdl_signal), .out_signal(vhdl_to_verilog_signal));

  ecc_top #(
      .AHB_DATA_WIDTH   (64),
      .AHB_ADDR_WIDTH   (15)
  ) dut (
      .clk              (ECC_in_agent_bus.clk),
      .reset_n          (ECC_in_agent_bus.ecc_rst_n),
      .cptra_pwrgood    (),

      .haddr_i          (ECC_in_agent_bus.haddr[14:0]),
      .hwdata_i         (ECC_in_agent_bus.hwdata),
      .hsel_i           (ECC_in_agent_bus.hsel),
      .hwrite_i         (ECC_in_agent_bus.hwrite),
      .hready_i         (ECC_in_agent_bus.hready),
      .htrans_i         (ECC_in_agent_bus.htrans),
      .hsize_i          (ECC_in_agent_bus.hsize),

      .hresp_o          (ECC_out_agent_bus.hresp),
      .hreadyout_o      (ECC_out_agent_bus.hreadyout),
      .hrdata_o         (hrdata_64),

      // KV interface
      .kv_read(),
      .kv_write(),
      .kv_rd_resp(kv_rd_resp_stub),
      .kv_wr_resp(kv_wr_resp_stub),

      //PCR Signing
      .pcr_signing_data(pcr_signing_data_stub),

      .ocp_lock_in_progress(1'b0),
      .busy_o           (ecc_busy),
      .error_intr       (),
      .notif_intr       (),
      .debugUnlock_or_scan_mode_switch('0)
  );

  ecc_top_cov_bind i_ecc_top_cov_bind();

  bit add_store_pending = 0;
  bit mult_store_pending = 0;
  bit mult_completed = 0;
  bit mult_running = 0;

  always @(posedge clk) begin
    if (!ECC_in_agent_bus.ecc_rst_n || dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.zeroize) begin
      add_store_pending = 0;
      mult_store_pending = 0;
      mult_completed = 0;
      mult_running = 0;
    end
    else begin
      if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_instr_s.opcode.add_en) begin
        if (add_store_pending)
          $fatal(1, "* TESTCASE FAILED: ADD issued before prior store");
        add_store_pending = 1;
      end
      if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_instr_s.opcode.add_we) begin
        if (!add_store_pending)
          $fatal(1, "* TESTCASE FAILED: ADD store without issue");
        add_store_pending = 0;
      end
      if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_instr_s.opcode.mult_en) begin
        if (mult_store_pending)
          $fatal(1, "* TESTCASE FAILED: MUL issued before prior store");
        mult_store_pending = 1;
        mult_completed = 0;
      end
      if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.mult_ready_s) begin
        mult_completed = 1;
      end
      if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.mult_accept_s) begin
        mult_running = 0;
      end
      if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.mult_start_s) begin
        if (mult_running)
          $fatal(1, "* TESTCASE FAILED: overlapping MUL launches");
        if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_fau_i.i_MULTIPLIER.push_reg !== '0)
          $fatal(1, "* TESTCASE FAILED: MUL launch before pipeline drained");
        mult_running = 1;
      end
      if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mult_store_issue) begin
        if (!mult_store_pending || !mult_completed)
          $fatal(1, "* TESTCASE FAILED: MUL store accepted before actual completion");
      end
      if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_instr_s.opcode.mult_we) begin
        if (!mult_store_pending || !mult_completed)
          $fatal(1, "* TESTCASE FAILED: MUL store without completed issue");
        mult_store_pending = 0;
      end
    end
  end

  bit ladder_was_active = 0;
  int unsigned ladder_digits = 0;
  int unsigned ladder_muls = 0;
  int unsigned ladder_adds = 0;
  int unsigned ladder_overlaps = 0;

  always @(posedge clk) begin : ladder_accounting
    if (!ECC_in_agent_bus.ecc_rst_n || dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.zeroize) begin
      ladder_was_active = 0;
      ladder_digits = 0;
      ladder_muls = 0;
      ladder_adds = 0;
      ladder_overlaps = 0;
    end
    else begin
      if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mont_ladder) begin
        if (!ladder_was_active) begin
          ladder_digits = 0;
          ladder_muls = 0;
          ladder_adds = 0;
          ladder_overlaps = 0;
        end
        if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.req_digit)
          ladder_digits++;
        if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.instruction_issue) begin
          if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_instr_pipe2.opcode.mult_en)
            ladder_muls++;
          if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_instr_pipe2.opcode.add_en)
            ladder_adds++;
          if (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_instr_pipe2_addr ==
              ecc_pm_uop_pkg::PD_PA_S)
            ladder_overlaps++;
        end
      end
      else if (ladder_was_active &&
               (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.ecc_cmd_reg inside {
                 ecc_pm_uop_pkg::KEYGEN_CMD, ecc_pm_uop_pkg::SIGN_CMD,
                 ecc_pm_uop_pkg::DH_SHARED_CMD})) begin
        if (ladder_digits != 576 || ladder_muls != 27 * 576 ||
            ladder_adds != 56 * 576 || ladder_overlaps != 575)
          $fatal(1, "* TESTCASE FAILED: ladder accounting steps=%0d muls=%0d adds=%0d overlaps=%0d",
                 ladder_digits, ladder_muls, ladder_adds, ladder_overlaps);
        $display("ECC_LADDER_SUMMARY steps=%0d muls=%0d adds=%0d overlaps=%0d",
                 ladder_digits, ladder_muls, ladder_adds, ladder_overlaps);
      end
      ladder_was_active = dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mont_ladder;
    end
  end

  initial begin : shadow_trace
    int unsigned trace_cycles;
    trace_cycles = 160;
    if ($value$plusargs("ECC_SHADOW_TRACE_CYCLES=%d", trace_cycles)) begin
      if (trace_cycles == 0 || trace_cycles > 2048)
        $fatal(1, "* TESTCASE FAILED: ECC_SHADOW_TRACE_CYCLES must be 1..2048");
    end
    if ($test$plusargs("ECC_SHADOW_TRACE")) begin
      if ($test$plusargs("ECC_SHADOW_TRACE_LAST_PD")) begin
        wait (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_cntr ==
              ecc_pm_uop_pkg::PD_E - 8 &&
              dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mont_cntr == 0);
      end
      else begin
        wait (dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_cntr ==
              ecc_pm_uop_pkg::PA_S);
      end
      repeat (trace_cycles) begin
        @(negedge clk);
        $display("SHADOW_TRACE cycle=%0d pc=%0d p0=%h p1=%h p2=%h p2addr=%0d issue=%b out=%h start=%b ready=%b launch_pending=%b busy=%b pending=%b wait=%b req_digit=%b ladder=%b digit=%b mont=%0d wea=%b web=%b a=%0d b=%0d p0addr=%0d p1addr=%0d stall=%b stall1=%b stallcnt=%0d store_ready=%b",
          total_cycles,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_cntr,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_instr,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_instr_pipe1,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_instr_pipe2,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_instr_pipe2_addr,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.instruction_issue,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_instr_s,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.mult_start_s,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.mult_ready_s,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mult_launch_pending,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mult_busy,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mult_pending,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.pipeline_wait,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.req_digit_o,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mont_ladder,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.digit_i,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mont_cntr,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ram_tdp_file_i.wea,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ram_tdp_file_i.web,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.addra_mux_s,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.addrb_mux_s,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_instr_addr,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.prog_instr_pipe1_addr,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.stalled,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.stalled_pipe1,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.stall_cntr,
          dut.ecc_dsa_ctrl_i.ecc_arith_unit_i.ecc_pm_ctrl_i.mult_pipe_store_ready);
      end
    end
  end
  // pragma uvmf custom dut_instantiation end

  initial begin      // tbx vif_binding_block
    import uvm_pkg::uvm_config_db;
    // The monitor_bfm and driver_bfm for each interface is placed into the uvm_config_db.
    // They are placed into the uvm_config_db using the string names defined in the parameters package.
    // The string names are passed to the agent configurations by test_top through the top level configuration.
    // They are retrieved by the agents configuration class for use by the agent.
    uvm_config_db #( virtual ECC_in_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , ECC_in_agent_BFM , ECC_in_agent_mon_bfm );
    uvm_config_db #( virtual ECC_out_monitor_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , ECC_out_agent_BFM , ECC_out_agent_mon_bfm );
    uvm_config_db #( virtual ECC_in_driver_bfm  )::set( null , UVMF_VIRTUAL_INTERFACES , ECC_in_agent_BFM , ECC_in_agent_drv_bfm  );
  end

endmodule

// pragma uvmf custom external begin
// pragma uvmf custom external end
