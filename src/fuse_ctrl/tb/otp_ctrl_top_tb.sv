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


// -------------------------------------------------------------------------
// FUSE CTRL Testbench for basic/initial testing
// -------------------------------------------------------------------------

module otp_ctrl_top_tb 
    import axi_pkg::*;
    import caliptra_otp_ctrl_pkg::*;
    import caliptra_otp_ctrl_reg_pkg::*;
    import caliptra_otp_ctrl_part_pkg::*;
    import otp_ctrl_top_tb_pkg::*;
    (
        `ifdef VERILATOR
        input bit clk_tb
        `endif
    );

    //----------------------------------------------------------------
    // Internal constant and parameter definitions.
    //----------------------------------------------------------------
    parameter DEBUG = 0;

    parameter CLK_HALF_PERIOD = 2;

    parameter MemInitFile = "/home/ws/caliptra/anjpar/ws1/chipsalliance/caliptra-rtl/src/fuse_ctrl/data/otp-img.2048.vmem";

    //----------------------------------------------------------------
    // Register and Wire declarations.
    //----------------------------------------------------------------
    reg [31 : 0] cycle_ctr;
    reg [31 : 0] error_ctr;
    reg [31 : 0] tc_ctr;

    `ifndef VERILATOR
    reg           clk_tb;
    `endif
    reg           reset_n_tb;

    logic edn_clk;
    logic edn_rst_n;

    edn_pkg::edn_req_t     edn_o;
    edn_pkg::edn_rsp_t     edn_i;

    logic intr_otp_operation_done;
    logic intr_otp_error;

    caliptra_prim_alert_pkg::alert_rx_t [NumAlerts-1:0]  alert_rx_i;
    caliptra_prim_alert_pkg::alert_tx_t [NumAlerts-1:0]  alert_tx_o;
    // Observability to AST
    ast_pkg::ast_obs_ctrl_t                      obs_ctrl_i;
    logic [7:0]                                 otp_obs_o;
    // Macro-specific power sequencing signals to/from AST.
    otp_ast_req_t                               otp_ast_pwr_seq_o;
    otp_ast_rsp_t                               otp_ast_pwr_seq_h_i;
    // Power manager interface (inputs are synced to OTP clock domain)
    //pwrmgr_pkg::pwr_otp_req_t                   pwr_otp_i;
    logic                                       pwr_otp_init_i;
    pwrmgr_pkg::pwr_otp_rsp_t                   pwr_otp_o;
    // Macro-specific test registers going to lifecycle TAP
    lc_otp_vendor_test_req_t                    lc_otp_vendor_test_i;
    lc_otp_vendor_test_rsp_t                    lc_otp_vendor_test_o;
    // Lifecycle transition command interface
    lc_otp_program_req_t                        lc_otp_program_i;
    lc_otp_program_rsp_t                        lc_otp_program_o;
    // Lifecycle broadcast inputs
    // SEC_CM: LC_CTRL.INTERSIG.MUBI
    
    //lc_ctrl_pkg::lc_tx_t                        lc_creator_seed_sw_rw_en_i;
    //lc_ctrl_pkg::lc_tx_t                        lc_owner_seed_sw_rw_en_i;
    //lc_ctrl_pkg::lc_tx_t                        lc_seed_hw_rd_en_i;
    lc_ctrl_pkg::lc_tx_t                        lc_dft_en_i;
    lc_ctrl_pkg::lc_tx_t                        lc_escalate_en_i;
    lc_ctrl_pkg::lc_tx_t                        lc_check_byp_en_i;
    
    otp_lc_data_t                               otp_lc_data_o;
    otp_broadcast_t                             otp_broadcast_o;
    wire                                       otp_ext_voltage_h_io;
    logic                                       scan_en_i;
    logic                                       scan_rst_ni;
    caliptra_prim_mubi_pkg::mubi4_t             scanmode_i;
    logic [OtpTestVectWidth-1:0]                cio_test_o;
    logic [OtpTestVectWidth-1:0]                cio_test_en_o;

    localparam ADDR_WIDTH   = 32;
    localparam DATA_WIDTH   = 32;
    localparam USER_WIDTH   = 32;
    localparam ID_WIDTH     = 1;

    // Register offsets for core interface
    parameter int CoreAw = 13;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_INTR_STATE_OFFSET = 13'h 0;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_INTR_ENABLE_OFFSET = 13'h 4;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_INTR_TEST_OFFSET = 13'h 8;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ALERT_TEST_OFFSET = 13'h c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_STATUS_OFFSET = 13'h 10;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_0_OFFSET = 13'h 14;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_1_OFFSET = 13'h 18;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_2_OFFSET = 13'h 1c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_3_OFFSET = 13'h 20;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_4_OFFSET = 13'h 24;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_5_OFFSET = 13'h 28;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_6_OFFSET = 13'h 2c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_7_OFFSET = 13'h 30;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ERR_CODE_8_OFFSET = 13'h 34;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_REGWEN_OFFSET = 13'h 38;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_CMD_OFFSET = 13'h 3c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_ADDRESS_OFFSET = 13'h 40;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_WDATA_0_OFFSET = 13'h 44;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_WDATA_1_OFFSET = 13'h 48;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_RDATA_0_OFFSET = 13'h 4c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_DIRECT_ACCESS_RDATA_1_OFFSET = 13'h 50;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_CHECK_TRIGGER_REGWEN_OFFSET = 13'h 54;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_CHECK_TRIGGER_OFFSET = 13'h 58;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_CHECK_REGWEN_OFFSET = 13'h 5c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_CHECK_TIMEOUT_OFFSET = 13'h 60;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_INTEGRITY_CHECK_PERIOD_OFFSET = 13'h 64;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_CONSISTENCY_CHECK_PERIOD_OFFSET = 13'h 68;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_VENDOR_TEST_READ_LOCK_OFFSET = 13'h 6c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_READ_LOCK_OFFSET = 13'h 70;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_VENDOR_TEST_DIGEST_0_OFFSET = 13'h 74;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_VENDOR_TEST_DIGEST_1_OFFSET = 13'h 78;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_DIGEST_0_OFFSET = 13'h 7c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_NON_SECRET_FUSES_DIGEST_1_OFFSET = 13'h 80;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET0_DIGEST_0_OFFSET = 13'h 84;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET0_DIGEST_1_OFFSET = 13'h 88;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET1_DIGEST_0_OFFSET = 13'h 8c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET1_DIGEST_1_OFFSET = 13'h 90;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET2_DIGEST_0_OFFSET = 13'h 94;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET2_DIGEST_1_OFFSET = 13'h 98;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET3_DIGEST_0_OFFSET = 13'h 9c;
    parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_SECRET3_DIGEST_1_OFFSET = 13'h a0;

    // AXI Core Interface
    axi_if #(
        .AW (ADDR_WIDTH),
        .DW (DATA_WIDTH),
        .IW (ID_WIDTH),
        .UW (USER_WIDTH)
    ) axi_core_if (
        .clk    (clk_tb),
        .rst_n  (reset_n_tb)
    );

    // AXI Prim Interface
    axi_if #(
        .AW (ADDR_WIDTH),
        .DW (DATA_WIDTH),
        .IW (ID_WIDTH),
        .UW (USER_WIDTH)
    ) axi_prim_if (
        .clk    (clk_tb),
        .rst_n  (reset_n_tb)
    );

    // AXI Secret Reg Interface
    axi_if #(
        .AW (ADDR_WIDTH),
        .DW (DATA_WIDTH),
        .IW (ID_WIDTH),
        .UW (USER_WIDTH)
    ) axi_secreg_if (
        .clk    (clk_tb),
        .rst_n  (reset_n_tb)
    );

      // dut
    otp_ctrl_top #(
        .MemInitFile        (MemInitFile)    
    ) dut (
        .clk_i                      (clk_tb     ),
        .rst_ni                     (reset_n_tb ),
        // edn
        .clk_edn_i                  (edn_clk    ),
        .rst_edn_ni                 (edn_rst_n  ),
        .edn_o                      (edn_o), //(edn_if[0].req ),
        .edn_i                      (edn_i), //({edn_if[0].ack, edn_if[0].d_data}),
        // AXI interface
        .s_core_axi_r_if            (axi_core_if.r_sub),
        .s_core_axi_w_if            (axi_core_if.w_sub),
        .s_prim_axi_r_if            (axi_prim_if.r_sub),
        .s_prim_axi_w_if            (axi_prim_if.w_sub),
        .s_secreg_axi_r_if          (axi_secreg_if.r_sub),
        // interrupt
        .intr_otp_operation_done_o  (intr_otp_operation_done),
        .intr_otp_error_o           (intr_otp_error),
        // alert
        .alert_rx_i                 (alert_rx_i  ), //(alert_rx      parameter logic [CoreAw-1:0] CALIPTRA_OTP_CTRL_ALERT_TEST_OFFSET = 13'h c;
        .alert_tx_o                 (alert_tx_o ), //(alert_tx   ),
        // ast
        .obs_ctrl_i                 (obs_ctrl_i), //(otp_ctrl_if.obs_ctrl_i),
        .otp_obs_o                  (otp_obs_o), 
        .otp_ast_pwr_seq_o          (otp_ast_pwr_seq_o), //(ast_req),
        .otp_ast_pwr_seq_h_i        (otp_ast_pwr_seq_h_i), //(otp_ctrl_if.otp_ast_pwr_seq_h_i),
        // pwrmgr
        .pwr_otp_i                  (pwr_otp_init_i), //(otp_ctrl_if.pwr_otp_init_i),
        .pwr_otp_o                  (pwr_otp_o), //({otp_ctrl_if.pwr_otp_done_o, otp_ctrl_if.pwr_otp_idle_o}),
        // lc
        .lc_otp_vendor_test_i       (lc_otp_vendor_test_i), //(otp_ctrl_if.otp_vendor_test_ctrl_i),
        .lc_otp_vendor_test_o		(lc_otp_vendor_test_o), //(otp_ctrl_if.otp_vendor_test_status_o),
        .lc_otp_program_i		    (lc_otp_program_i), //({lc_prog_if.req, lc_prog_if.h_data}),
        .lc_otp_program_o		    (lc_otp_program_o), //({lc_prog_if.d_data, lc_prog_if.ack}),
        //.lc_creator_seed_sw_rw_en_i	(lc_creator_seed_sw_rw_en_i), //(otp_ctrl_if.lc_creator_seed_sw_rw_en_i),
        //.lc_owner_seed_sw_rw_en_i	(lc_owner_seed_sw_rw_en_i), //(otp_ctrl_if.lc_owner_seed_sw_rw_en_i),
        //.lc_seed_hw_rd_en_i		    (lc_seed_hw_rd_en_i), //(otp_ctrl_if.lc_seed_hw_rd_en_i),
        .lc_dft_en_i		        (lc_dft_en_i), //(otp_ctrl_if.lc_dft_en_i),
        .lc_escalate_en_i		    (lc_escalate_en_i), //(otp_ctrl_if.lc_escalate_en_i),
        .lc_check_byp_en_i		    (lc_check_byp_en_i), //(otp_ctrl_if.lc_check_byp_en_i),
        .otp_lc_data_o		        (otp_lc_data_o), //(otp_ctrl_if.lc_data_o),
        

        .otp_broadcast_o            (otp_broadcast_o), //(otp_ctrl_if.otp_broadcast_o),
        .otp_ext_voltage_h_io       (otp_ext_voltage_h_io),

        //scan
        .scan_en_i                  (scan_en_i), //(otp_ctrl_if.scan_en_i),
        .scan_rst_ni                (scan_rst_ni), //(otp_ctrl_if.scan_rst_ni),
        .scanmode_i                 (scanmode_i), //(otp_ctrl_if.scanmode_i),

        // Test-related GPIO output
        .cio_test_o                 (cio_test_o), //(otp_ctrl_if.cio_test_o),
        .cio_test_en_o              (cio_test_en_o) //(otp_ctrl_if.cio_test_en_o)
    );

    //----------------------------------------------------------------
    // clk_gen
    //
    // Clock generator process.
    //----------------------------------------------------------------
    `ifndef VERILATOR
        always
        begin : clk_gen
            #CLK_HALF_PERIOD
            clk_tb = !clk_tb;
        end // clk_gen
    `endif

    //----------------------------------------------------------------
    // sys_monitor
    //
    // Generates a cycle counter and displays information about
    // the dut as needed.
    //----------------------------------------------------------------
    always @(posedge clk_tb) begin : sys_monitor
        cycle_ctr = (!reset_n_tb) ? 32'h0 : cycle_ctr + 1;
    end

    //----------------------------------------------------------------
    // reset_dut()
    //
    // Toggles reset to force the DUT into a well defined state.
    //----------------------------------------------------------------
    task reset_dut;
        begin
            $display("*** Toggle reset.");
            reset_n_tb = 0;
            
            repeat (2) @(posedge clk_tb);
            reset_n_tb = 1;
            
            repeat (2) @(posedge clk_tb);
            
            $display("");
        end
    endtask // reset_dut

    //----------------------------------------------------------------
    // init_sim()
    //
    // Initialize all counters and testbed functionality as well
    // as setting the DUT inputs to defined values.
    //----------------------------------------------------------------
    task init_sim;
        begin
    `ifndef VERILATOR
            clk_tb          = 0;
    `endif
            reset_n_tb          = 1;

            axi_core_if.araddr  = '0;
            axi_core_if.arburst  = '0;
            axi_core_if.arlen    = '0;
            axi_core_if.arlock   = 0;
            axi_core_if.arsize   = '0;
            axi_core_if.arid     = 0;   
            axi_core_if.aruser   = '0;
            axi_core_if.arvalid  = 0;
            axi_core_if.rready   = 0;

            axi_core_if.awaddr   = '0;
            axi_core_if.awid     = '0;
            axi_core_if.awburst  = '0;
            axi_core_if.awlen    = '0;
            axi_core_if.awlock   = 0;
            axi_core_if.awsize   = '0;
            axi_core_if.awuser   = '0;
            axi_core_if.awvalid  = 0;
            axi_core_if.wdata    = '0;
            axi_core_if.wvalid   = 0;
            axi_core_if.wlast    = 0;
            axi_core_if.wstrb    = '0;
            axi_core_if.bready   = 0;

            axi_prim_if.araddr   = '0;
            axi_prim_if.arburst  = '0;
            axi_prim_if.arlen    = '0;
            axi_prim_if.arlock   = 0;
            axi_prim_if.arsize   = '0;
            axi_prim_if.arid     = 0;
            axi_prim_if.aruser   = '0;
            axi_prim_if.arvalid  = 0;
            axi_prim_if.rready   = 0;

            axi_prim_if.awaddr   = '0;
            axi_prim_if.awid     = '0;
            axi_prim_if.awburst  = '0;
            axi_prim_if.awlen    = '0;
            axi_prim_if.awlock   = 0;
            axi_prim_if.awsize   = '0;
            axi_prim_if.awuser   = '0;
            axi_prim_if.awvalid  = 0;
            axi_prim_if.wdata    = '0;
            axi_prim_if.wvalid   = 0;
            axi_prim_if.wlast    = 0;
            axi_prim_if.wstrb    = '0;
            axi_prim_if.bready   = 0;

            axi_secreg_if.araddr  = '0;
            axi_secreg_if.arburst = '0;
            axi_secreg_if.arlen   = '0;
            axi_secreg_if.arlock  = 0;
            axi_secreg_if.arsize  = '0;
            axi_secreg_if.aruser  = '0;
            axi_secreg_if.arvalid = 0;
            axi_secreg_if.rready  = 0;    

            //lc_creator_seed_sw_rw_en_i  = lc_ctrl_pkg::Off;;
            //lc_owner_seed_sw_rw_en_i    = lc_ctrl_pkg::Off;;
            //lc_seed_hw_rd_en_i          = lc_ctrl_pkg::Off;;
            lc_dft_en_i                 = lc_ctrl_pkg::Off;;
            lc_escalate_en_i            = lc_ctrl_pkg::Off;;
            lc_check_byp_en_i           = lc_ctrl_pkg::Off;;

            pwr_otp_init_i              = 0;
        end
    endtask

    //----------------------------------------------------------------
    // display_test_result()
    //
    // Display the accumulated test results.
    //----------------------------------------------------------------
    task display_test_result;
        begin
            if (error_ctr == 0) begin
                $display("*** All %02d test cases completed successfully.", tc_ctr);
                $display("* TESTCASE PASSED");
            end
            else begin
                $display("*** %02d test cases completed.", tc_ctr);
                $display("*** %02d errors detected during testing.", error_ctr);
                $display("* TESTCASE FAILED");
            end
        end
    endtask // display_test_result

    //-----------------------------------------------------------------
    // init_parition()
    //
    // Initialize partitions and wait for initialization complete.
    //-----------------------------------------------------------------
    task init_partition;
        begin
            $display("*** TEST: Initialize OTP partitions.");
            pwr_otp_init_i      = 1;
            repeat (5) @(posedge clk_tb);
            pwr_otp_init_i      = 0;

            while (!otp_lc_data_o.valid) begin
                @(posedge clk_tb);
            end

            $display("*** TEST PASS - OTP partition initialization complete");
        end
    endtask

    //-----------------------------------------------------------------
    // read_csr()
    //
    // Read a CSR over AXI interface (via AXI2TLUL gasket).
    //-----------------------------------------------------------------
    task read_csr (
        input string            csr_name,
        input logic [12:0]      csr_addr,
        input logic [31:0]      user,
        input logic             id
    );
        begin
            logic [31:0]        read_addr;
            logic [31:0]        read_data;
            axi_pkg::axi_resp_e read_rsp;

            $display("*** Read CSR %s", csr_name); 

            read_addr   = {{19{1'b0}}, csr_addr};
            //user        = 32'h00000001;
            //id          = 1'b1;
            $display(" DEBUG: read_addr = 0x%x", read_addr);
            axi_core_if.axi_read_single(read_addr, user, id, clk_tb, read_data, read_rsp);
            $display("DEBUG: Issued axi read command");
            @(posedge clk_tb);
            if (read_rsp == axi_pkg::AXI_RESP_OKAY) begin
                $display(" *** TEST PASS: CSR %s = 0x%x\n", csr_name, read_data);
            end
            else begin
                $display(" TEST FAIL: Failed to read CSR %s. Read Response = %s", csr_name, read_rsp);
            end
        end
    endtask

    //-----------------------------------------------------------------
    // read_all_csrs()
    //
    // Read all CSRs back to back CSRs over AXI interface (via AXI2TLUL gasket).
    //-----------------------------------------------------------------
    task read_all_csrs;
        begin
            logic [CoreAw-1:0]  csr_addr;
            string              csr_reg_name;
            logic [31:0]        user;
            logic               id;

            user    = 32'h00000001;
            id      = 1'b1;

            $display("*** \n\nTEST: Read all CSRs");

            foreach (csr_registers[i]) begin
                csr_reg_name    = csr_registers[i];
                csr_addr        = get_addr(csr_reg_name);
                read_csr(csr_reg_name, csr_addr, user, id);
            end

            $display("*** TEST Read all CSRs compelete!!");
        end
    endtask

    //----------------------------------------------------------------
    // write_csr()
    //
    // Write a CSR over AXI itnerface (via AXI2TLUL gasket)
    //----------------------------------------------------------------
    task write_csr(
        input string            csr_name,
        input logic [12:0]      csr_addr,
        input logic [31:0]      csr_write_data,
        input logic [31:0]      user,
        input logic             id
    );
        begin
            logic [31:0] write_addr;
            logic [31:0] read_data;
            axi_pkg::axi_resp_e write_rsp;
            axi_pkg::axi_resp_e read_rsp;
            write_addr = {{19{1'b0}}, csr_addr};
            $display(" DEBUG: write_addr = 0x%x", write_addr);
            axi_core_if.axi_write_single(write_addr, user, id, clk_tb, csr_write_data, write_rsp);
            @(posedge clk_tb);
            if (write_rsp != AXI_RESP_OKAY) begin
                $display("*** FAIL: Write to CSR %s (addr 0x%x) unsuccessful. Response = %s", csr_name, write_addr, write_rsp);
            end
            read_csr(csr_name, write_addr, user, id);
        end
    endtask
    
    //----------------------------------------------------------------
    //  write_all_csrs()
    // 
    // Write all CSRs back to back over AXI interface (via AXI2TLUL gasket)
    //----------------------------------------------------------------
    task write_all_csrs;
        begin
            logic [CoreAw-1:0]  csr_addr;
            string              csr_reg_name;
            logic [31:0]        csr_write_data;
            logic [31:0]        user;
            logic               id;

            user    = 32'h00000001;
            id      = 1'b1;

            $display("*** \n\nTEST: Write all CSRs");

            foreach (csr_registers[i]) begin
                csr_reg_name    = csr_registers[i];
                csr_addr        = get_addr(csr_reg_name);
                csr_write_data  = $random;
                write_csr(csr_reg_name, csr_addr, csr_write_data, user, id);
            end

            $display("*** TEST Write all CSRs compelete!!");
        end
    endtask

    //----------------------------------------------------------------
    //  write_dai_regs()
    // 
    // Write DAI registers over AXI interface (via AXI2TLUL gasket)
    //----------------------------------------------------------------
    task write_dai_regs;
        begin
            logic [CoreAw-1:0]  csr_addr;
            string              cur_dai_reg;
            logic [31:0]        user;
            logic               id;
            logic [31:0]        write_data;
            strq_t              dai_regs;
            axi_resp_e          write_rsp;
            $display("*** TEST: Write to DAI registers");

            dai_regs = get_dai_regnames();

            // Write to DAI WDATA_0 register
            foreach (dai_regs[i]) begin
                cur_dai_reg = dai_regs[i];
                if (str_find(cur_dai_reg, "WDATA_0")) 
                    break;
            end
            csr_addr    = get_addr(cur_dai_reg);
            write_data  = 32'h11223344; // reset value is 0x1; Write 0 to clear
            user        = 32'h1;
            id          = 1'b1;
            write_csr(cur_dai_reg, csr_addr, write_data, user, id);

        end
    endtask


    //----------------------------------------------------------------
    // The main test functionality.
    //----------------------------------------------------------------
        initial begin : main
            fork
                begin
                    $display("      -- Testbench for fuse_ctrl started. --");

                    init_sim();
                    reset_dut();

                    init_partition();
                    read_all_csrs();
                    write_all_csrs();
                    //write_dai_regs();

                    $display("      -- Testbench for fuse_ctrl done. --");
                    $finish;
                end

                begin
                    repeat (100000) @(posedge clk_tb);
                    $display("*** Test timed out!!!");
                    $finish;
                end
            join_any
            disable fork;
        end

endmodule // otp_ctrl_top_tb

//======================================================================
// EOF otp_ctrl_top_tb.sv
//======================================================================


