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
`default_nettype none

`include "common_defines.sv"
`include "config_defines.svh"
`include "caliptra_reg_defines.svh"
`include "caliptra_macros.svh"

`ifndef VERILATOR
module caliptra_top_tb;
`else
module caliptra_top_tb (
    input bit core_clk,
    input bit rst_l
    );
`endif

    import soc_ifc_pkg::*;
    import caliptra_top_tb_pkg::*;

`ifndef VERILATOR
    // Time formatting for %t in display tasks
    // -9 = ns units
    // 3  = 3 bits of precision (to the ps)
    // "ns" = nanosecond suffix for output time values
    // 15 = 15 bits minimum field width
    initial $timeformat(-9, 3, " ns", 15); // up to 99ms representable in this width
`endif

`ifndef VERILATOR
    bit                         core_clk;
`endif

    int                         cycleCnt;
    int                         cycleCnt_Flag = '0;


    logic                       cptra_pwrgood;
    logic                       cptra_rst_b;
    logic                       BootFSM_BrkPoint;
    logic                       scan_mode;

    logic [`CLP_OBF_KEY_DWORDS-1:0][31:0]          cptra_obf_key;
    logic [0:`CLP_OBF_KEY_DWORDS-1][31:0]          cptra_obf_key_uds, cptra_obf_key_fe;
    
    // logic [11:0][31:0]          cptra_uds_tb;
    // logic [7:0][31:0]           cptra_fe_tb;
    logic [0:`CLP_OBF_UDS_DWORDS-1][31:0]          cptra_uds_tb;
    logic [0:`CLP_OBF_FE_DWORDS-1][31:0]           cptra_fe_tb;

    // logic [11:0][31:0]          cptra_uds_rand;
    // logic [7:0][31:0]           cptra_fe_rand;
    logic [0:`CLP_OBF_UDS_DWORDS-1][31:0]          cptra_uds_rand;
    logic [0:`CLP_OBF_FE_DWORDS-1][31:0]           cptra_fe_rand;
    logic [0:`CLP_OBF_KEY_DWORDS-1][31:0]          cptra_obf_key_tb;

    logic                       start_apb_fuse_sequence;

    enum logic [5:0] {
        S_APB_IDLE,
        S_APB_WR_UDS,
        S_APB_WR_FE,
        S_APB_WR_FUSE_DONE,
        S_APB_POLL_FLOW_ST,
        S_APB_WR_BOOT_GO,
        S_APB_WAIT_FW_TEST,
        S_APB_POLL_LOCK,
        S_APB_PRE_WR_CMD,
        S_APB_WR_CMD,
        S_APB_WR_DLEN,
        S_APB_WR_DATAIN,
        S_APB_WR_STATUS,
        S_APB_WR_EXEC,
        S_APB_WAIT_ERROR_AXS,
        S_APB_RD_HW_ERROR_FATAL,
        S_APB_WR_HW_ERROR_FATAL,
        S_APB_RD_HW_ERROR_NON_FATAL,
        S_APB_WR_HW_ERROR_NON_FATAL,
        S_APB_DONE,
        S_APB_RD_DLEN,
        S_APB_RD_DATAOUT,
        S_APB_RST_EXEC,
        S_APB_ERROR
    } n_state_apb, c_state_apb;

    parameter FW_NUM_DWORDS         = 256;

    logic [$clog2(FW_NUM_DWORDS)-1:0] apb_wr_count, apb_wr_count_nxt;
    logic [31:0] apb_rd_count, apb_rd_count_nxt, dlen;
    logic apb_enable_ph;
    logic apb_xfer_end;
    logic execute_mbox_rx_protocol;

    //jtag interface
    logic                       jtag_tck;    // JTAG clk
    logic                       jtag_tms;    // JTAG TMS
    logic                       jtag_tdi;    // JTAG tdi
    logic                       jtag_trst_n; // JTAG Reset
    logic                       jtag_tdo;    // JTAG TDO
    //APB Interface
    logic [`CALIPTRA_APB_ADDR_WIDTH-1:0] PADDR;
    logic [2:0]                          PPROT;
    logic                                PSEL;
    logic                                PENABLE;
    logic                                PWRITE;
    logic [`CALIPTRA_APB_DATA_WIDTH-1:0] PWDATA;
    logic [`CALIPTRA_APB_USER_WIDTH-1:0] PAUSER;

    logic                                PREADY;
    logic                                PSLVERR;
    logic [`CALIPTRA_APB_DATA_WIDTH-1:0] PRDATA;

    // QSPI Interface
    logic                                qspi_clk;
    logic [`CALIPTRA_QSPI_CS_WIDTH-1:0]  qspi_cs_n;
    wire  [`CALIPTRA_QSPI_IO_WIDTH-1:0]  qspi_data;
    logic [`CALIPTRA_QSPI_IO_WIDTH-1:0]  qspi_data_host_to_device, qspi_data_device_to_host;
    logic [`CALIPTRA_QSPI_IO_WIDTH-1:0]  qspi_data_host_to_device_en;

`ifdef CALIPTRA_INTERNAL_UART
    logic uart_loopback;
`endif

    logic ready_for_fuses;
    logic ready_for_fw_push;
    logic mailbox_data_avail;
    logic status_set;
    logic mbox_sram_cs;
    logic mbox_sram_we;
    logic [14:0] mbox_sram_addr;
    logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_wdata;
    logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_rdata;

    logic imem_cs;
    logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] imem_addr;
    logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] imem_rdata;

    //device lifecycle
    security_state_t security_state;

    ras_test_ctrl_t ras_test_ctrl;
    logic [63:0] generic_input_wires;
    logic        etrng_req;
    logic  [3:0] itrng_data;
    logic        itrng_valid;

    logic cptra_error_fatal;
    logic cptra_error_non_fatal;
    logic [15:0] cptra_error_fatal_counter;
    logic [15:0] cptra_error_non_fatal_counter;
    logic cptra_error_fatal_dly_p;
    logic cptra_error_non_fatal_dly_p;

    logic mbox_apb_dataout_read_ooo;
    logic mbox_ooo_read_done;
    logic mbox_apb_dataout_read_no_lock;
    logic mbox_no_lock_read_done;

    logic [`CALIPTRA_APB_DATA_WIDTH-1:0] soc_ifc_hw_error_wdata;

    //Interrupt flags
    //logic nmi_int;
    //logic soft_int;
    //logic timer_int;
    logic int_flag;
    logic cycleCnt_smpl_en;
    int cycleCnt_ff;

    //Reset flags
    logic assert_hard_rst_flag;
    logic deassert_hard_rst_flag;
    logic assert_rst_flag_from_service;
    logic assert_rst_flag_from_fatal;
    logic assert_rst_flag;
    logic deassert_rst_flag_from_service;
    int   count_deassert_rst_flag_from_fatal;
    logic deassert_rst_flag_from_fatal;
    logic deassert_rst_flag;

    el2_mem_if el2_mem_export ();

    logic [FW_NUM_DWORDS-1:0][31:0] fw_blob;

`ifndef VERILATOR
    always
    begin : clk_gen
      core_clk = #5ns ~core_clk;
    end // clk_gen
`endif
    
    always@(negedge core_clk) begin
        if(!cptra_rst_b) cycleCnt_ff <= 'h0;
        else if(cycleCnt_smpl_en) cycleCnt_ff <= cycleCnt;
    end

    always@(negedge core_clk) begin
        if((cycleCnt == cycleCnt_ff + 2000) && int_flag) begin
            force caliptra_top_dut.soft_int = 'b1;
        end
        
        else if((cycleCnt == cycleCnt_ff + 7000) && int_flag) begin
            force caliptra_top_dut.timer_int = 'b1;
        end
        
        else if((c_state_apb == S_APB_WR_EXEC) && apb_xfer_end && int_flag) begin
            //Wait for APB flow to be done before toggling generic_input_wires
            generic_input_wires <= {$urandom, $urandom}; //Toggle wires
        end
        
        else if((cycleCnt == cycleCnt_ff + 15000) && int_flag) begin
            force caliptra_top_dut.soft_int = 'b1;
        end
        
        else if (!ras_test_ctrl.error_injection_seen) begin
            release caliptra_top_dut.soft_int;
            release caliptra_top_dut.timer_int;
            generic_input_wires <= 'h0;
        end

        else if (ras_test_ctrl.reset_generic_input_wires) begin
            generic_input_wires <= {32'h0, ERROR_NONE_SET};
        end

        else if (c_state_apb == S_APB_RD_HW_ERROR_FATAL && apb_xfer_end) begin
            if (PRDATA[`SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_LOW]) begin
                generic_input_wires <= {32'h0, ICCM_FATAL_OBSERVED};
            end
            else if (PRDATA[`SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_LOW]) begin
                generic_input_wires <= {32'h0, DCCM_FATAL_OBSERVED};
            end
            else if (PRDATA[`SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_LOW]) begin
                generic_input_wires <= {32'h0, NMI_FATAL_OBSERVED};
            end
            else begin
                generic_input_wires <= {32'h0, ERROR_NONE_SET};
            end
        end

        else if (c_state_apb == S_APB_RD_HW_ERROR_NON_FATAL && apb_xfer_end) begin
            if (PRDATA[`SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_LOW]) begin
                generic_input_wires <= {32'h0, PROT_NO_LOCK_NON_FATAL_OBSERVED};
            end
            else if (PRDATA[`SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_LOW]) begin
                generic_input_wires <= {32'h0, PROT_OOO_NON_FATAL_OBSERVED};
            end
            else if (PRDATA[`SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_LOW]) begin
                generic_input_wires <= {32'h0, MBOX_NON_FATAL_OBSERVED};
            end
            else begin
                generic_input_wires <= {32'h0, ERROR_NONE_SET};
            end
        end

    end

    always@(negedge core_clk or negedge cptra_pwrgood) begin
        // This persists across soft reset
        if (!cptra_pwrgood) begin
            soc_ifc_hw_error_wdata <= '0;
        end
        else if (c_state_apb inside {S_APB_RD_HW_ERROR_FATAL, S_APB_RD_HW_ERROR_NON_FATAL} && apb_xfer_end) begin
            // HW ERROR registers are W1C, capture the set bits
            soc_ifc_hw_error_wdata <= PRDATA;
        end
        else if (c_state_apb inside {S_APB_WR_HW_ERROR_FATAL, S_APB_WR_HW_ERROR_NON_FATAL} && apb_xfer_end) begin
            // Clear after completing the write
            soc_ifc_hw_error_wdata <= 0;
        end
    end

    always@(negedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            cptra_error_fatal_counter     <= 16'h0;
            cptra_error_non_fatal_counter <= 16'h0;
        end
        else begin
            cptra_error_fatal_counter     <= cptra_error_fatal     ? (cptra_error_fatal_counter     + 16'h1) : 16'h0;
            cptra_error_non_fatal_counter <= cptra_error_non_fatal ? (cptra_error_non_fatal_counter + 16'h1) : 16'h0;
        end
    end
    // Pulse fires about 640ns after the original error interrupt occurs
    always_comb cptra_error_fatal_dly_p     = cptra_error_fatal_counter     == 16'h0040;
    always_comb cptra_error_non_fatal_dly_p = cptra_error_non_fatal_counter == 16'h0040;

    always_comb assert_rst_flag_from_fatal = c_state_apb == S_APB_ERROR;
    always@(negedge core_clk) begin
        if (!cptra_pwrgood) begin
            count_deassert_rst_flag_from_fatal <= 0;
        end
        // Start counting after the fatal flag asserts reset, and continue
        // counting until the reset is deasserted
        else if (assert_rst_flag_from_fatal || (!cptra_rst_b && |count_deassert_rst_flag_from_fatal)) begin
            count_deassert_rst_flag_from_fatal <= count_deassert_rst_flag_from_fatal + 1;
        end
        else begin
            count_deassert_rst_flag_from_fatal <= 0;
        end
    end
    // Leave reset asserted for 32 clock cycles
    always_comb deassert_rst_flag_from_fatal = count_deassert_rst_flag_from_fatal == 31;

    assert property (@(posedge core_clk) c_state_apb == S_APB_WR_FUSE_DONE |-> !cptra_error_non_fatal) else begin
        $error("cptra_error_non_fatal observed during boot up");
        $finish;
    end
    assert property (@(posedge core_clk) c_state_apb == S_APB_WR_FUSE_DONE |-> !cptra_error_fatal) else begin
        $error("cptra_error_fatal observed during boot up");
        $finish;
    end

    always@(negedge core_clk or negedge cptra_rst_b) begin
        if(!cptra_rst_b) begin
            mbox_apb_dataout_read_ooo <= 1'b0;
        end
        else if(ras_test_ctrl.do_ooo_access) begin
            mbox_apb_dataout_read_ooo <= 1'b1;
        end
        else if (mbox_apb_dataout_read_ooo && (c_state_apb == S_APB_RD_DATAOUT) && (apb_rd_count == dlen)) begin
            mbox_apb_dataout_read_ooo <= 1'b0;
        end
    end

    always@(negedge core_clk or negedge cptra_rst_b) begin
        if(!cptra_rst_b) begin
            mbox_apb_dataout_read_no_lock <= 1'b0;
        end
        else if(ras_test_ctrl.do_no_lock_access) begin
            mbox_apb_dataout_read_no_lock <= 1'b1;
        end
        else if (mbox_apb_dataout_read_no_lock && (c_state_apb == S_APB_RD_DATAOUT) && (apb_rd_count == dlen)) begin
            mbox_apb_dataout_read_no_lock <= 1'b0;
        end
    end

    always@(negedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            mbox_ooo_read_done <= 1'b0;
        end
        else if (mbox_apb_dataout_read_ooo && (c_state_apb == S_APB_RD_DATAOUT) && (apb_rd_count == dlen)) begin
            mbox_ooo_read_done <= 1'b1;
        end
        else if (c_state_apb == S_APB_WR_HW_ERROR_NON_FATAL)
            mbox_ooo_read_done <= 1'b0;
        else if (ras_test_ctrl.reset_ooo_done_flag)
            mbox_ooo_read_done <= 1'b0;
    end

    always@(negedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            mbox_no_lock_read_done <= 1'b0;
        end
        else if (mbox_apb_dataout_read_no_lock && (c_state_apb == S_APB_RD_DATAOUT) && (apb_rd_count == dlen)) begin
            mbox_no_lock_read_done <= 1'b1;
        end
        else if (c_state_apb == S_APB_WR_HW_ERROR_NON_FATAL)
            mbox_no_lock_read_done <= 1'b0;
        else if (ras_test_ctrl.reset_no_lock_done_flag)
            mbox_no_lock_read_done <= 1'b0;
    end

    always@(negedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            execute_mbox_rx_protocol <= 'b0;
        end
        else if (c_state_apb == S_APB_WR_EXEC) begin
            execute_mbox_rx_protocol <= 'b1;
        end
        else if (execute_mbox_rx_protocol && ((c_state_apb == S_APB_RST_EXEC) && apb_xfer_end)) begin
            execute_mbox_rx_protocol <= 'b0;
        end
    end

    initial begin
        cptra_pwrgood = 1'b0;
        BootFSM_BrkPoint = 1'b1; //Set to 1 even before anything starts
        cptra_rst_b = 1'b0;
        start_apb_fuse_sequence = 1'b0;
        //TIE-OFF
        PPROT = '0;

`ifndef VERILATOR
        if($test$plusargs("dumpon")) $dumpvars;
`endif

        if($test$plusargs("RAND_DOE_VALUES")) begin
            //cptra_obf_key = cptra_obf_key_tb;
            for (int dword = 0; dword < $bits(cptra_obf_key/32); dword++) begin
                cptra_obf_key[dword] = cptra_obf_key_tb[dword];
            end

            cptra_uds_tb = cptra_uds_rand;
            cptra_fe_tb = cptra_fe_rand;
        end
        else begin
            //Key for UDS
            cptra_obf_key_uds = 256'h54682728db5035eb04b79645c64a95606abb6ba392b6633d79173c027c5acf77;
            cptra_uds_tb = 384'he4046d05385ab789c6a72866e08350f93f583e2a005ca0faecc32b5cfc323d461c76c107307654db5566a5bd693e227c;

            //Key for FE
            cptra_obf_key_fe = 256'h31358e8af34d6ac31c958bbd5c8fb33c334714bffb41700d28b07f11cfe891e7;
            cptra_fe_tb = 256'hb32e2b171b63827034ebb0d1909f7ef1d51c5f82c1bb9bc26bc4ac4dccdee835;
                           /*256'h7dca6154c2510ae1c87b1b422b02b621bb06cac280023894fcff3406af08ee9b,
                           256'he1dd72419beccddff77c722d992cdcc87e9c7486f56ab406ea608d8c6aeb060c,
                           256'h64cf2785ad1a159147567e39e303370da445247526d95942bf4d7e88057178b0};*/

            //swizzle the key so it matches the endianness of AES block
            //used for visual inspection of uds/fe flow, manually switching keys and checking both
            for (int dword = 0; dword < $bits(cptra_obf_key/32); dword++) begin
                //cptra_obf_key[dword] = cptra_obf_key_uds[dword];
                cptra_obf_key[dword] = cptra_obf_key_fe[dword];
            end
        end
        
    end

    assign assert_rst_flag   =   assert_rst_flag_from_service ||   assert_rst_flag_from_fatal;
    assign deassert_rst_flag = deassert_rst_flag_from_service || deassert_rst_flag_from_fatal;
    always @(posedge core_clk) begin
        //Reset/pwrgood assertion during runtime
        if (cycleCnt == 15 || deassert_hard_rst_flag) begin
            $display ("\n\n\n\n\n\n");
            $display ("SoC: Asserting cptra_pwrgood and breakpoint\n");
            //assert power good
            cptra_pwrgood <= 1'b1;
            //BootFSM_BrkPoint <= 1'b1;
        end
        else if (cycleCnt == 20 || deassert_rst_flag) begin
            $display ("SoC: De-Asserting cptra_rst_b\n");
            //de-assert reset
            cptra_rst_b <= 1'b1;
        end
        else if (assert_hard_rst_flag) begin
            cptra_pwrgood <= 'b0;
            cptra_rst_b <= 'b0;
            start_apb_fuse_sequence <= 1'b0;
        end
        else if (assert_rst_flag) begin
            cptra_rst_b <= 'b0;
            start_apb_fuse_sequence <= 1'b0;
        end
        //wait for fuse indication
        else if (ready_for_fuses == 1'b0) begin
            //nop
            cycleCnt_Flag <= cycleCnt;
        end
        else if (cycleCnt == cycleCnt_Flag + 5) begin
            start_apb_fuse_sequence <= 1'b1;
        end
    end

    always@(negedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            dlen <= '0;
        end
        else if ((c_state_apb == S_APB_RD_DLEN) && apb_xfer_end) begin
            dlen <= PRDATA;
        end
    end

    always@(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            c_state_apb  <= S_APB_IDLE;
            apb_wr_count <= '0;
            apb_rd_count <= '0;
            apb_enable_ph <= 0;
        end
        else begin
            c_state_apb  <= n_state_apb;
            apb_wr_count <= apb_wr_count_nxt;
            apb_rd_count <= apb_rd_count_nxt;
            //next phase is an access phase if this is setup phase OR it's access and responder isn't ready
            apb_enable_ph <= (PSEL & ~PENABLE) | (PSEL & PENABLE & ~PREADY);
        end
        if (c_state_apb != n_state_apb) begin
            case (n_state_apb)
                S_APB_WR_UDS: begin
                    $display ("CLP: Ready for fuse download\n");
                    $display ("SoC: Writing obfuscated UDS to fuse bank\n");
                end
                S_APB_WR_FE: begin
                    $display ("SoC: Writing obfuscated Field Entropy to fuse bank\n");
                end
                S_APB_WR_FUSE_DONE: begin
                    $display ("SoC: Writing fuse done register\n");
                end
                S_APB_POLL_FLOW_ST: begin
                    $display ("SoC: Polling Flow Status\n");
                end
                S_APB_WR_BOOT_GO: begin
                    $display ("SoC: Writing BootGo register\n");
                end
                S_APB_WAIT_FW_TEST: begin
                    $display ("CLP: ROM Flow in progress...\n");
                end
                S_APB_POLL_LOCK: begin
                    $display ("CLP: Ready for firmware push\n");
                    $display ("SoC: Requesting mailbox lock\n");
                end
                S_APB_PRE_WR_CMD: begin
                    $display ("SoC: Lock granted\n");
                end
                S_APB_WR_CMD: begin
                    $display ("SoC: Writing the Command Register\n");
                end
                S_APB_WR_DLEN: begin
                    $display ("SoC: Writing the Data Length Register\n");
                end
                S_APB_WR_DATAIN: begin
                    $display ("SoC: Writing the Firmware into Data-in Register\n");
                end
                S_APB_WR_EXEC: begin
                    $display ("SoC: Setting the Execute Register\n");
                end
                S_APB_WR_STATUS: begin
                    $display ("SoC: Writing the Mbox Status Register\n");
                end
                S_APB_WAIT_ERROR_AXS: begin
                    $display("SoC: Waiting to see cptra_error_fatal/non_fatal\n");
                end
                S_APB_RD_HW_ERROR_FATAL: begin
                    $display("SoC: Observed cptra_error_fatal; reading Caliptra register\n");
                end
                S_APB_WR_HW_ERROR_FATAL: begin
                    $display("SoC: Observed cptra_error_fatal; writing to clear Caliptra register\n");
                end
                S_APB_RD_HW_ERROR_NON_FATAL: begin
                    $display("SoC: Observed cptra_error_non_fatal; reading Caliptra register\n");
                end
                S_APB_WR_HW_ERROR_NON_FATAL: begin
                    $display("SoC: Observed cptra_error_non_fatal; writing to clear Caliptra register\n");
                end
                S_APB_DONE: begin
                end
                S_APB_RD_DLEN: begin
                    $display("SoC: Reading the Data Length Register\n");
                end
                S_APB_RD_DATAOUT: begin
                    $display("SoC: Reading the Data Out Register\n");
                end
                S_APB_RST_EXEC: begin
                    $display("SoC: Resetting the Execute Register\n");
                end
                default: begin
                    $display("Entering unexpected APB state: %p", n_state_apb);
                end
            endcase
        end
    end

    always_comb begin
        apb_wr_count_nxt = 0;
        apb_rd_count_nxt = 0;
        case (c_state_apb) inside
            S_APB_IDLE: begin
                if (start_apb_fuse_sequence)
                    n_state_apb = S_APB_WR_UDS;
                else
                    n_state_apb = S_APB_IDLE;
            end
            //load fuses
            S_APB_WR_UDS: begin
                if (apb_xfer_end && apb_wr_count == (`CLP_OBF_UDS_DWORDS-1)) begin
                    n_state_apb = S_APB_WR_FE;
                    apb_wr_count_nxt = '0;
                end
                else if (apb_xfer_end) begin
                    n_state_apb = S_APB_WR_UDS;
                    apb_wr_count_nxt = apb_wr_count + 1;
                end
                else begin
                    n_state_apb = S_APB_WR_UDS;
                    apb_wr_count_nxt = apb_wr_count;
                end
            end
            S_APB_WR_FE: begin
                if (apb_xfer_end && apb_wr_count == (`CLP_OBF_FE_DWORDS-1)) begin
                    n_state_apb = S_APB_WR_FUSE_DONE;
                    apb_wr_count_nxt = '0;
                end
                else if (apb_xfer_end) begin
                    n_state_apb = S_APB_WR_FE;
                    apb_wr_count_nxt = apb_wr_count + 1;
                end
                else begin
                    n_state_apb = S_APB_WR_FE;
                    apb_wr_count_nxt = apb_wr_count;
                end
            end
            //set fuse done
            S_APB_WR_FUSE_DONE: begin
                if (apb_xfer_end) begin
                    if(BootFSM_BrkPoint) begin
                       n_state_apb = S_APB_POLL_FLOW_ST;
                    end
                    else begin
                       n_state_apb = S_APB_WAIT_FW_TEST;
                    end
                end
                else begin
                    n_state_apb = S_APB_WR_FUSE_DONE;
                end
            end
            S_APB_POLL_FLOW_ST: begin
                if (apb_xfer_end && (PRDATA[`SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_LOW] == 0)) begin
                    n_state_apb = S_APB_WR_BOOT_GO;
                end
                else begin
                    n_state_apb = S_APB_POLL_FLOW_ST;
                end
            end
            //Write BootGo register
            S_APB_WR_BOOT_GO: begin
                if(apb_xfer_end) begin
                   n_state_apb = S_APB_WAIT_FW_TEST;
                end
                else begin
                   n_state_apb = S_APB_WR_BOOT_GO;
                end
            end
        
            //This is for Caliptra Demo, smoke tests will stop here since they don't set ready for fw
            //wait for fw req
            S_APB_WAIT_FW_TEST: begin
                if (ready_for_fw_push & (apb_wr_count == 5)) begin
                    n_state_apb = S_APB_POLL_LOCK;
                    apb_wr_count_nxt = 0;
                end
                else if (ready_for_fw_push) begin
                    n_state_apb = S_APB_WAIT_FW_TEST;
                    apb_wr_count_nxt = apb_wr_count + 1;
                end
                else if (ras_test_ctrl.error_injection_seen) begin
                    n_state_apb = S_APB_WAIT_ERROR_AXS;
                end
                else begin
                    n_state_apb = S_APB_WAIT_FW_TEST;
                    apb_wr_count_nxt = 0;
                end
            end
            // poll for lock register
            S_APB_POLL_LOCK: begin
                if (apb_xfer_end && (PRDATA != 0)) begin
                    n_state_apb = mbox_apb_dataout_read_ooo ? S_APB_RD_DLEN : S_APB_WR_CMD;
                end
                else begin
                    n_state_apb = S_APB_POLL_LOCK;
                end
            end
            S_APB_PRE_WR_CMD: begin
                if (apb_wr_count == 5) begin
                    n_state_apb = S_APB_WR_CMD;
                    apb_wr_count_nxt = 0;
                end
                else begin
                    n_state_apb = S_APB_PRE_WR_CMD;
                    apb_wr_count_nxt = apb_wr_count + 1;
                end
            end
            //write to MBOX_ADDR_CMD
            S_APB_WR_CMD: begin
                if (apb_xfer_end)
                    n_state_apb = S_APB_WR_DLEN;
                else
                    n_state_apb = S_APB_WR_CMD;
            end
            // write to MBOX_ADDR_DLEN
            S_APB_WR_DLEN: begin
                if (apb_xfer_end)
                    n_state_apb = S_APB_WR_DATAIN;
                else
                    n_state_apb = S_APB_WR_DLEN;
            end
            // write a random block in
            S_APB_WR_DATAIN: begin
                if (apb_xfer_end && apb_wr_count == (FW_NUM_DWORDS-1)) begin
                    n_state_apb = S_APB_WR_EXEC;
                    apb_wr_count_nxt = '0;
                end
                else if (apb_xfer_end) begin
                    n_state_apb = S_APB_WR_DATAIN;
                    apb_wr_count_nxt = apb_wr_count + 1;
                end
                else begin
                    n_state_apb = S_APB_WR_DATAIN;
                    apb_wr_count_nxt = apb_wr_count;
                end
            end
            // execute
            S_APB_WR_EXEC: begin
                if (apb_xfer_end)
                    n_state_apb = S_APB_DONE;
                else
                    n_state_apb = S_APB_WR_EXEC;
            end
            // status
            S_APB_WR_STATUS: begin
                if (apb_xfer_end)
                    n_state_apb = S_APB_DONE;
                else
                    n_state_apb = S_APB_WR_STATUS;
            end
            S_APB_WAIT_ERROR_AXS: begin
                if (cptra_error_fatal_dly_p) begin
                    n_state_apb = S_APB_RD_HW_ERROR_FATAL;
                end
                else if (cptra_error_non_fatal_dly_p) begin
                    n_state_apb = S_APB_RD_HW_ERROR_NON_FATAL;
                end
                else if (soc_ifc_hw_error_wdata) begin
                    n_state_apb = S_APB_WR_HW_ERROR_FATAL;
                end
                else if (ras_test_ctrl.do_no_lock_access) begin
                    n_state_apb = S_APB_RD_DLEN;
                end
                else if (mbox_apb_dataout_read_ooo && !mbox_ooo_read_done) begin
                    n_state_apb = S_APB_POLL_LOCK;
                end
                else begin
                    n_state_apb = S_APB_WAIT_ERROR_AXS;
                end
            end
            S_APB_RD_HW_ERROR_FATAL: begin
                // Go to ERROR state to wait for cptra_rst_b to assert
                if (apb_xfer_end) begin
                    n_state_apb = S_APB_ERROR;
                end
                else begin
                    n_state_apb = S_APB_RD_HW_ERROR_FATAL;
                end
            end
            S_APB_WR_HW_ERROR_FATAL: begin
                if (apb_xfer_end) begin
                    n_state_apb = S_APB_WAIT_ERROR_AXS;
                end
                else begin
                    n_state_apb = S_APB_WR_HW_ERROR_FATAL;
                end
            end
            S_APB_RD_HW_ERROR_NON_FATAL: begin
                if (apb_xfer_end) begin
                    n_state_apb = S_APB_WR_HW_ERROR_NON_FATAL;
                end
                else begin
                    n_state_apb = S_APB_RD_HW_ERROR_NON_FATAL;
                end
            end
            S_APB_WR_HW_ERROR_NON_FATAL: begin
                if (apb_xfer_end) begin
                    n_state_apb = S_APB_WAIT_ERROR_AXS;
                end
                else begin
                    n_state_apb = S_APB_WR_HW_ERROR_NON_FATAL;
                end
            end
            S_APB_DONE: begin
                apb_wr_count_nxt = '0;
                apb_rd_count_nxt = '0;
                if (mailbox_data_avail && execute_mbox_rx_protocol)
                    n_state_apb = S_APB_RD_DLEN;
                else if (mailbox_data_avail && ~status_set && ~execute_mbox_rx_protocol)
                    n_state_apb = S_APB_WR_STATUS;
                else
                    n_state_apb = S_APB_DONE;
            end
            S_APB_RD_DLEN: begin
                if (apb_xfer_end)
                    n_state_apb = S_APB_RD_DATAOUT;
                else
                    n_state_apb = S_APB_RD_DLEN;
            end
            S_APB_RD_DATAOUT: begin
                if (apb_xfer_end && (apb_rd_count == dlen)) begin
                    n_state_apb = (mbox_no_lock_read_done || mbox_ooo_read_done) ? S_APB_WAIT_ERROR_AXS : S_APB_RST_EXEC;
                    apb_rd_count_nxt = '0;
                end
                else if (apb_xfer_end) begin
                    n_state_apb = S_APB_RD_DATAOUT;
                    apb_rd_count_nxt = apb_rd_count + 1;
                end
                else begin
                    n_state_apb = S_APB_RD_DATAOUT;
                    apb_rd_count_nxt = apb_rd_count;
                end
            end
            S_APB_RST_EXEC: begin
                if (apb_xfer_end)
                    n_state_apb = S_APB_DONE;
                else
                    n_state_apb = S_APB_RST_EXEC;
            end
            default: begin
                apb_wr_count_nxt = apb_wr_count;
                apb_rd_count_nxt = apb_rd_count;
                n_state_apb = S_APB_ERROR;
            end
        endcase
    end
    
    always@(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            status_set  <= '0;
        end else begin
            status_set <= ~mailbox_data_avail ? '0 :
                          (c_state_apb == S_APB_WR_STATUS) ? '1 : status_set;
        end
    end

    assign apb_xfer_end = PSEL && PENABLE && PREADY;
    always@(posedge core_clk) begin
        if ((n_state_apb == S_APB_WR_DATAIN) && apb_xfer_end)
            fw_blob[apb_wr_count_nxt] <= $urandom;
    end
    always_comb begin
        case (c_state_apb) inside
            S_APB_WR_UDS: begin
                PADDR      = `CLP_SOC_IFC_REG_FUSE_UDS_SEED_0 + 4 * apb_wr_count;
                PWDATA     = cptra_uds_tb[apb_wr_count];
            end
            S_APB_WR_FE: begin
                PADDR      = `CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_0 + 4 * apb_wr_count;
                PWDATA     = cptra_fe_tb[apb_wr_count];
            end
            S_APB_WR_FUSE_DONE: begin
                PADDR      = `CLP_SOC_IFC_REG_CPTRA_FUSE_WR_DONE;
                PWDATA     = 32'h00000001;
            end
            S_APB_POLL_FLOW_ST: begin
                PADDR      = `CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS; 
                PWDATA     = '0;
            end
            S_APB_WR_BOOT_GO: begin
                PADDR      = `CLP_SOC_IFC_REG_CPTRA_BOOTFSM_GO; 
                PWDATA     = 32'h00000001;
            end
            S_APB_POLL_LOCK: begin
                PADDR      = `CLP_MBOX_CSR_MBOX_LOCK;
                PWDATA     = '0;
            end
            S_APB_WR_CMD: begin
                PADDR      = `CLP_MBOX_CSR_MBOX_CMD;
                PWDATA     = 32'hBA5EBA11;
            end
            S_APB_WR_DLEN: begin
                PADDR      = `CLP_MBOX_CSR_MBOX_DLEN;
                PWDATA     = FW_NUM_DWORDS*4;
            end
            S_APB_WR_DATAIN: begin
                PADDR      = `CLP_MBOX_CSR_MBOX_DATAIN;
                PWDATA     = fw_blob[apb_wr_count];
            end
            S_APB_WR_EXEC: begin
                PADDR      = `CLP_MBOX_CSR_MBOX_EXECUTE;
                PWDATA     = 32'h00000001;
            end
            S_APB_WR_STATUS: begin
                PADDR      = `CLP_MBOX_CSR_MBOX_STATUS;
                PWDATA     = 32'h00000001;
            end
            S_APB_RD_HW_ERROR_FATAL: begin
                PADDR      = `CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL;
                PWDATA     = soc_ifc_hw_error_wdata;
            end
            S_APB_WR_HW_ERROR_FATAL: begin
                PADDR      = `CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL;
                PWDATA     = soc_ifc_hw_error_wdata;
            end
            S_APB_RD_HW_ERROR_NON_FATAL: begin
                PADDR      = `CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL;
                PWDATA     = soc_ifc_hw_error_wdata;
            end
            S_APB_WR_HW_ERROR_NON_FATAL: begin
                PADDR      = `CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL;
                PWDATA     = soc_ifc_hw_error_wdata;
            end
            S_APB_DONE: begin
                PADDR      = '0;
                PWDATA     = '0;
            end
            S_APB_RD_DLEN: begin
                PADDR      = `CLP_MBOX_CSR_MBOX_DLEN;
                PWDATA     = dlen;
            end
            S_APB_RD_DATAOUT: begin
                PADDR      = `CLP_MBOX_CSR_MBOX_DATAOUT;
                PWDATA     = '0;
            end
            S_APB_RST_EXEC: begin
                PADDR      = `CLP_MBOX_CSR_MBOX_EXECUTE;
                PWDATA     = '0;
            end
            default: begin
                PADDR      = '0;
                PWDATA     = '0;
            end
        endcase
    end
    always_comb begin
        PENABLE = apb_enable_ph;
        case (c_state_apb) inside
            S_APB_IDLE: begin
                PSEL       = 0;
                PWRITE     = 0;
                PAUSER     = 0;
            end
            S_APB_WR_UDS: begin
                PSEL       = 1;
                PWRITE     = 1;
                PAUSER     = 0;
            end
            S_APB_WR_FE: begin
                PSEL       = 1;
                PWRITE     = 1;
                PAUSER     = 0;
            end
            S_APB_WR_FUSE_DONE: begin
                PSEL       = 1;
                PWRITE     = 1;
                PAUSER     = 0;
            end
            S_APB_POLL_FLOW_ST: begin
                PSEL       = 1;
                PWRITE     = 0;
                PAUSER     = 0;
            end
            S_APB_WR_BOOT_GO: begin
                PSEL       = 1;
                PWRITE     = 1;
                PAUSER     = 0;
            end
            S_APB_POLL_LOCK: begin
                PSEL       = 1;
                PWRITE     = 0;
                PAUSER     = '1;
            end
            S_APB_WR_CMD: begin
                PSEL       = 1;
                PWRITE     = 1;
                PAUSER     = '1;
            end
            S_APB_WR_DLEN: begin
                PSEL       = 1;
                PWRITE     = 1;
                PAUSER     = '1;
            end
            S_APB_WR_DATAIN: begin
                PSEL       = 1;
                PWRITE     = 1;
                PAUSER     = '1;
            end
            S_APB_WR_EXEC: begin
                PSEL       = 1;
                PWRITE     = 1;
                PAUSER     = '1;
            end
            S_APB_WR_STATUS: begin
                PSEL       = 1;
                PWRITE     = 1;
                PAUSER     = '1;
            end
            S_APB_RD_HW_ERROR_FATAL: begin
                PSEL       = 1;
                PWRITE     = 0;
                PAUSER     = '1;
            end
            S_APB_WR_HW_ERROR_FATAL: begin
                PSEL       = 1;
                PWRITE     = 1;
                PAUSER     = '1;
            end
            S_APB_RD_HW_ERROR_NON_FATAL: begin
                PSEL       = 1;
                PWRITE     = 0;
                PAUSER     = '1;
            end
            S_APB_WR_HW_ERROR_NON_FATAL: begin
                PSEL       = 1;
                PWRITE     = 1;
                PAUSER     = '1;
            end
            S_APB_DONE: begin
                PSEL       = 0;
                PWRITE     = 0;
                PAUSER     = 0;
            end
            S_APB_RD_DLEN: begin
                PSEL       = 1;
                PWRITE     = 0;
                PAUSER     = '1; //TODO - which value?
            end
            S_APB_RD_DATAOUT: begin
                PSEL       = 1;
                PWRITE     = 0;
                PAUSER     = '1;
            end
            S_APB_RST_EXEC: begin
                PSEL       = 1;
                PWRITE     = 1;
                PAUSER     = '1;
            end
            default: begin
                PSEL       = 0;
                PWRITE     = 0;
                PAUSER     = 0;
            end
        endcase
    end

// JTAG DPI
jtagdpi #(
    .Name           ("jtag0"),
    .ListenPort     (5000)
) jtagdpi (
    .clk_i          (core_clk),
    .rst_ni         (cptra_rst_b),
    .jtag_tck       (jtag_tck),
    .jtag_tms       (jtag_tms),
    .jtag_tdi       (jtag_tdi),
    .jtag_tdo       (jtag_tdo),
    .jtag_trst_n    (jtag_trst_n),
    .jtag_srst_n    ()
);

   //=========================================================================-
   // DUT instance
   //=========================================================================-
caliptra_top caliptra_top_dut (
    .cptra_pwrgood              (cptra_pwrgood),
    .cptra_rst_b                (cptra_rst_b),
    .clk                        (core_clk),

    .cptra_obf_key              (cptra_obf_key),

    .jtag_tck(jtag_tck),
    .jtag_tdi(jtag_tdi),
    .jtag_tms(jtag_tms),
    .jtag_trst_n(jtag_trst_n),
    .jtag_tdo(jtag_tdo),
    
    .PADDR(PADDR),
    .PPROT(PPROT),
    .PAUSER(PAUSER),
    .PENABLE(PENABLE),
    .PRDATA(PRDATA),
    .PREADY(PREADY),
    .PSEL(PSEL),
    .PSLVERR(),
    .PWDATA(PWDATA),
    .PWRITE(PWRITE),

    .qspi_clk_o (qspi_clk),
    .qspi_cs_no (qspi_cs_n),
    .qspi_d_i   (qspi_data_device_to_host),
    .qspi_d_o   (qspi_data_host_to_device),
    .qspi_d_en_o(qspi_data_host_to_device_en),

`ifdef CALIPTRA_INTERNAL_UART
    .uart_tx(uart_loopback),
    .uart_rx(uart_loopback),
`endif

    .el2_mem_export(el2_mem_export),

    .ready_for_fuses(ready_for_fuses),
    .ready_for_fw_push(ready_for_fw_push),
    .ready_for_runtime(),

    .mbox_sram_cs(mbox_sram_cs),
    .mbox_sram_we(mbox_sram_we),
    .mbox_sram_addr(mbox_sram_addr),
    .mbox_sram_wdata(mbox_sram_wdata),
    .mbox_sram_rdata(mbox_sram_rdata),
        
    .imem_cs(imem_cs),
    .imem_addr(imem_addr),
    .imem_rdata(imem_rdata),

    .mailbox_data_avail(mailbox_data_avail),
    .mailbox_flow_done(),
    .BootFSM_BrkPoint(BootFSM_BrkPoint),

    //SoC Interrupts
    .cptra_error_fatal    (cptra_error_fatal    ),
    .cptra_error_non_fatal(cptra_error_non_fatal),

`ifdef CALIPTRA_INTERNAL_TRNG
    .etrng_req             (etrng_req),
    .itrng_data            (itrng_data),
    .itrng_valid           (itrng_valid),
`else
    .etrng_req             (),
    .itrng_data            (4'b0),
    .itrng_valid           (1'b0),
`endif

    .generic_input_wires(generic_input_wires),
    .generic_output_wires(),

    .security_state(security_state),
    .scan_mode     (scan_mode)
);


`ifdef CALIPTRA_INTERNAL_TRNG
    //=========================================================================-
    // Physical RNG used for Internal TRNG
    //=========================================================================-
physical_rng physical_rng (
    .clk    (core_clk),
    .enable (etrng_req),
    .data   (itrng_data),
    .valid  (itrng_valid)
);
`endif

`ifdef CALIPTRA_INTERNAL_QSPI
    //=========================================================================-
    // SPI Flash
    //=========================================================================-
for (genvar ii = 0; ii < `CALIPTRA_QSPI_IO_WIDTH; ii += 1) begin: gen_qspi_io
  assign qspi_data[ii] = qspi_data_host_to_device_en[ii]
      ? qspi_data_host_to_device[ii]
      : 1'bz;
  assign qspi_data_device_to_host[ii] = qspi_data_host_to_device_en[ii]
      ? 1'bz
      : qspi_data[ii];
end

localparam logic [15:0] DeviceId0 = 16'hF10A;
localparam logic [15:0] DeviceId1 = 16'hF10B;

spiflash #(
  .DeviceId(DeviceId0),
  .SpiFlashRandomData(0) // fixed pattern for smoke test
) spiflash0 (
  .sck (qspi_clk),
  .csb (qspi_cs_n[0]),
  .sd  (qspi_data)
);

spiflash #(
  .DeviceId(DeviceId1),
  .SpiFlashRandomData(0) // fixed pattern for smoke test
) spiflash1 (
  .sck (qspi_clk),
  .csb (qspi_cs_n[1]),
  .sd  (qspi_data)
);

`endif

   //=========================================================================-
   // Services for SRAM exports, STDOUT, etc
   //=========================================================================-
caliptra_top_tb_services #(
    .UVM_TB(0)
) tb_services_i (
    .clk(core_clk),

    .cptra_rst_b(cptra_rst_b),

    // Caliptra Memory Export Interface
    .el2_mem_export (el2_mem_export),

    //SRAM interface for mbox
    .mbox_sram_cs   (mbox_sram_cs   ),
    .mbox_sram_we   (mbox_sram_we   ),
    .mbox_sram_addr (mbox_sram_addr ),
    .mbox_sram_wdata(mbox_sram_wdata),
    .mbox_sram_rdata(mbox_sram_rdata),

    //SRAM interface for imem
    .imem_cs   (imem_cs   ),
    .imem_addr (imem_addr ),
    .imem_rdata(imem_rdata),

    // Security State
    .security_state(security_state),

    //Scan mode
    .scan_mode(scan_mode),

    // TB Controls
    .ras_test_ctrl(ras_test_ctrl),
    .cycleCnt(cycleCnt),

    //Interrupt flags
    .int_flag(int_flag),
    .cycleCnt_smpl_en(cycleCnt_smpl_en),

    //Reset flags
    .assert_hard_rst_flag(assert_hard_rst_flag),
    .deassert_hard_rst_flag(deassert_hard_rst_flag),

    .assert_rst_flag(assert_rst_flag_from_service),
    .deassert_rst_flag(deassert_rst_flag_from_service),
    
    .cptra_uds_tb(cptra_uds_rand),
    .cptra_fe_tb(cptra_fe_rand),
    .cptra_obf_key_tb(cptra_obf_key_tb)

);

caliptra_top_sva sva();

endmodule
