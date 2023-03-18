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

    import caliptra_top_tb_pkg::*;
    import soc_ifc_pkg::*;

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

    logic [7:0][31:0]           cptra_obf_key;
    logic [0:7][31:0]           cptra_obf_key_uds, cptra_obf_key_fe;
    
    logic [0:11][31:0]          cptra_uds_tb;
    logic [0:31][31:0]          cptra_fe_tb;

    logic                       start_apb_fuse_sequence;

    enum logic [5:0] {
        S_APB_IDLE,
        S_APB_WR_UDS,
        S_APB_WR_FE,
        S_APB_WR_FUSE_DONE,
        S_APB_WR_BOOT_GO,
        S_APB_WAIT_FW_READY,
        S_APB_POLL_LOCK,
        S_APB_PRE_WR_CMD,
        S_APB_WR_CMD,
        S_APB_WR_DLEN,
        S_APB_WR_DATAIN,
        S_APB_WR_EXEC,
        S_APB_DONE,
        S_APB_ERROR
    } n_state_apb, c_state_apb;

    logic [$clog2(FW_NUM_DWORDS)-1:0] apb_wr_count, apb_wr_count_nxt;
    logic apb_enable_ph;
    logic apb_xfer_end;

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

    logic ready_for_fuses;
    logic ready_for_fw_push;
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

    logic [63:0] generic_input_wires;
    logic        etrng_req;
    logic  [3:0] itrng_data;
    logic        itrng_valid;

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
    logic assert_rst_flag;
    logic deassert_rst_flag;

    el2_mem_if el2_mem_export ();

    parameter FW_NUM_DWORDS         = 256;

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
            generic_input_wires <= 'h4001; //Toggle wires
        end
        
        else if((cycleCnt == cycleCnt_ff + 15000) && int_flag) begin
            force caliptra_top_dut.soft_int = 'b1;
        end
        
        else begin
            release caliptra_top_dut.soft_int;
            release caliptra_top_dut.timer_int;
            generic_input_wires <= 'h0;
        end
    end


    initial begin
        cptra_pwrgood = 1'b0;
        BootFSM_BrkPoint = 1'b1; //Set to 1 even before anything starts
        cptra_rst_b = 1'b0;
        scan_mode = 1'b0;
        start_apb_fuse_sequence = 1'b0;
        //tie offs
        jtag_tck = 1'b0;    // JTAG clk
        jtag_tms = 1'b0;    // JTAG TMS
        jtag_tdi = 1'b0;    // JTAG tdi
        jtag_trst_n = 1'b0; // JTAG Reset
        //TIE-OFF
        PPROT = '0;

`ifndef VERILATOR
        if($test$plusargs("dumpon")) $dumpvars;
`endif

        //Key for UDS 
        cptra_obf_key_uds = 256'h54682728db5035eb04b79645c64a95606abb6ba392b6633d79173c027c5acf77;
        cptra_uds_tb = 384'he4046d05385ab789c6a72866e08350f93f583e2a005ca0faecc32b5cfc323d461c76c107307654db5566a5bd693e227c;

        //Key for FE
        cptra_obf_key_fe = 256'h31358e8af34d6ac31c958bbd5c8fb33c334714bffb41700d28b07f11cfe891e7;
        cptra_fe_tb = {256'hb32e2b171b63827034ebb0d1909f7ef1d51c5f82c1bb9bc26bc4ac4dccdee835,
                       256'h7dca6154c2510ae1c87b1b422b02b621bb06cac280023894fcff3406af08ee9b,
                       256'he1dd72419beccddff77c722d992cdcc87e9c7486f56ab406ea608d8c6aeb060c,
                       256'h64cf2785ad1a159147567e39e303370da445247526d95942bf4d7e88057178b0};

        //swizzle the key so it matches the endianness of AES block
        //used for visual inspection of uds/fe flow, manually switching keys and checking both
        for (int dword = 0; dword < $bits(cptra_obf_key/32); dword++) begin
            //cptra_obf_key[dword] = cptra_obf_key_uds[dword];
            cptra_obf_key[dword] = cptra_obf_key_fe[dword];
        end
    end

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
        end
        else if (assert_rst_flag) begin
            cptra_rst_b <= 'b0;
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

    always@(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            c_state_apb  <= S_APB_IDLE;
            apb_wr_count <= '0;
            apb_enable_ph <= 0;
        end
        else begin
            c_state_apb  <= n_state_apb;
            apb_wr_count <= apb_wr_count_nxt;
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
                S_APB_WR_BOOT_GO: begin
                    $display ("SoC: Writing BootGo register\n");
                end
                S_APB_WAIT_FW_READY: begin
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
                S_APB_DONE: begin
                end
                default: begin
                    $display("Entering unexpected APB state: %p", n_state_apb);
                end
            endcase
        end
    end

    always_comb begin
        apb_wr_count_nxt = 0;
        case (c_state_apb) inside
            S_APB_IDLE: begin
                if (start_apb_fuse_sequence)
                    n_state_apb = S_APB_WR_UDS;
                else
                    n_state_apb = S_APB_IDLE;
            end
            //load fuses
            S_APB_WR_UDS: begin
                if (apb_xfer_end && apb_wr_count == 11) begin
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
                if (apb_xfer_end && apb_wr_count == 31) begin
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
                       n_state_apb = S_APB_WR_BOOT_GO;
                    end
                    else begin
                       n_state_apb = S_APB_WAIT_FW_READY;
                    end
                end
                else begin
                    n_state_apb = S_APB_WR_FUSE_DONE;
                end
            end
            //Write BootGo register
            S_APB_WR_BOOT_GO: begin
                if(apb_xfer_end) begin
                   n_state_apb = S_APB_WAIT_FW_READY;
                end
                else begin
                   n_state_apb = S_APB_WR_BOOT_GO;
                end
            end
        
            //This is for Caliptra Demo, smoke tests will stop here since they don't set ready for fw
            //wait for fw req
            S_APB_WAIT_FW_READY: begin
                if (ready_for_fw_push & (apb_wr_count == 5)) begin
                    n_state_apb = S_APB_POLL_LOCK;
                    apb_wr_count_nxt = 0;
                end
                else if (ready_for_fw_push) begin
                    n_state_apb = S_APB_WAIT_FW_READY;
                    apb_wr_count_nxt = apb_wr_count + 1;
                end
                else begin
                    n_state_apb = S_APB_WAIT_FW_READY;
                    apb_wr_count_nxt = 0;
                end
            end
            // poll for lock register
            S_APB_POLL_LOCK: begin
                if (apb_xfer_end && (PRDATA != 0)) begin
                    n_state_apb = S_APB_WR_CMD;
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
            S_APB_DONE: begin
                apb_wr_count_nxt = '0;
                n_state_apb = S_APB_DONE;
            end
            default: begin
                apb_wr_count_nxt = apb_wr_count;
                n_state_apb = S_APB_ERROR;
            end
        endcase
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
            S_APB_DONE: begin
                PADDR      = '0;
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
            S_APB_DONE: begin
                PSEL       = 0;
                PWRITE     = 0;
                PAUSER     = 0;
            end
            default: begin
                PSEL       = 0;
                PWRITE     = 0;
                PAUSER     = 0;
            end
        endcase
    end


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

    .qspi_clk_o(),
    .qspi_cs_no(),
    .qspi_d_io(),

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

    .mailbox_data_avail(),
    .mailbox_flow_done(),
    .BootFSM_BrkPoint(BootFSM_BrkPoint),

    //SoC Interrupts
    .cptra_error_fatal    (),
    .cptra_error_non_fatal(),

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

    .security_state(security_state), //FIXME TIE-OFF
    .scan_mode     (scan_mode) //FIXME TIE-OFF
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

    // TB Controls
    .cycleCnt(cycleCnt),

    //Interrupt flags
    .int_flag(int_flag),
    .cycleCnt_smpl_en(cycleCnt_smpl_en),

    //Reset flags
    .assert_hard_rst_flag(assert_hard_rst_flag),
    .deassert_hard_rst_flag(deassert_hard_rst_flag),
    .assert_rst_flag(assert_rst_flag),
    .deassert_rst_flag(deassert_rst_flag)

);

caliptra_top_sva sva();


endmodule
