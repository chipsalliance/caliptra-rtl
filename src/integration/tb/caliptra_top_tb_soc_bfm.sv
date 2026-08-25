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

`include "common_defines.sv"
`include "config_defines.svh"
`include "caliptra_reg_defines.svh"
`include "caliptra_reg_field_defines.svh"
`include "caliptra_macros.svh"

module caliptra_top_tb_soc_bfm
import axi_pkg::*;
import soc_ifc_pkg::*;
import mbox_pkg::*;
import kv_defines_pkg::*;
import caliptra_top_tb_pkg::*; #(
    parameter SKIP_BRINGUP = 0
) (
    input logic core_clk,
    output logic                       cptra_pwrgood,
    output logic                       cptra_rst_b,
    output logic                       BootFSM_BrkPoint,
    input int                          cycleCnt,

    output logic [`CLP_OBF_KEY_DWORDS-1:0][31:0]          cptra_obf_key,
    output logic [`CLP_CSR_HMAC_KEY_DWORDS-1:0][31:0]     cptra_csr_hmac_key,

    input  logic [0:`CLP_OBF_UDS_DWORDS-1][31:0]          cptra_uds_rand,
    input  logic [0:`CLP_OBF_FE_DWORDS-1] [31:0]          cptra_fe_rand,
    input  logic [0:OCP_LOCK_HEK_NUM_DWORDS-1] [31:0]     cptra_hek_rand,
    input  logic [0:`CLP_OBF_KEY_DWORDS-1][31:0]          cptra_obf_key_tb,

    axi_if m_axi_bfm_if,

    output logic [15:0] strap_ss_key_release_key_size,
    output logic [63:0] strap_ss_key_release_base_addr,

    output logic ss_ocp_lock_en,

    output logic itrng1_en,

    // Secondary iTRNG (ES1) source control for the entropy-combiner bench:
    // observe the ES1 entropy request (etrng1_req) and assert second_RNG_triggered
    // a random number of cycles (0-100) later to model a late-arriving noise source.
    input  logic etrng1_req,
    output logic second_RNG_triggered,

    output logic [31:0] strap_ss_strap_generic_0,
    output logic [31:0] strap_ss_strap_generic_1,
    output logic [31:0] strap_ss_strap_generic_2,
    output logic [31:0] strap_ss_strap_generic_3,

    input logic ready_for_fuses,
    input logic ready_for_mb_processing,
    input logic mailbox_data_avail,

    input  var  ras_test_ctrl_t ras_test_ctrl,

    output logic [63:0] generic_input_wires,

    input logic cptra_error_fatal,
    input logic cptra_error_non_fatal,
    
    //Interrupt flags
    input logic int_flag,
    input logic cycleCnt_smpl_en,

    input logic assert_hard_rst_flag,
    input logic deassert_hard_rst_flag,
    input logic assert_rst_flag_from_service,
    input logic deassert_rst_flag_from_service

);
    localparam FW_NUM_DWORDS         = 256;

    int poll_count;

    logic [0:`CLP_OBF_KEY_DWORDS-1][31:0]          cptra_obfkey_tb;

    logic [0:`CLP_OBF_UDS_DWORDS-1][31:0]          cptra_uds_tb;
    logic [0:`CLP_OBF_FE_DWORDS-1][31:0]           cptra_fe_tb;
    logic [0:OCP_LOCK_HEK_NUM_DWORDS-1] [31:0]     cptra_hek_tb;

    // AXI request signals
    axi_resp_e wresp, rresp;
    logic [`CALIPTRA_AXI_DATA_WIDTH  -1:0] wdata, rdata;
    logic [`CALIPTRA_AXI_DATA_WIDTH/8-1:0] wstrb_array[];
    logic [`CALIPTRA_AXI_USER_WIDTH  -1:0] wuser_array[];
    logic [`CALIPTRA_AXI_USER_WIDTH  -1:0] buser;
    logic [`CALIPTRA_AXI_DATA_WIDTH  -1:0] rdata_array[];
    logic [`CALIPTRA_AXI_USER_WIDTH  -1:0] ruser_array[];
    axi_resp_e rresp_array[];

    int byte_count;
    int dw_count;

    logic [15:0] cptra_error_fatal_counter;
    logic [15:0] cptra_error_non_fatal_counter;
    logic cptra_error_fatal_dly_p;
    logic cptra_error_non_fatal_dly_p;

    logic rv_dma_resp_error;

    logic [`CALIPTRA_AXI_DATA_WIDTH-1:0] soc_ifc_hw_error_wdata;

    process boot_and_cmd_flow;

    logic assert_rst_flag_from_fatal;
    logic assert_rst_flag;
    int   count_deassert_rst_flag_from_fatal;
    logic deassert_rst_flag_from_fatal;
    logic deassert_rst_flag;

    logic [31:0] fw_blob [];

    // smoke_test_stash_bank_rst: populate stash only on the first boot; skip
    // on subsequent warm-reset boots so FW can observe cleared lock state.
    bit stash_bank_rst_boot_complete;

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

    // -------------------------------------------------------------------------
    // Secondary iTRNG (ES1) source trigger for the entropy-combiner bench.
    // The primary iTRNG source is enabled directly by the DUT's etrng0_req. The
    // secondary source is modeled as coming online a random number of cycles
    // (0-100) after ES1 first asserts etrng1_req, so the combiner observes
    // ES1 entropy arriving later than ES0. Once triggered it latches high until
    // reset. The delay is randomized by default; +CLP_SECOND_RNG_DELAY overrides
    // it for reproducible runs. itrng1_en (set above) separately controls whether
    // the DUT actually consumes/combines ES1.
    // -------------------------------------------------------------------------
    int unsigned second_rng_delay;
    int unsigned second_rng_count;

    initial begin
        second_RNG_triggered = 1'b0;
        second_rng_count     = 0;
        if (!$value$plusargs("CLP_SECOND_RNG_DELAY=%d", second_rng_delay)) begin
            second_rng_delay = $urandom_range(0, 100);
        end
        $display("SECOND_RNG_TRIGGERED will assert ~%0d cycle(s) after etrng1_req", second_rng_delay);
    end

    always @(posedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            second_RNG_triggered <= 1'b0;
            second_rng_count     <= 0;
        end
        else if (!second_RNG_triggered && etrng1_req) begin
            if (second_rng_count >= second_rng_delay)
                second_RNG_triggered <= 1'b1;
            else
                second_rng_count <= second_rng_count + 1;
        end
    end

    initial begin
        // Initialize strap_ss_key_release_key_size based on plusargs
        if ($test$plusargs("STRAP_SS_KEY_RELEASE_KEY_SIZE_MANUAL")) begin
            if (!$value$plusargs("STRAP_SS_KEY_RELEASE_KEY_SIZE_MANUAL=%h", strap_ss_key_release_key_size)) begin
                $error("Failed to get value for +STRAP_SS_KEY_RELEASE_KEY_SIZE_MANUAL");
            end
            $display("STRAP_SS_KEY_RELEASE_KEY_SIZE set manually to 0x%04x", strap_ss_key_release_key_size);
        end
        else if ($test$plusargs("STRAP_SS_KEY_RELEASE_KEY_SIZE_RAND_LOW")) begin
            // Randomize from 4 to 64 bytes, ensure DWORD alignment
            strap_ss_key_release_key_size = $urandom_range(16'h4, 16'h40);
            strap_ss_key_release_key_size = strap_ss_key_release_key_size & ~16'h3;
            $display("STRAP_SS_KEY_RELEASE_KEY_SIZE randomized (0x4-0x40, DWORD aligned) to 0x%04x", strap_ss_key_release_key_size);
        end
        else if ($test$plusargs("STRAP_SS_KEY_RELEASE_KEY_SIZE_RAND_HIGH")) begin
`ifdef CLP_ASSERT_ON
    `ifndef VERILATOR
            $assertoff(0, `CPTRA_TOP_PATH.soc_ifc_top1.SS_STRAP_KEY_SIZE_LTE_64);
    `endif // VERILATOR
`endif // CLP_ASSERT_ON
            strap_ss_key_release_key_size = $urandom_range(16'h44, 16'hFFFF);
            // Ensure DWORD alignment by clearing lower 2 bits
            strap_ss_key_release_key_size = strap_ss_key_release_key_size & ~16'h3;
            $display("STRAP_SS_KEY_RELEASE_KEY_SIZE randomized (>0x40, DWORD aligned) to 0x%04x", strap_ss_key_release_key_size);
        end
        else if ($test$plusargs("STRAP_SS_KEY_RELEASE_KEY_SIZE_RAND_ANY")) begin
            strap_ss_key_release_key_size = $urandom();
            // Ensure DWORD alignment by clearing lower 2 bits
            strap_ss_key_release_key_size = strap_ss_key_release_key_size & ~16'h3;
            $display("STRAP_SS_KEY_RELEASE_KEY_SIZE randomized (any value, DWORD aligned) to 0x%04x", strap_ss_key_release_key_size);
        end
        else begin
            // Default value (already DWORD aligned)
            strap_ss_key_release_key_size = 16'h40;
            $display("STRAP_SS_KEY_RELEASE_KEY_SIZE set to default value 0x%04x", strap_ss_key_release_key_size);
        end
        
        if ($test$plusargs("CLP_OCP_LOCK_EN")) begin
            ss_ocp_lock_en = 1'b1;
        end
        else if ($test$plusargs("CLP_OCP_LOCK_DIS")) begin
            ss_ocp_lock_en = 1'b0;
        end
        else begin
            // Randomize when neither plusarg is set
            ss_ocp_lock_en = $urandom();
        end

        if ($test$plusargs("CLP_ITRNG1_EN")) begin
            itrng1_en = 1'b1;
        end
        else begin
            itrng1_en = 1'b0;
        end

        // Initialize SS strap generics: randomize by default, plusarg overrides
        for (int i = 0; i < 4; i++) begin
            automatic logic [31:0] strap_val;
            strap_val = $urandom();
            case (i)
                0: strap_ss_strap_generic_0 = strap_val;
                1: strap_ss_strap_generic_1 = strap_val;
                2: strap_ss_strap_generic_2 = strap_val;
                3: strap_ss_strap_generic_3 = strap_val;
            endcase
            $display("STRAP_SS_STRAP_GENERIC_%0d randomized to 0x%08x", i, strap_val);
        end
        if ($test$plusargs("CLP_SS_STRAP_GENERIC_3_EN")) begin
            strap_ss_strap_generic_3[0] = 1'b1;
            $display("STRAP_SS_STRAP_GENERIC_3[0] forced to 1 by +CLP_SS_STRAP_GENERIC_3_EN");
        end
        else if ($test$plusargs("CLP_SS_STRAP_GENERIC_3_DIS")) begin
            strap_ss_strap_generic_3[0] = 1'b0;
            $display("STRAP_SS_STRAP_GENERIC_3[0] forced to 0 by +CLP_SS_STRAP_GENERIC_3_DIS");
        end

        // Initialize strap_ss_key_release_base_addr based on plusargs
        if ($test$plusargs("STRAP_SS_KEY_RELEASE_BASE_ADDR_RAND_SRAM")) begin
            logic [63:0] random_offset;
            // Ensure address is at least 64 bytes (512 bits) before end of SRAM
            random_offset = $urandom_range(64'h0, AXI_SRAM_SIZE_BYTES - 64 - 1);
            random_offset = random_offset & ~64'h3;
            strap_ss_key_release_base_addr = AXI_SRAM_BASE_ADDR + random_offset;
            $display("STRAP_SS_KEY_RELEASE_BASE_ADDR randomized within AXI SRAM to 0x%016x", strap_ss_key_release_base_addr);
        end
        else begin
            // Default value
            strap_ss_key_release_base_addr = AXI_SRAM_BASE_ADDR;
            $display("STRAP_SS_KEY_RELEASE_BASE_ADDR set to default value 0x%016x", strap_ss_key_release_base_addr);
        end
    end


    initial begin
        cptra_pwrgood = 1'b0;
        BootFSM_BrkPoint = $urandom_range(1,0); //Set before anything starts (drive like a const strap)
        cptra_rst_b = 1'b0;
        assert_rst_flag_from_fatal = 1'b0;
        m_axi_bfm_if.rst_mgr();

`ifndef VERILATOR
        // Legacy VCD dump (+dumpon). Prefer +fsdbon in caliptra_top_tb.sv for FSDB/Verdi.
        if($test$plusargs("dumpon")) $dumpvars;
`endif

        if($test$plusargs("RAND_DOE_VALUES")) begin
            //cptra_obf_key = cptra_obf_key_tb;
            for (int dword = 0; dword < $bits(cptra_obf_key)/32; dword++) begin
                `ifndef VERILATOR
                    wait(cptra_obf_key_tb[dword] !== 32'hXXXXXXXX);
                `endif
                cptra_obf_key[dword] = cptra_obf_key_tb[dword];
            end

            cptra_uds_tb = cptra_uds_rand;
            cptra_fe_tb = cptra_fe_rand;
            cptra_hek_tb = cptra_hek_rand;
        end
        else begin
            if ($test$plusargs("SECOND_DOE_KAT")) begin
                //Key for DOE
                cptra_obfkey_tb = 256'he1dd72419beccddff77c722d992cdcc87e9c7486f56ab406ea608d8c6aeb060c;
                cptra_uds_tb = 512'h32cd8a75b5e515bd7b0fe37a6de144696aeedb1f5e03225a71fc690f5b004ff593794db7a99ced97c376385149c4ecafd3afd70cb657a6f6434bfd911983f4ff;
                cptra_fe_tb = 256'h7dca6154c2510ae1c87b1b422b02b621bb06cac280023894fcff3406af08ee9b;
                cptra_hek_tb = 256'h7dca6154c2510ae1c87b1b422b02b621bb06cac280023894fcff3406af08ee9b; // FIXME unique value?
                           /*256'h7dca6154c2510ae1c87b1b422b02b621bb06cac280023894fcff3406af08ee9b,
                           256'he1dd72419beccddff77c722d992cdcc87e9c7486f56ab406ea608d8c6aeb060c,
                           256'h64cf2785ad1a159147567e39e303370da445247526d95942bf4d7e88057178b0};*/
            end 
            else begin
                cptra_obfkey_tb = 256'h31358e8af34d6ac31c958bbd5c8fb33c334714bffb41700d28b07f11cfe891e7;
                cptra_uds_tb = 512'he4046d05385ab789c6a72866e08350f93f583e2a005ca0faecc32b5cfc323d461c76c107307654db5566a5bd693e227c144516246a752c329056d884daf3c89d;
                cptra_fe_tb = 256'hb32e2b171b63827034ebb0d1909f7ef1d51c5f82c1bb9bc26bc4ac4dccdee835;
                cptra_hek_tb = 256'hb32e2b171b63827034ebb0d1909f7ef1d51c5f82c1bb9bc26bc4ac4dccdee835; // FIXME
            end
            //swizzle the key so it matches the endianness of AES block
            //used for visual inspection of uds/fe/hek flow, manually switching keys and checking both
            for (int dword = 0; dword < $bits(cptra_obf_key)/32; dword++) begin
                cptra_obf_key[dword] = cptra_obfkey_tb[dword];
            end
        end

        for (int dword = 0; dword < `CLP_CSR_HMAC_KEY_DWORDS; dword++) begin
            cptra_csr_hmac_key[dword] = 32'h0b0b0b0b;
        end

        // Run the test stimulus

        soc_ifc_hw_error_wdata = 'h0;
        generic_input_wires = 'h0;
        $display ("\n\n\n\n\n\n");
        repeat(15) @(posedge core_clk);
        $display("CLP: Waiting for cptra_rst_b deassertion\n");

        forever begin
            fork
                begin: STASH_BANK_STDOUT_FLOW
                    // Stash bank STDOUT hooks (0xc1/0xc2) are not gated on
                    // ready_for_mb_processing. RFC #673 allows SoC stash activity
                    // through ROM boot; integration tests preload ICCM and the uC
                    // may request BFM AXI writes before mailbox FW push completes.
                    if (!$test$plusargs("CALIPTRA_TEST_STASH_BANK")) begin
                        forever @(posedge core_clk);
                    end
                    else forever begin
                        @(posedge cptra_rst_b);
                        $display("[stash_bank] BFM: STDOUT handler active\n");
                        while (cptra_rst_b) begin
                            if (ras_test_ctrl.do_stash_bad_pauser_writes) begin
                                write_stash_bank_bad_pauser();
                                generic_input_wires = {32'h0, STASH_BAD_PAUSER_DONE};
                            end
                            else if (ras_test_ctrl.do_stash_post_cptra_lock_writes) begin
                                write_stash_bank_post_cptra_lock();
                                generic_input_wires = {32'h0, STASH_POST_CPTRA_LOCK_DONE};
                            end
                            @(posedge core_clk);
                        end
                    end
                end: STASH_BANK_STDOUT_FLOW
                begin: BOOT_AND_CMD_FLOW
                    boot_and_cmd_flow = process::self();

                    // Repeat this flow after every warm reset
                    @(posedge cptra_rst_b)
                    $display("CLP: Observed cptra_rst_b deassertion\n");

                    if (!SKIP_BRINGUP) begin: DO_BOOT_AND_CMD_FLOW

                    // Fuse download sequence
                    wait(ready_for_fuses == 1);
                    $display ("CLP: Ready for fuse download\n");

                    for (int rpt=0; rpt < 5; rpt++) @(posedge core_clk);

                    $display ("SoC: Writing obfuscated UDS to fuse bank\n");
                    for (int dw=0; dw < `CLP_OBF_UDS_DWORDS; dw++) begin
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_FUSE_UDS_SEED_0 + 4 * dw), .data(cptra_uds_tb[dw]), .resp(wresp), .resp_user(buser));
                    end

                    $display ("SoC: Writing obfuscated Field Entropy to fuse bank\n");
                    for (int dw=0; dw < `CLP_OBF_FE_DWORDS; dw++) begin
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_0 + 4 * dw), .data(cptra_fe_tb[dw]), .resp(wresp), .resp_user(buser));
                    end

                    $display ("SoC: Writing obfuscated HEK seed to fuse bank\n");
                    for (int dw=0; dw < OCP_LOCK_HEK_NUM_DWORDS; dw++) begin
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_FUSE_HEK_SEED_0 + 4 * dw), .data(cptra_hek_tb[dw]), .resp(wresp), .resp_user(buser));
                    end

                    $display ("SoC: Writing SOC Stepping ID to fuse bank\n");
                    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_FUSE_SOC_STEPPING_ID), .data($urandom()), .resp(wresp), .resp_user(buser));

                    $display ("SoC: Writing fuse done register\n");
                    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_FUSE_WR_DONE), .data(32'h00000001), .resp(wresp), .resp_user(buser));

                    // Stash measurement register bank smoke-test hook (RFC #673).
                    // Gated by +CALIPTRA_TEST_STASH_BANK plusarg; happens after
                    // fuses are committed but before BOOTFSM_GO releases the uC,
                    // matching the RFC use case of SoC depositing measurements
                    // before Caliptra ROM finishes booting.
                    if ($test$plusargs("CALIPTRA_TEST_STASH_BANK")) begin
                        if ($test$plusargs("CALIPTRA_TEST_STASH_BANK_CPTRA_LOCK")) begin
                            write_stash_bank_partial();
                        end else if ($test$plusargs("CALIPTRA_TEST_STASH_BANK_RST") && stash_bank_rst_boot_complete) begin
                            $display("[stash_bank] BFM: skipping stash populate (post-cptra_rst_b boot)");
                        end else begin
                            write_stash_bank();
                            if ($test$plusargs("CALIPTRA_TEST_STASH_BANK_RST")) begin
                                stash_bank_rst_boot_complete = 1'b1;
                            end
                            if ($test$plusargs("CALIPTRA_TEST_STASH_BANK_NEG")) begin
                                write_stash_bank_negative();
                            end
                        end
                    end

                    assert (!cptra_error_non_fatal) else begin
                        $error("cptra_error_non_fatal observed during boot up");
                        $finish;
                    end
                    assert (!cptra_error_fatal) else begin
                        $error("cptra_error_fatal observed during boot up");
                        $finish;
                    end

                    if (BootFSM_BrkPoint) begin
                        $write ("SoC: Polling Flow Status...");
                        poll_count = 0;
                        do begin
                            m_axi_bfm_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS), .data(rdata), .resp(rresp), .resp_user(buser));
                            poll_count++;
                        end while(rdata[`SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_LOW] == 1);
                        $display("\n  >>> SoC: Ready for Fuses deasserted after polling %d times\n", poll_count);
                        $display ("SoC: Writing BootGo register\n");
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_BOOTFSM_GO), .data(32'h00000001), .resp(wresp), .resp_user(buser));
                    end
                    else begin
                        $display("SoC: Breakpoint not set; skipping BOOTFSM_GO step\n");
                    end

                    $display ("CLP: ROM Flow in progress...\n");

                    // Test sequence (Mailbox or error handling)
                    wait(ready_for_mb_processing || ras_test_ctrl.error_injection_seen);

                    // Mailbox flow
                    if (ready_for_mb_processing) begin
                        for (int rpt=0; rpt<5; rpt++) @(posedge core_clk);

                        $display ("CLP: Ready for firmware push\n");
                        $write ("SoC: Requesting mailbox lock...");
                        poll_count = 0;
                        do begin
                            m_axi_bfm_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_LOCK), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp), .resp_user(buser));
                            poll_count++;
                        end while (rdata[`MBOX_CSR_MBOX_LOCK_LOCK_LOW] == 1);
                        $display ("\n  >>> SoC: Lock granted after polling %d times\n", poll_count);

                        $display ("SoC: Writing the Command Register\n");
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_CMD), .user(32'hFFFF_FFFF), .data(32'hBA5EBA11), .resp(wresp), .resp_user(buser));

                        $display ("SoC: Writing the Data Length Register\n");
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_DLEN), .user(32'hFFFF_FFFF), .data(FW_NUM_DWORDS*4), .resp(wresp), .resp_user(buser));

                        $display ("SoC: Writing the Firmware into Data-in Register\n");
                        fw_blob = new[FW_NUM_DWORDS];
                        wstrb_array = new[FW_NUM_DWORDS]('{default: {`CALIPTRA_AXI_DATA_WIDTH/8{1'b1}}});
                        for (int dw=0; dw < FW_NUM_DWORDS; dw++)
                            fw_blob[dw] = $urandom();
                        m_axi_bfm_if.axi_write(.addr      (`CLP_MBOX_CSR_MBOX_DATAIN),
                                               .burst     (AXI_BURST_FIXED),
                                               .len       (FW_NUM_DWORDS-1),
                                               .user      (32'hFFFF_FFFF  ),
                                               .data      (fw_blob        ),
                                               .strb      (wstrb_array    ),
                                               .write_user(wuser_array    ),
                                               .resp      (wresp          ),
                                               .resp_user (buser          ));

                        $display ("SoC: Setting the Execute Register\n");
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_EXECUTE), .user(32'hFFFF_FFFF), .data(32'h00000001), .resp(wresp), .resp_user(buser));

                        $display("SoC: Waiting for Response Data availability\n");
                        wait(mailbox_data_avail);

                        $display("SoC: Reading the Status Register...\n");
                        m_axi_bfm_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_STATUS), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp), .resp_user(buser));

                        if (((rdata & `MBOX_CSR_MBOX_STATUS_STATUS_MASK) >> `MBOX_CSR_MBOX_STATUS_STATUS_LOW) == DATA_READY) begin: READ_RESP_DATA
                            $display("SoC: Reading the Data Length Register...\n");
                            m_axi_bfm_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_DLEN), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp), .resp_user(buser));

                            $display("SoC: Reading the Data Out Register\n");
                            for (int xfer4k = 0; xfer4k < rdata; xfer4k += 4096) begin
                                byte_count = (rdata - xfer4k) > 4096 ? 4096 : (rdata - xfer4k);
                                dw_count = byte_count/(`CALIPTRA_AXI_DATA_WIDTH/8) + |byte_count[$clog2(`CALIPTRA_AXI_DATA_WIDTH/8)-1:0];
                                rdata_array = new[dw_count];
                                rresp_array = new[dw_count];
                                ruser_array = new[dw_count];
                                m_axi_bfm_if.axi_read(.addr     (`CLP_MBOX_CSR_MBOX_DATAOUT),
                                                      .burst    (AXI_BURST_FIXED),
                                                      .len      (dw_count-1     ),
                                                      .user     (32'hFFFF_FFFF  ),
                                                      .data     (rdata_array    ),
                                                      .resp     (rresp_array    ),
                                                      .resp_user(ruser_array    ));
                            end
                        end: READ_RESP_DATA

                        $display("SoC: Resetting the Execute Register\n");
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_EXECUTE), .user(32'hFFFF_FFFF), .data(32'h0), .resp(wresp), .resp_user(buser));

                        //Wait for Mailbox flow to be done before toggling generic_input_wires
                        @(negedge core_clk);
                        generic_input_wires = {$urandom, $urandom}; //Toggle wires
                    end

                    if (ras_test_ctrl.error_injection_seen) begin
                        $display("SoC: Waiting to see cptra_error_fatal/non_fatal\n");
                        rv_dma_resp_error = 1'b0;
                    end

                    // Mailbox response flow and RAS functionality
                    forever begin
                        if (cptra_error_fatal_dly_p) begin
                            $display("SoC: Observed cptra_error_fatal; reading Caliptra register\n");
                            m_axi_bfm_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL), .data(rdata), .resp(rresp), .resp_user(buser));
                            if (rdata[`SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_ICCM_ECC_UNC_LOW]) begin
                                generic_input_wires = {32'h0, ICCM_FATAL_OBSERVED};
                            end
                            else if (rdata[`SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_DCCM_ECC_UNC_LOW]) begin
                                generic_input_wires = {32'h0, DCCM_FATAL_OBSERVED};
                            end
                            else if (rdata[`SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_LOW]) begin
                                generic_input_wires = {32'h0, NMI_FATAL_OBSERVED};
                            end
                            else if (rdata[`SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_CRYPTO_ERR_LOW]) begin
                                generic_input_wires = {32'h0, CRYPTO_ERROR_OBSERVED};
                            end
                            else if (rdata[`SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_FSM_ERROR_LOW]) begin // fsm_error bit
                                generic_input_wires = {32'h0, FSM_ERROR_OBSERVED};
                            end
                            else begin
                                generic_input_wires = {32'h0, ERROR_NONE_SET};
                            end
                            // HW ERROR registers are W1C, capture the set bits
                            soc_ifc_hw_error_wdata = rdata;

                            if (soc_ifc_hw_error_wdata) begin
                                $display("SoC: Observed cptra_error_fatal; writing to clear Caliptra register\n");
                                m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL), .data(soc_ifc_hw_error_wdata), .resp(wresp), .resp_user(buser));
                                soc_ifc_hw_error_wdata = '0;
                            end
                            //wait for reset stuff
                            assert_rst_flag_from_fatal = 1;
                            wait(cptra_rst_b == 0);
                        end
                        else if (cptra_error_non_fatal_dly_p) begin
                            $display("SoC: Observed cptra_error_non_fatal; reading Caliptra register\n");
                            m_axi_bfm_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL), .data(rdata), .resp(rresp), .resp_user(buser));
                            if (rdata[`SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_NO_LOCK_LOW]) begin
                                generic_input_wires = {32'h0, PROT_NO_LOCK_NON_FATAL_OBSERVED};
                            end
                            else if (rdata[`SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_PROT_OOO_LOW]) begin
                                generic_input_wires = {32'h0, PROT_OOO_NON_FATAL_OBSERVED};
                            end
                            else if (rdata[`SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL_MBOX_ECC_UNC_LOW]) begin
                                generic_input_wires = {32'h0, MBOX_NON_FATAL_OBSERVED};
                            end
                            else begin
                                generic_input_wires = {32'h0, ERROR_NONE_SET};
                            end
                            // HW ERROR registers are W1C, capture the set bits
                            soc_ifc_hw_error_wdata = rdata;

                            if (soc_ifc_hw_error_wdata) begin
                                $display("SoC: Observed cptra_error_non_fatal; writing to clear Caliptra register\n");
                                m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL), .data(soc_ifc_hw_error_wdata), .resp(wresp), .resp_user(buser));
                                soc_ifc_hw_error_wdata = '0;
                            end
                        end
                        else if (ras_test_ctrl.do_no_lock_access) begin
                            fork
                                begin
                                    $display("SoC: Reading the Data Out Register without lock\n");
                                    dw_count = 1;
                                    rdata_array = new[dw_count];
                                    rresp_array = new[dw_count];
                                    ruser_array = new[dw_count];
                                    m_axi_bfm_if.axi_read(.addr     (`CLP_MBOX_CSR_MBOX_DATAOUT),
                                                          .burst    (AXI_BURST_FIXED),
                                                          .len      (dw_count-1     ),
                                                          .user     (32'hFFFF_FFFF  ),
                                                          .data     (rdata_array    ),
                                                          .resp     (rresp_array    ),
                                                          .resp_user(ruser_array    ));
                                end
                            join
                        end
                        else if (ras_test_ctrl.do_ooo_access) begin
                            fork
                                begin
                                    $write ("SoC: Requesting mailbox lock...");
                                    poll_count = 0;
                                    do begin
                                        m_axi_bfm_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_LOCK), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp), .resp_user(buser));
                                        poll_count++;
                                    end while (rdata[`MBOX_CSR_MBOX_LOCK_LOCK_LOW] == 1);
                                    $display ("\n  >>> SoC: Lock granted after polling %d times\n", poll_count);

                                    $display("SoC: Reading the Data Length Register...\n");
                                    m_axi_bfm_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_DLEN), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp), .resp_user(buser));

                                    $display("SoC: Reading the Data Out Register\n");
                                    dw_count = 1;
                                    rdata_array = new[dw_count];
                                    rresp_array = new[dw_count];
                                    ruser_array = new[dw_count];
                                    m_axi_bfm_if.axi_read(.addr     (`CLP_MBOX_CSR_MBOX_DATAOUT),
                                                          .burst    (AXI_BURST_FIXED),
                                                          .len      (dw_count-1     ),
                                                          .user     (32'hFFFF_FFFF  ),
                                                          .data     (rdata_array    ),
                                                          .resp     (rresp_array    ),
                                                          .resp_user(ruser_array    ));
                                end
                            join
                        end
                        else if (ras_test_ctrl.reset_generic_input_wires) begin
                            `ifdef VERILATOR
                            generic_input_wires = {32'h72746C76, ERROR_NONE_SET}; /* 32'h72746c76 is the big-endian ASCII representation of 'vltr' (r t l v) */
                            `else
                            generic_input_wires = {32'h0, ERROR_NONE_SET};
                            `endif
                        end
                        else if (rv_dma_resp_error) begin
                            generic_input_wires = {32'h0, DMA_ERROR_OBSERVED};
                            rv_dma_resp_error = 1'b0;
                        end
                        else if (mailbox_data_avail) begin
                            $display("SoC: Reading the Data Length Register\n");
                            m_axi_bfm_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_DLEN), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp), .resp_user(buser));

                            $display("SoC: Reading the Data Out Register\n");
                            for (int xfer4k = 0; xfer4k < rdata; xfer4k += 4096) begin
                                byte_count = (rdata - xfer4k) > 4096 ? 4096 : (rdata - xfer4k);
                                dw_count = byte_count/(`CALIPTRA_AXI_DATA_WIDTH/8) + |byte_count[$clog2(`CALIPTRA_AXI_DATA_WIDTH/8)-1:0];
                                rdata_array = new[dw_count];
                                rresp_array = new[dw_count];
                                ruser_array = new[dw_count];
                                m_axi_bfm_if.axi_read(.addr     (`CLP_MBOX_CSR_MBOX_DATAOUT),
                                                      .burst    (AXI_BURST_FIXED ),
                                                      .len      (dw_count-1      ),
                                                      .user     (32'hFFFF_FFFF   ),
                                                      .data     (rdata_array     ),
                                                      .resp     (rresp_array     ),
                                                      .resp_user(ruser_array     ));
                            end

                            $display ("SoC: Writing the Mbox Status Register\n");
                            m_axi_bfm_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_STATUS), .user(32'hFFFF_FFFF), .data(32'h1), .resp(wresp), .resp_user(buser));
                        end
                        @(posedge core_clk);
                    end
                    end: DO_BOOT_AND_CMD_FLOW
                    else begin: SKIP_BOOT_AND_CMD_FLOW
                        forever @(posedge core_clk);
                    end: SKIP_BOOT_AND_CMD_FLOW
                end: BOOT_AND_CMD_FLOW
                begin: CLK_GATE_FLOW
                    wait(cycleCnt_smpl_en);
                    for (int rpt=0; rpt<2000; rpt++) @(negedge core_clk);

                    if (int_flag) begin
                        $display("SoC (clk_gate_flow): Forcing soft_int = 1. cycleCnt [%d]\n", cycleCnt);
                        force `CPTRA_TOP_PATH.soft_int = 1'b1;
                        for (int rpt=0; rpt<2; rpt++) @(negedge core_clk);
                        $display("SoC (clk_gate_flow): Releasing soft_int = 1. cycleCnt [%d]\n", cycleCnt);
                        release `CPTRA_TOP_PATH.soft_int;
                    end

                    for (int rpt=0; rpt<5000; rpt++) @(negedge core_clk);

                    if (int_flag) begin
                        $display("SoC (clk_gate_flow): Forcing timer_int = 1. cycleCnt [%d]\n", cycleCnt);
                        force `CPTRA_TOP_PATH.timer_int = 1'b1;
                        for (int rpt=0; rpt<2; rpt++) @(negedge core_clk);
                        $display("SoC (clk_gate_flow): Releasing timer_int = 1. cycleCnt [%d]\n", cycleCnt);
                        release `CPTRA_TOP_PATH.timer_int;
                    end

                    for (int rpt=0; rpt<8000; rpt++) @(negedge core_clk);

                    if (int_flag) begin
                        $display("SoC (clk_gate_flow): Forcing soft_int = 1. cycleCnt [%d]\n", cycleCnt);
                        force `CPTRA_TOP_PATH.soft_int = 1'b1;
                        for (int rpt=0; rpt<2; rpt++) @(negedge core_clk);
                        $display("SoC (clk_gate_flow): Releasing soft_int = 1. cycleCnt [%d]\n", cycleCnt);
                        release `CPTRA_TOP_PATH.soft_int;
                    end

                    wait(cptra_rst_b == 0);
                end: CLK_GATE_FLOW
                begin: RESET_FLOW
                    @(negedge cptra_rst_b);
                    $display("CLP: Observed cptra_rst_b assertion\n");
//                    disable BOOT_AND_CMD_FLOW; 
                    if (boot_and_cmd_flow != null) boot_and_cmd_flow.kill();
                    assert_rst_flag_from_fatal = 1'b0;
                    m_axi_bfm_if.rst_mgr();
                end: RESET_FLOW
            join_any
        end
    end

    assign assert_rst_flag   =   assert_rst_flag_from_service ||   assert_rst_flag_from_fatal;
    assign deassert_rst_flag = deassert_rst_flag_from_service || deassert_rst_flag_from_fatal;
    always @(posedge core_clk) begin
        //Reset/pwrgood assertion during runtime
        if (cycleCnt == 15 || deassert_hard_rst_flag) begin
            $display ("SoC: Asserting cptra_pwrgood and breakpoint. cycleCnt [%d] deassert_hard_rst_flag[%d]\n", cycleCnt, deassert_hard_rst_flag);
            //assert power good
            cptra_pwrgood <= 1'b1;
        end
        else if (cycleCnt == 20 || deassert_rst_flag) begin
            $display ("SoC: De-Asserting cptra_rst_b. cycleCnt [%d] deassert_rst_flag[%d]\n", cycleCnt, deassert_rst_flag);
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
    end

`define RV_INST `CPTRA_TOP_PATH.rvtop
`define RV_IDMA_RESP_INST `CPTRA_TOP_PATH.responder_inst[`CALIPTRA_SLAVE_SEL_IDMA]
`define RV_DDMA_RESP_INST `CPTRA_TOP_PATH.responder_inst[`CALIPTRA_SLAVE_SEL_DDMA]
task force_ahb_dma_read(input logic [31:0] address);
    while(`RV_INST.dma_hsel) @(posedge core_clk);

    // Disable DMA-related hreadyout assertions before forcing signals
`ifdef CLP_ASSERT_ON
    `ifndef VERILATOR
    $assertoff(0, `CPTRA_TOP_PATH.ahb_lite_bus_i.u_ahb_lite_address_decoder.rspr_ready_loop[`CALIPTRA_SLAVE_SEL_DDMA].rspr_ready_do_assert.rspr_ready_rv_dma_merge.AHB_RSPR_DFLT_READY);
    $assertoff(0, `CPTRA_TOP_PATH.ahb_lite_bus_i.u_ahb_lite_address_decoder.rspr_ready_loop[`CALIPTRA_SLAVE_SEL_IDMA].rspr_ready_do_assert.rspr_ready_rv_dma_merge.AHB_RSPR_DFLT_READY);
    `endif // VERILATOR
`endif // CLP_ASSERT_ON

    force `RV_IDMA_RESP_INST.hreadyout = 1'b0;
    force `RV_DDMA_RESP_INST.hreadyout = 1'b0;

    force `RV_INST.dma_haddr = address;
    force `RV_INST.dma_hsize = 3'b010; // 4-bytes
    force `RV_INST.dma_hwrite = 1'b0;
    force `RV_INST.dma_hwdata = '0;
    force `RV_INST.dma_hreadyin = 1'b1;
    force `RV_INST.dma_hsel = 1'b1;
    force `RV_INST.dma_htrans = 2'b10;

    // Wait for command to be accepted
    do @(posedge core_clk); while(!`RV_INST.dma_hreadyout);
    force   `RV_INST.dma_htrans = 2'b00;
    // Wait for response to be provided
    do @(posedge core_clk); while(!`RV_INST.dma_hreadyout);
    $display("[%t] AHB DMA FORCE READ: Address 0x%x Data 0x%x Resp 0x%x", $time, address, `RV_INST.dma_hrdata, `RV_INST.dma_hresp);
    if (`RV_INST.dma_hresp)
        rv_dma_resp_error = 1'b1;

    force `RV_INST.dma_hsel = 1'b0; // Reset to the expected value before releasing force
    force `RV_IDMA_RESP_INST.hreadyout = `RV_INST.dma_hreadyout; // Reset to the expected value before releasing force
    force `RV_DDMA_RESP_INST.hreadyout = `RV_INST.dma_hreadyout; // Reset to the expected value before releasing force

    release `RV_IDMA_RESP_INST.hreadyout;
    release `RV_DDMA_RESP_INST.hreadyout;

    release `RV_INST.dma_htrans;
    release `RV_INST.dma_haddr;
    release `RV_INST.dma_hsize;
    release `RV_INST.dma_hwrite;
    release `RV_INST.dma_hwdata;
    release `RV_INST.dma_hsel;
    release `RV_INST.dma_hreadyin;

    #1ps;

    // Re-enable DMA-related hreadyout assertions after releasing signals
`ifdef CLP_ASSERT_ON
    `ifndef VERILATOR
    $asserton(0, `CPTRA_TOP_PATH.ahb_lite_bus_i.u_ahb_lite_address_decoder.rspr_ready_loop[`CALIPTRA_SLAVE_SEL_DDMA].rspr_ready_do_assert.rspr_ready_rv_dma_merge.AHB_RSPR_DFLT_READY);
    $asserton(0, `CPTRA_TOP_PATH.ahb_lite_bus_i.u_ahb_lite_address_decoder.rspr_ready_loop[`CALIPTRA_SLAVE_SEL_IDMA].rspr_ready_do_assert.rspr_ready_rv_dma_merge.AHB_RSPR_DFLT_READY);
    `endif // VERILATOR
`endif // CLP_ASSERT_ON
endtask

task force_ahb_dma_loop_read(input logic [31:0] start_addr, input logic [19:0] count);
    automatic logic [31:0] addr;
    addr = start_addr;
    $display("[%t] AHB DMA FORCE LOOP READ: Start Address 0x%x Count 0x%x", $time, addr, count);
    if ($isunknown(start_addr) || $isunknown(addr))
        $error("[%t] Unknown signal found: start_addr 0x%x addr 0x%x", $time, start_addr, addr);
    repeat(count) begin
        force_ahb_dma_read(addr);
        addr += 4;
    end
endtask

initial begin
    forever @(posedge core_clk) begin
        if (ras_test_ctrl.dccm_read_burst.start)
            force_ahb_dma_loop_read(ras_test_ctrl.dccm_read_burst.addr, ras_test_ctrl.dccm_read_burst.count);
        if (ras_test_ctrl.iccm_read_burst.start)
            force_ahb_dma_loop_read(ras_test_ctrl.iccm_read_burst.addr, ras_test_ctrl.iccm_read_burst.count);
    end
end

//==========================================================================
// Stash measurement register bank smoke-test driver (RFC #673)
//
// Common slot-data pattern used by both the BFM (writes) and the C tests
// (reads): dword_value = (slot_idx << 24) | (dword_idx << 8) | 0xA5.
// Pattern is deterministic and self-describing so a failed comparison in
// the C test points at the (slot, dword) where the mismatch occurred.
//
// Gated by +CALIPTRA_TEST_STASH_BANK at the call site (above). In
// CALIPTRA_MODE_SUBSYSTEM builds, only slot 0 is exercised because slots
// 1..7 are tied off in soc_ifc_top.sv.
//==========================================================================
// Custom AXI USER value programmed into CPTRA_MBOX_VALID_AXI_USER[0] for stash
// access. Picked to be distinct from the default 0xFFFF_FFFF so the test
// specifically exercises the SoC-programmed register-lock path (source 2 of
// soc_ifc_top.sv::valid_mbox_users resolution) and not the default fallback.
// Distinct from all other in-test sentinel values (0xDEAD_BEEF, 0xBAAD_F00D,
// 0xCAFE_BABE, 0xCAFE_F00D).
localparam logic [31:0] STASH_PAUSER = 32'hAAAA_BBBB;

// Slot 0 dword written with CPTRA_DEF_MBOX_VALID_AXI_USER rather than
// STASH_PAUSER, covering the second of the two PAUSER match terms in
// soc_ifc_top.sv. Every CPTRA_MBOX_VALID_AXI_USER entry is programmed and locked
// away from the default below, so this dword lands only if the stash filter
// accepts the default user on its own. The C tests already compare every dword
// against the pattern, so this needs no separate check.
localparam int STASH_DEFAULT_USER_DWORD = 25;

task automatic write_stash_bank();
    int num_slots;
    int slot_idx;
    int dword_idx;
    int user_idx;
    logic [31:0] data_val;
    logic [31:0] write_user;
    axi_resp_e   local_wresp;
    logic [`CALIPTRA_AXI_USER_WIDTH-1:0] local_buser;

    $display("[stash_bank] BFM: starting stash bank write sequence");

    // 1. Program and lock all five mailbox AXI USER table entries. Entry 0 gets
    //    STASH_PAUSER; entries 1..4 get distinct values that no write in this
    //    test uses. With every entry locked, valid_mbox_users[] never resolves to
    //    CPTRA_DEF_MBOX_VALID_AXI_USER, which is what lets step 2 exercise the
    //    default user as a match in its own right.
    //    The setup writes themselves use 0xFFFF_FFFF; the
    //    CPTRA_MBOX_VALID_AXI_USER / CPTRA_MBOX_AXI_USER_LOCK registers are
    //    not PAUSER-gated, so any value works for these setup writes.
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0),
                                  .user(32'hFFFF_FFFF), .data(STASH_PAUSER),
                                  .resp(local_wresp), .resp_user(local_buser));
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0),
                                  .user(32'hFFFF_FFFF), .data(32'h0000_0001),
                                  .resp(local_wresp), .resp_user(local_buser));
    for (user_idx = 1; user_idx < 5; user_idx++) begin
        m_axi_bfm_if.axi_write_single(
            .addr(`CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0 + 4*user_idx),
            .user(32'hFFFF_FFFF), .data(32'hAAAA_BBB0 | user_idx[3:0]),
            .resp(local_wresp), .resp_user(local_buser));
        m_axi_bfm_if.axi_write_single(
            .addr(`CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0 + 4*user_idx),
            .user(32'hFFFF_FFFF), .data(32'h0000_0001),
            .resp(local_wresp), .resp_user(local_buser));
    end
    $display("[stash_bank] BFM: CPTRA_MBOX_VALID_AXI_USER[0] = 0x%08x, all 5 entries programmed and locked", STASH_PAUSER);

`ifdef CALIPTRA_MODE_SUBSYSTEM
    num_slots = 1;
`else
    // Passive mode: exercise every slot supported by the RTL (8 total).
    num_slots = 8;
`endif

    // 2. Populate slots 0..num_slots-1 with deterministic patterns. Slot 0's
    //    STASH_DEFAULT_USER_DWORD goes in under the default AXI USER, covering
    //    the mailbox PAUSER set's default-user member (RFC 673 §4.1).
    for (slot_idx = 0; slot_idx < num_slots; slot_idx++) begin
        for (dword_idx = 0; dword_idx < 26; dword_idx++) begin
            data_val = (slot_idx[7:0] << 24) | (dword_idx[15:0] << 8) | 8'hA5;
            write_user = ((slot_idx == 0) && (dword_idx == STASH_DEFAULT_USER_DWORD)) ?
                         32'hFFFF_FFFF : STASH_PAUSER;
            m_axi_bfm_if.axi_write_single(
                .addr(`CLP_SOC_IFC_REG_STASH_BANK_SLOT_DATA_0 + 4*(slot_idx*26 + dword_idx)),
                .user(write_user), .data(data_val),
                .resp(local_wresp), .resp_user(local_buser));
        end
        $display("[stash_bank] BFM: slot %0d populated (26 dwords)", slot_idx);
    end
    $display("[stash_bank] BFM: slot 0 dword %0d written with default AXI USER 0xFFFF_FFFF",
             STASH_DEFAULT_USER_DWORD);

    // 3b. Negative-path (CALIPTRA_TEST_STASH_BANK_NEG): attempt to clear a
    //     randomly selected lock bit by writing 0 to that bit in
    //     STASH_BANK_SOC_LOCK (wr_data = ~(1 << slot)). W1S semantics must
    //     ignore zero data; slot_locked mirror unchanged.
    //     Must run before STASH_END_STASH (soc_ifc_top gates SOC_LOCK swwe
    //     once end_stash is set).
    if ($test$plusargs("CALIPTRA_TEST_STASH_BANK_NEG")) begin
        int unlock_attempt_slot;
        logic [31:0] unlock_attempt_data;
        unlock_attempt_slot = $urandom_range(num_slots - 1, 0);
        // W1S: only 1-bits take effect; bit unlock_attempt_slot is 0 in wr_data.
        unlock_attempt_data = ~(32'h1 << unlock_attempt_slot);
        $display("[stash_bank] BFM: attempting STASH_BANK_SOC_LOCK write of 0x%08x to clear slot %0d (W1S - expected to be ignored)",
                 unlock_attempt_data, unlock_attempt_slot);
        m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_SOC_LOCK),
                                      .user(STASH_PAUSER), .data(unlock_attempt_data),
                                      .resp(local_wresp), .resp_user(local_buser));

        // 3c. Post-SOC-lock, pre-end_stash: rewrite a locked slot's data.
        //     end_stash is not yet set, so rejection must be due to
        //     STASH_BANK_SOC_LOCK[slot] only (not end_stash).
        begin
            int soc_lock_rewrite_slot;
            soc_lock_rewrite_slot = $urandom_range(num_slots - 1, 0);
            $display("[stash_bank] BFM: attempting pre-end_stash rewrite of slot %0d dword 0 with 0xFEED_FACE (SOC_LOCK only - expected to be dropped)",
                     soc_lock_rewrite_slot);
            m_axi_bfm_if.axi_write_single(
                .addr(`CLP_SOC_IFC_REG_STASH_BANK_SLOT_DATA_0 + 4*(soc_lock_rewrite_slot*26 + 0)),
                .user(STASH_PAUSER), .data(32'hFEED_FACE),
                .resp(local_wresp), .resp_user(local_buser));
        end
    end

`ifdef CALIPTRA_MODE_SUBSYSTEM
    // 3. Subsystem mode implements slot 0 only. Write all eight lock bits so the
    //    C test can confirm STASH_BANK_STATUS.slot_locked reports 0x01 - an
    //    unimplemented slot is never presentable as populated.
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_SOC_LOCK),
                                  .user(STASH_PAUSER), .data(32'h0000_00FF),
                                  .resp(local_wresp), .resp_user(local_buser));
    $display("[stash_bank] BFM (subsystem): STASH_BANK_SOC_LOCK = 0xFF written; only bit 0 is implemented");

    // 3a. Subsystem-mode tie-off check: attempt to write slot 1 dword 0
    // with a valid PAUSER and no end_stash asserted yet. The
    // soc_ifc_top.sv glue ties swwel high for slot_idx > 0 in subsystem
    // builds, so this write must be dropped at the RTL level. The C test
    // verifies the value is still 0.
    $display("[stash_bank] BFM (subsystem): attempting slot 1 dword 0 write (must be dropped by tie-off)");
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_SLOT_DATA_0 + 4*(1*26 + 0)),
                                  .user(STASH_PAUSER), .data(32'hCAFE_F00D),
                                  .resp(local_wresp), .resp_user(local_buser));
`else
    // 3. Lock the populated slots via STASH_BANK_SOC_LOCK (W1S).
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_SOC_LOCK),
                                  .user(STASH_PAUSER),
                                  .data((32'h1 << num_slots) - 32'h1),
                                  .resp(local_wresp), .resp_user(local_buser));
    $display("[stash_bank] BFM: STASH_BANK_SOC_LOCK = 0x%0h", (1 << num_slots) - 1);
`endif

    // 4. Assert STASH_END_STASH (W1S, sticky).
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_END_STASH),
                                  .user(STASH_PAUSER), .data(32'h0000_0001),
                                  .resp(local_wresp), .resp_user(local_buser));
    $display("[stash_bank] BFM: STASH_END_STASH asserted - stash bank closed for SoC writes");
endtask

//==========================================================================
// Invalid-PAUSER overwrite attempt for smoke_test_stash_bank step D.
// Populates every RTL slot with random data using an AXI USER that does not
// match valid_mbox_users[]; all writes must be silently dropped.
//==========================================================================
localparam logic [31:0] INVALID_STASH_PAUSER = 32'hCAFE_BABE;

task automatic write_stash_bank_bad_pauser();
    int num_slots;
    int slot_idx;
    int dword_idx;
    logic [31:0] data_val;
    axi_resp_e   local_wresp;
    logic [`CALIPTRA_AXI_USER_WIDTH-1:0] local_buser;

`ifdef CALIPTRA_MODE_SUBSYSTEM
    num_slots = 1;
`else
    num_slots = 8;
`endif

    $display("[stash_bank] BFM: attempting random overwrite of %0d slot(s) with invalid PAUSER 0x%08x (expected to be silently dropped)",
             num_slots, INVALID_STASH_PAUSER);
    for (slot_idx = 0; slot_idx < num_slots; slot_idx++) begin
        for (dword_idx = 0; dword_idx < 26; dword_idx++) begin
            data_val = $urandom();
            m_axi_bfm_if.axi_write_single(
                .addr(`CLP_SOC_IFC_REG_STASH_BANK_SLOT_DATA_0 + 4*(slot_idx*26 + dword_idx)),
                .user(INVALID_STASH_PAUSER), .data(data_val),
                .resp(local_wresp), .resp_user(local_buser));
        end
    end
    $display("[stash_bank] BFM: invalid-PAUSER random overwrite sequence complete");
endtask

//==========================================================================
// Negative-path additional ops for smoke_test_stash_bank_negative.
// Runs after write_stash_bank() completes. Attempts (a) post-lock rewrite
// of slot 0 dword 0, (b) a write with a mismatched AXI USER, (c) a write
// of 0 to STASH_END_STASH after end_stash is latched, (d) a SoC write to
// STASH_BANK_CPTRA_LOCK, and (e) SoC reads of all three write-only lock
// registers. All must be silently dropped, ignored, or read as 0; the C
// test verifies uC-side behavior.
//==========================================================================
task automatic write_stash_bank_negative();
    axi_resp_e   local_wresp;
    axi_resp_e   local_rresp;
    logic [31:0] local_rdata;
    logic [31:0] local_status;
    logic [`CALIPTRA_AXI_USER_WIDTH-1:0] local_buser;

    // (a) Post-end_stash rewrite: uses the valid stash PAUSER so rejection is
    //     attributable to STASH_BANK_SOC_LOCK[0] and/or end_stash (step 3c in
    //     write_stash_bank() already covers SOC_LOCK-only rejection before
    //     end_stash is asserted).
    $display("[stash_bank] BFM: attempting illegal post-lock rewrite of slot 0 dword 0 (expected to be silently dropped)");
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_SLOT_DATA_0),
                                  .user(STASH_PAUSER), .data(32'hDEAD_BEEF),
                                  .resp(local_wresp), .resp_user(local_buser));

    // (b) Bad-PAUSER write: 0xCAFE_BABE matches none of the five locked
    //     valid_mbox_users[] entries (0xAAAA_BBBB, 0xAAAA_BBB1..4) and is not
    //     CPTRA_DEF_MBOX_VALID_AXI_USER, so the stash PAUSER filter must drop
    //     this write.
    $display("[stash_bank] BFM: attempting write with mismatched AXI USER (expected to be silently dropped)");
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_SLOT_DATA_0 + 4*26),
                                  .user(32'hCAFE_BABE), .data(32'hBAAD_F00D),
                                  .resp(local_wresp), .resp_user(local_buser));

    // (c) Attempt to clear STASH_END_STASH by writing 0 after it is already
    //     latched. W1S ignores zero data; end_stash mirror must stay set.
    $display("[stash_bank] BFM: attempting STASH_END_STASH write of 0 (W1S - expected to be ignored)");
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_END_STASH),
                                  .user(STASH_PAUSER), .data(32'h0000_0000),
                                  .resp(local_wresp), .resp_user(local_buser));

    // (d) SoC write to STASH_BANK_CPTRA_LOCK must be dropped (Caliptra-only;
    //     soc_ifc_top.sv gates swwe on ~soc_req).
    $display("[stash_bank] BFM: attempting SoC write to STASH_BANK_CPTRA_LOCK (expected to be silently dropped)");
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK),
                                  .user(STASH_PAUSER), .data(32'h0000_0001),
                                  .resp(local_wresp), .resp_user(local_buser));
    m_axi_bfm_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_STATUS),
                                  .user(STASH_PAUSER), .data(local_status),
                                  .resp(local_rresp), .resp_user(local_buser));
    if (local_status[`SOC_IFC_REG_STASH_BANK_STATUS_CPTRA_LOCK_LOW]) begin
        $error("[stash_bank] BFM: SoC write to STASH_BANK_CPTRA_LOCK landed (STATUS=0x%08x)", local_status);
    end

    // (e) All three lock registers are write-only; SoC reads must return 0.
    $display("[stash_bank] BFM: reading write-only lock registers from SoC (expect 0)");
    m_axi_bfm_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_SOC_LOCK),
                                  .user(STASH_PAUSER), .data(local_rdata),
                                  .resp(local_rresp), .resp_user(local_buser));
    if (local_rdata != 32'h0)
        $error("[stash_bank] BFM: STASH_BANK_SOC_LOCK SoC read = 0x%08x (expected 0)", local_rdata);
    m_axi_bfm_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_STASH_END_STASH),
                                  .user(STASH_PAUSER), .data(local_rdata),
                                  .resp(local_rresp), .resp_user(local_buser));
    if (local_rdata != 32'h0)
        $error("[stash_bank] BFM: STASH_END_STASH SoC read = 0x%08x (expected 0)", local_rdata);
    m_axi_bfm_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_CPTRA_LOCK),
                                  .user(STASH_PAUSER), .data(local_rdata),
                                  .resp(local_rresp), .resp_user(local_buser));
    if (local_rdata != 32'h0)
        $error("[stash_bank] BFM: STASH_BANK_CPTRA_LOCK SoC read = 0x%08x (expected 0)", local_rdata);
endtask

//==========================================================================
// Partial stash bank populate for smoke_test_stash_bank_cptra_lock.
// Only slot 0 dwords 0..9 are written; only STASH_BANK_SOC_LOCK[0] is set.
// Slots 1..7 remain zero and are not SOC-locked before end_stash.
//==========================================================================
localparam int STASH_PARTIAL_SLOT         = 0;
localparam int STASH_PARTIAL_DWORDS       = 10;
localparam int STASH_SOC_UNLOCKED_SLOT    = 1;
localparam logic [31:0] STASH_POST_CPTRA_SLOT0_DATA = 32'hC0FFEE00;
localparam logic [31:0] STASH_POST_CPTRA_SLOT1_DATA = 32'hC0FFEE01;
localparam logic [31:0] STASH_PARTIAL_EXPECTED_STATUS = 32'h0000_0301;

task automatic write_stash_bank_partial();
    int dword_idx;
    logic [31:0] data_val;
    axi_resp_e   local_wresp;
    logic [`CALIPTRA_AXI_USER_WIDTH-1:0] local_buser;

    $display("[stash_bank] BFM: starting partial stash bank write sequence");

    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_MBOX_VALID_AXI_USER_0),
                                  .user(32'hFFFF_FFFF), .data(STASH_PAUSER),
                                  .resp(local_wresp), .resp_user(local_buser));
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_MBOX_AXI_USER_LOCK_0),
                                  .user(32'hFFFF_FFFF), .data(32'h0000_0001),
                                  .resp(local_wresp), .resp_user(local_buser));

    for (dword_idx = 0; dword_idx < STASH_PARTIAL_DWORDS; dword_idx++) begin
        data_val = (STASH_PARTIAL_SLOT[7:0] << 24) | (dword_idx[15:0] << 8) | 8'hA5;
        m_axi_bfm_if.axi_write_single(
            .addr(`CLP_SOC_IFC_REG_STASH_BANK_SLOT_DATA_0 + 4*(STASH_PARTIAL_SLOT*26 + dword_idx)),
            .user(STASH_PAUSER), .data(data_val),
            .resp(local_wresp), .resp_user(local_buser));
    end
    $display("[stash_bank] BFM: slot %0d partially populated (%0d of 26 dwords)", STASH_PARTIAL_SLOT, STASH_PARTIAL_DWORDS);

    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_SOC_LOCK),
                                  .user(STASH_PAUSER), .data(32'h0000_0001),
                                  .resp(local_wresp), .resp_user(local_buser));
    $display("[stash_bank] BFM: STASH_BANK_SOC_LOCK = 0x01 (slot 0 only)");

    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_END_STASH),
                                  .user(STASH_PAUSER), .data(32'h0000_0001),
                                  .resp(local_wresp), .resp_user(local_buser));
    $display("[stash_bank] BFM: STASH_END_STASH asserted");
endtask

//==========================================================================
// Post-CPTRA_LOCK negative writes for smoke_test_stash_bank_cptra_lock.
// Triggered by uC via STDOUT 0xc2 after firmware asserts CPTRA_LOCK.
//==========================================================================
task automatic write_stash_bank_post_cptra_lock();
    axi_resp_e   local_wresp;
    axi_resp_e   local_rresp;
    logic [31:0] local_status;
    logic [`CALIPTRA_AXI_USER_WIDTH-1:0] local_buser;

    $display("[stash_bank] BFM: post-CPTRA_LOCK negative write sequence");

    // (a) Write to SOC-unlocked slot 1 - must drop due to CPTRA_LOCK.
    $display("[stash_bank] BFM: attempting write to SOC-unlocked slot %0d dword 0 (CPTRA_LOCK - expected dropped)",
             STASH_SOC_UNLOCKED_SLOT);
    m_axi_bfm_if.axi_write_single(
        .addr(`CLP_SOC_IFC_REG_STASH_BANK_SLOT_DATA_0 + 4*(STASH_SOC_UNLOCKED_SLOT*26 + 0)),
        .user(STASH_PAUSER), .data(STASH_POST_CPTRA_SLOT1_DATA),
        .resp(local_wresp), .resp_user(local_buser));

    // (b) Write to partially populated locked slot 0 - must drop due to CPTRA_LOCK.
    $display("[stash_bank] BFM: attempting rewrite of slot %0d dword 5 (CPTRA_LOCK - expected dropped)",
             STASH_PARTIAL_SLOT);
    m_axi_bfm_if.axi_write_single(
        .addr(`CLP_SOC_IFC_REG_STASH_BANK_SLOT_DATA_0 + 4*(STASH_PARTIAL_SLOT*26 + 5)),
        .user(STASH_PAUSER), .data(STASH_POST_CPTRA_SLOT0_DATA),
        .resp(local_wresp), .resp_user(local_buser));

    // (c) SoC write to STASH_BANK_SOC_LOCK - gated by CPTRA_LOCK (and end_stash).
    $display("[stash_bank] BFM: attempting SoC write to STASH_BANK_SOC_LOCK (CPTRA_LOCK - expected dropped)");
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_SOC_LOCK),
                                  .user(STASH_PAUSER), .data(32'h0000_00FE),
                                  .resp(local_wresp), .resp_user(local_buser));

    // (d) SoC write to STASH_END_STASH - gated by CPTRA_LOCK.
    $display("[stash_bank] BFM: attempting SoC write to STASH_END_STASH (CPTRA_LOCK - expected dropped)");
    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_STASH_END_STASH),
                                  .user(STASH_PAUSER), .data(32'h0000_0001),
                                  .resp(local_wresp), .resp_user(local_buser));

    m_axi_bfm_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_STASH_BANK_STATUS),
                                  .user(STASH_PAUSER), .data(local_status),
                                  .resp(local_rresp), .resp_user(local_buser));
    if (local_status != STASH_PARTIAL_EXPECTED_STATUS) begin
        $error("[stash_bank] BFM: post-CPTRA_LOCK writes changed STATUS (got 0x%08x, expected 0x%08x)",
               local_status, STASH_PARTIAL_EXPECTED_STATUS);
    end
    $display("[stash_bank] BFM: post-CPTRA_LOCK negative sequence complete (STATUS=0x%08x)", local_status);
endtask

initial begin
    forever @(posedge cptra_rst_b) begin
        if($test$plusargs("SOC_WRITE_RST")) begin
            fork
                begin
                    assert (`CPTRA_TOP_PATH.cptra_noncore_rst_b == 0) else begin
                        $display("* TEST FAILED");
                        $error("cptra_noncore_rst_b deasserted for the SoC access under reset test");
                        $finish;
                    end
                    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0), .user(32'hFFFF_FFFF), .data(32'hBAADB000), .resp(wresp), .resp_user(buser));
                    m_axi_bfm_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp), .resp_user(buser));

                    if (rdata != 32'hBAADB000) begin
                        $display("* TEST FAILED");
                        $error($sformatf("SoC write on reset failed! Expected to read back: 0x%x. Got: 0x%x.", 32'hBAADB000, rdata));
                        $finish;
                    end

                    $display("* TEST PASSED");
                    $finish;
                end
            join
        end
    end
end

endmodule
