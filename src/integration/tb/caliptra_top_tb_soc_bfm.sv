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
    input  logic [0:`CLP_OBF_KEY_DWORDS-1][31:0]          cptra_obf_key_tb,

    axi_if m_axi_bfm_if,

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

    // AXI request signals
    axi_resp_e wresp, rresp;
    logic [`CALIPTRA_AXI_DATA_WIDTH-1:0] wdata, rdata;
    logic [`CALIPTRA_AXI_DATA_WIDTH/8-1:0] wstrb_array[];
    logic [`CALIPTRA_AXI_DATA_WIDTH-1:0] rdata_array[];
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

    initial begin
        cptra_pwrgood = 1'b0;
        BootFSM_BrkPoint = 1'b1; //Set to 1 even before anything starts
        cptra_rst_b = 1'b0;
        assert_rst_flag_from_fatal = 1'b0;
        m_axi_bfm_if.rst_mgr();

`ifndef VERILATOR
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
        end
        else begin
            if ($test$plusargs("SECOND_DOE_KAT")) begin
                //Key for DOE
                cptra_obfkey_tb = 256'he1dd72419beccddff77c722d992cdcc87e9c7486f56ab406ea608d8c6aeb060c;
                cptra_uds_tb = 512'h32cd8a75b5e515bd7b0fe37a6de144696aeedb1f5e03225a71fc690f5b004ff593794db7a99ced97c376385149c4ecafd3afd70cb657a6f6434bfd911983f4ff;
                cptra_fe_tb = 256'h7dca6154c2510ae1c87b1b422b02b621bb06cac280023894fcff3406af08ee9b;
                           /*256'h7dca6154c2510ae1c87b1b422b02b621bb06cac280023894fcff3406af08ee9b,
                           256'he1dd72419beccddff77c722d992cdcc87e9c7486f56ab406ea608d8c6aeb060c,
                           256'h64cf2785ad1a159147567e39e303370da445247526d95942bf4d7e88057178b0};*/
            end 
            else begin
                cptra_obfkey_tb = 256'h31358e8af34d6ac31c958bbd5c8fb33c334714bffb41700d28b07f11cfe891e7;
                cptra_uds_tb = 512'he4046d05385ab789c6a72866e08350f93f583e2a005ca0faecc32b5cfc323d461c76c107307654db5566a5bd693e227c144516246a752c329056d884daf3c89d;
                cptra_fe_tb = 256'hb32e2b171b63827034ebb0d1909f7ef1d51c5f82c1bb9bc26bc4ac4dccdee835;
            end
            //swizzle the key so it matches the endianness of AES block
            //used for visual inspection of uds/fe flow, manually switching keys and checking both
            for (int dword = 0; dword < $bits(cptra_obf_key)/32; dword++) begin
                cptra_obf_key[dword] = cptra_obfkey_tb[dword];
            end
        end

        for (int dword = 0; dword < `CLP_CSR_HMAC_KEY_DWORDS; dword++) begin
            cptra_csr_hmac_key[dword] = '1; //FIXME
        end

        // Run the test stimulus

        soc_ifc_hw_error_wdata = 'h0;
        generic_input_wires = 'h0;
        $display ("\n\n\n\n\n\n");
        repeat(15) @(posedge core_clk);
        $display("CLP: Waiting for cptra_rst_b deassertion\n");

        forever begin
            fork
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
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_FUSE_UDS_SEED_0 + 4 * dw), .data(cptra_uds_tb[dw]), .resp(wresp));
                    end

                    $display ("SoC: Writing obfuscated Field Entropy to fuse bank\n");
                    for (int dw=0; dw < `CLP_OBF_FE_DWORDS; dw++) begin
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_0 + 4 * dw), .data(cptra_fe_tb[dw]), .resp(wresp));
                    end

                    $display ("SoC: Writing SOC Stepping ID to fuse bank\n");
                    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_FUSE_SOC_STEPPING_ID), .data($urandom()), .resp(wresp));

                    $display ("SoC: Writing fuse done register\n");
                    m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_FUSE_WR_DONE), .data(32'h00000001), .resp(wresp));

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
                            m_axi_bfm_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS), .data(rdata), .resp(rresp));
                            poll_count++;
                        end while(rdata[`SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_LOW] == 1);
                        $display("\n  >>> SoC: Ready for Fuses deasserted after polling %d times\n", poll_count);
                        $display ("SoC: Writing BootGo register\n");
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_BOOTFSM_GO), .data(32'h00000001), .resp(wresp));
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
                            m_axi_bfm_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_LOCK), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp));
                            poll_count++;
                        end while (rdata[`MBOX_CSR_MBOX_LOCK_LOCK_LOW] == 1);
                        $display ("\n  >>> SoC: Lock granted after polling %d times\n", poll_count);

                        $display ("SoC: Writing the Command Register\n");
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_CMD), .user(32'hFFFF_FFFF), .data(32'hBA5EBA11), .resp(wresp));

                        $display ("SoC: Writing the Data Length Register\n");
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_DLEN), .user(32'hFFFF_FFFF), .data(FW_NUM_DWORDS*4), .resp(wresp));

                        $display ("SoC: Writing the Firmware into Data-in Register\n");
                        fw_blob = new[FW_NUM_DWORDS];
                        wstrb_array = new[FW_NUM_DWORDS]('{default: {`CALIPTRA_AXI_DATA_WIDTH/8{1'b1}}});
                        for (int dw=0; dw < FW_NUM_DWORDS; dw++)
                            fw_blob[dw] = $urandom();
                        m_axi_bfm_if.axi_write(.addr(`CLP_MBOX_CSR_MBOX_DATAIN),
                                           .burst(AXI_BURST_FIXED),
                                           .len  (FW_NUM_DWORDS-1),
                                           .user (32'hFFFF_FFFF),
                                           .data (fw_blob),
                                           .strb (wstrb_array),
                                           .resp (wresp));

                        $display ("SoC: Setting the Execute Register\n");
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_EXECUTE), .user(32'hFFFF_FFFF), .data(32'h00000001), .resp(wresp));

                        $display("SoC: Waiting for Response Data availability\n");
                        wait(mailbox_data_avail);

                        $display("SoC: Reading the Status Register...\n");
                        m_axi_bfm_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_STATUS), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp));

                        if (((rdata & `MBOX_CSR_MBOX_STATUS_STATUS_MASK) >> `MBOX_CSR_MBOX_STATUS_STATUS_LOW) == DATA_READY) begin: READ_RESP_DATA
                            $display("SoC: Reading the Data Length Register...\n");
                            m_axi_bfm_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_DLEN), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp));

                            $display("SoC: Reading the Data Out Register\n");
                            for (int xfer4k = 0; xfer4k < rdata; xfer4k += 4096) begin
                                byte_count = (rdata - xfer4k) > 4096 ? 4096 : (rdata - xfer4k);
                                dw_count = byte_count/(`CALIPTRA_AXI_DATA_WIDTH/8) + |byte_count[$clog2(`CALIPTRA_AXI_DATA_WIDTH/8)-1:0];
                                rdata_array = new[dw_count];
                                rresp_array = new[dw_count];
                                m_axi_bfm_if.axi_read(.addr (`CLP_MBOX_CSR_MBOX_DATAOUT),
                                                      .burst(AXI_BURST_FIXED),
                                                      .len  (dw_count-1     ),
                                                      .user (32'hFFFF_FFFF  ),
                                                      .data (rdata_array    ),
                                                      .resp (rresp_array)   );
                            end
                        end: READ_RESP_DATA

                        $display("SoC: Resetting the Execute Register\n");
                        m_axi_bfm_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_EXECUTE), .user(32'hFFFF_FFFF), .data(32'h0), .resp(wresp));

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
                            m_axi_bfm_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL), .data(rdata), .resp(rresp));
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
                            else begin
                                generic_input_wires = {32'h0, ERROR_NONE_SET};
                            end
                            // HW ERROR registers are W1C, capture the set bits
                            soc_ifc_hw_error_wdata = rdata;
                            //wait for reset stuff
                            assert_rst_flag_from_fatal = 1;
                            wait(cptra_rst_b == 0);
                        end
                        else if (cptra_error_non_fatal_dly_p) begin
                            $display("SoC: Observed cptra_error_non_fatal; reading Caliptra register\n");
                            m_axi_bfm_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL), .data(rdata), .resp(rresp));
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
                            $display("SoC: Observed cptra_error_non_fatal; writing to clear Caliptra register\n");
                            m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL), .data(rdata), .resp(wresp));
                        end
                        else if (soc_ifc_hw_error_wdata) begin
                            $display("SoC: Observed cptra_error_fatal; writing to clear Caliptra register\n");
                            m_axi_bfm_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL), .data(soc_ifc_hw_error_wdata), .resp(wresp));
                            soc_ifc_hw_error_wdata = '0;
                        end
                        else if (ras_test_ctrl.do_no_lock_access) begin
                            fork
                                begin
                                    $display("SoC: Reading the Data Out Register without lock\n");
                                    dw_count = 1;
                                    rdata_array = new[dw_count];
                                    rresp_array = new[dw_count];
                                    m_axi_bfm_if.axi_read(.addr(`CLP_MBOX_CSR_MBOX_DATAOUT),
                                                      .burst(AXI_BURST_FIXED),
                                                      .len  (dw_count-1     ),
                                                      .user (32'hFFFF_FFFF  ),
                                                      .data (rdata_array    ),
                                                      .resp (rresp_array)   );
                                end
                            join
                        end
                        else if (ras_test_ctrl.do_ooo_access) begin
                            fork
                                begin
                                    $write ("SoC: Requesting mailbox lock...");
                                    poll_count = 0;
                                    do begin
                                        m_axi_bfm_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_LOCK), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp));
                                        poll_count++;
                                    end while (rdata[`MBOX_CSR_MBOX_LOCK_LOCK_LOW] == 1);
                                    $display ("\n  >>> SoC: Lock granted after polling %d times\n", poll_count);

                                    $display("SoC: Reading the Data Length Register...\n");
                                    m_axi_bfm_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_DLEN), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp));

                                    $display("SoC: Reading the Data Out Register\n");
                                    dw_count = 1;
                                    rdata_array = new[dw_count];
                                    rresp_array = new[dw_count];
                                    m_axi_bfm_if.axi_read(.addr(`CLP_MBOX_CSR_MBOX_DATAOUT),
                                                      .burst(AXI_BURST_FIXED),
                                                      .len  (dw_count-1     ),
                                                      .user (32'hFFFF_FFFF  ),
                                                      .data (rdata_array    ),
                                                      .resp (rresp_array)   );
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
                            m_axi_bfm_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_DLEN), .user(32'hFFFF_FFFF), .data(rdata), .resp(rresp));

                            $display("SoC: Reading the Data Out Register\n");
                            for (int xfer4k = 0; xfer4k < rdata; xfer4k += 4096) begin
                                byte_count = (rdata - xfer4k) > 4096 ? 4096 : (rdata - xfer4k);
                                dw_count = byte_count/(`CALIPTRA_AXI_DATA_WIDTH/8) + |byte_count[$clog2(`CALIPTRA_AXI_DATA_WIDTH/8)-1:0];
                                rdata_array = new[dw_count];
                                rresp_array = new[dw_count];
                                m_axi_bfm_if.axi_read(.addr(`CLP_MBOX_CSR_MBOX_DATAOUT),
                                                  .burst(AXI_BURST_FIXED),
                                                  .len  (dw_count-1     ),
                                                  .user (32'hFFFF_FFFF  ),
                                                  .data (rdata_array    ),
                                                  .resp (rresp_array    ));
                            end

                            $display ("SoC: Writing the Mbox Status Register\n");
                            m_axi_bfm_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_STATUS), .user(32'hFFFF_FFFF), .data(32'h1), .resp(wresp));
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
    release `RV_IDMA_RESP_INST.hreadyout;
    release `RV_DDMA_RESP_INST.hreadyout;

    release `RV_INST.dma_htrans;
    release `RV_INST.dma_haddr;
    release `RV_INST.dma_hsize;
    release `RV_INST.dma_hwrite;
    release `RV_INST.dma_hwdata;
    release `RV_INST.dma_hsel;
    release `RV_INST.dma_hreadyin;
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

endmodule
