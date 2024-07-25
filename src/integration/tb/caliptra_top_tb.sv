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

    import axi_pkg::*;
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
    int poll_count;


    logic                       cptra_pwrgood;
    logic                       cptra_rst_b;
    logic                       BootFSM_BrkPoint;
    logic                       scan_mode;

    logic [`CLP_OBF_KEY_DWORDS-1:0][31:0]          cptra_obf_key;
    logic [0:`CLP_OBF_KEY_DWORDS-1][31:0]          cptra_obf_key_uds, cptra_obf_key_fe;
    
    logic [0:`CLP_OBF_UDS_DWORDS-1][31:0]          cptra_uds_tb;
    logic [0:`CLP_OBF_FE_DWORDS-1][31:0]           cptra_fe_tb;

    logic [0:`CLP_OBF_UDS_DWORDS-1][31:0]          cptra_uds_rand;
    logic [0:`CLP_OBF_FE_DWORDS-1][31:0]           cptra_fe_rand;
    logic [0:`CLP_OBF_KEY_DWORDS-1][31:0]          cptra_obf_key_tb;

    localparam FW_NUM_DWORDS         = 256;

    //jtag interface
    logic                       jtag_tck;    // JTAG clk
    logic                       jtag_tms;    // JTAG TMS
    logic                       jtag_tdi;    // JTAG tdi
    logic                       jtag_trst_n; // JTAG Reset
    logic                       jtag_tdo;    // JTAG TDO
    logic                       jtag_tdoEn;  // JTAG TDO enable

    // AXI request signals
    axi_resp_e wresp, rresp;
    logic [`CALIPTRA_AXI_DATA_WIDTH-1:0] wdata, rdata;
    logic [`CALIPTRA_AXI_DATA_WIDTH/8-1:0] wstrb_array[];
    logic [`CALIPTRA_AXI_DATA_WIDTH-1:0] rdata_array[];
    axi_resp_e rresp_array[];

    int byte_count;
    int dw_count;

    // AXI Interface
    axi_if #(
        .AW(`CALIPTRA_SLAVE_ADDR_WIDTH(`CALIPTRA_SLAVE_SEL_SOC_IFC)),
        .DW(`CALIPTRA_AXI_DATA_WIDTH),
        .IW(`CALIPTRA_AXI_ID_WIDTH),
        .UW(`CALIPTRA_AXI_USER_WIDTH)
    ) s_axi_if (.clk(core_clk), .rst_n(cptra_rst_b));
    axi_if #(
        .AW(`CALIPTRA_AXI_DMA_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .IW(CPTRA_AXI_DMA_ID_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH)
    ) m_axi_if (.clk(core_clk), .rst_n(cptra_rst_b));
    axi_if #(
        .AW(AXI_SRAM_ADDR_WIDTH),
        .DW(CPTRA_AXI_DMA_DATA_WIDTH),
        .IW(CPTRA_AXI_DMA_ID_WIDTH),
        .UW(CPTRA_AXI_DMA_USER_WIDTH)
    ) axi_sram_if (.clk(core_clk), .rst_n(cptra_rst_b));

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

    logic rv_dma_resp_error;

    logic [`CALIPTRA_AXI_DATA_WIDTH-1:0] soc_ifc_hw_error_wdata;

    //Interrupt flags
    logic int_flag;
    logic cycleCnt_smpl_en;
    process boot_and_cmd_flow;

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

    logic [31:0] fw_blob [];

`ifndef VERILATOR
    always
    begin : clk_gen
      core_clk = #5ns ~core_clk;
    end // clk_gen
`endif
    
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
        s_axi_if.rst_mgr();

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

                    // Fuse download sequence
                    wait(ready_for_fuses == 1);
                    $display ("CLP: Ready for fuse download\n");

                    repeat(5) @(posedge core_clk);

                    $display ("SoC: Writing obfuscated UDS to fuse bank\n");
                    for (int dw=0; dw < `CLP_OBF_UDS_DWORDS; dw++) begin
                        s_axi_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_FUSE_UDS_SEED_0 + 4 * dw), .data(cptra_uds_tb[dw]), .resp(wresp));
                    end

                    $display ("SoC: Writing obfuscated Field Entropy to fuse bank\n");
                    for (int dw=0; dw < `CLP_OBF_FE_DWORDS; dw++) begin
                        s_axi_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_FUSE_FIELD_ENTROPY_0 + 4 * dw), .data(cptra_fe_tb[dw]), .resp(wresp));
                    end

                    $display ("SoC: Writing SOC Stepping ID to fuse bank\n");
                    s_axi_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_FUSE_SOC_STEPPING_ID), .data($urandom()), .resp(wresp));

                    $display ("SoC: Writing fuse done register\n");
                    s_axi_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_FUSE_WR_DONE), .data(32'h00000001), .resp(wresp));

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
                            s_axi_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_CPTRA_FLOW_STATUS), .data(rdata), .resp(rresp));
                            poll_count++;
                        end while(rdata[`SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FUSES_LOW] == 1);
                        $display("\n  >>> SoC: Ready for Fuses deasserted after polling %d times\n", poll_count);
                        $display ("SoC: Writing BootGo register\n");
                        s_axi_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_BOOTFSM_GO), .data(32'h00000001), .resp(wresp));
                    end

                    // Test sequence (Mailbox or error handling)
                    wait(ready_for_fw_push || ras_test_ctrl.error_injection_seen);

                    // Mailbox flow
                    if (ready_for_fw_push) begin
                        $display ("CLP: ROM Flow in progress...\n");
                        repeat(5) @(posedge core_clk);

                        $display ("CLP: Ready for firmware push\n");
                        $write ("SoC: Requesting mailbox lock...");
                        poll_count = 0;
                        do begin
                            s_axi_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_LOCK), .id(32'hFFFF_FFFF), .data(rdata), .resp(rresp));
                            poll_count++;
                        end while (rdata[`MBOX_CSR_MBOX_LOCK_LOCK_LOW] == 1);
                        $display ("\n  >>> SoC: Lock granted after polling %d times\n", poll_count);

                        $display ("SoC: Writing the Command Register\n");
                        s_axi_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_CMD), .id(32'hFFFF_FFFF), .data(32'hBA5EBA11), .resp(wresp));

                        $display ("SoC: Writing the Data Length Register\n");
                        s_axi_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_DLEN), .id(32'hFFFF_FFFF), .data(FW_NUM_DWORDS*4), .resp(wresp));

                        $display ("SoC: Writing the Firmware into Data-in Register\n");
                        fw_blob = new[FW_NUM_DWORDS];
                        wstrb_array = new[FW_NUM_DWORDS]('{default: {`CALIPTRA_AXI_DATA_WIDTH/8{1'b1}}});
                        for (int dw=0; dw < FW_NUM_DWORDS; dw++)
                            fw_blob[dw] = $urandom();
                        s_axi_if.axi_write(.addr(`CLP_MBOX_CSR_MBOX_DATAIN),
                                           .burst(AXI_BURST_FIXED),
                                           .len  (FW_NUM_DWORDS-1),
                                           .id   (32'hFFFF_FFFF),
                                           .data (fw_blob),
                                           .strb (wstrb_array),
                                           .resp (wresp));

                        $display ("SoC: Setting the Execute Register\n");
                        s_axi_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_EXECUTE), .id(32'hFFFF_FFFF), .data(32'h00000001), .resp(wresp));

                        $display("SoC: Waiting for Response Data availability\n");
                        wait(mailbox_data_avail);

                        $display("SoC: Reading the Status Register...\n");
                        s_axi_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_STATUS), .id(32'hFFFF_FFFF), .data(rdata), .resp(rresp));

                        if (((rdata & `MBOX_CSR_MBOX_STATUS_STATUS_MASK) >> `MBOX_CSR_MBOX_STATUS_STATUS_LOW) == DATA_READY) begin: READ_RESP_DATA
                            $display("SoC: Reading the Data Length Register...\n");
                            s_axi_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_DLEN), .id(32'hFFFF_FFFF), .data(rdata), .resp(rresp));

                            $display("SoC: Reading the Data Out Register\n");
                            for (int xfer4k = 0; xfer4k < rdata; xfer4k += 4096) begin
                                byte_count = (rdata - xfer4k) > 4096 ? 4096 : (rdata - xfer4k);
                                dw_count = byte_count/(`CALIPTRA_AXI_DATA_WIDTH/8) + |byte_count[$clog2(`CALIPTRA_AXI_DATA_WIDTH/8)-1:0];
                                rdata_array = new[dw_count];
                                rresp_array = new[dw_count];
                                s_axi_if.axi_read(.addr(`CLP_MBOX_CSR_MBOX_DATAOUT),
                                                  .burst(AXI_BURST_FIXED),
                                                  .len(dw_count-1),
                                                  .id (32'hFFFF_FFFF),
                                                  .data(rdata_array),
                                                  .resp(rresp_array));
                            end
                        end: READ_RESP_DATA

                        $display("SoC: Resetting the Execute Register\n");
                        s_axi_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_EXECUTE), .id(32'hFFFF_FFFF), .data(32'h0), .resp(wresp));

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
                            s_axi_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL), .id(32'hFFFF_FFFF), .data(rdata), .resp(rresp));
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
                            s_axi_if.axi_read_single(.addr(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL), .id(32'hFFFF_FFFF), .data(rdata), .resp(rresp));
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
                            s_axi_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_NON_FATAL), .id(32'hFFFF_FFFF), .data(rdata), .resp(wresp));
                        end
                        else if (soc_ifc_hw_error_wdata) begin
                            $display("SoC: Observed cptra_error_fatal; writing to clear Caliptra register\n");
                            s_axi_if.axi_write_single(.addr(`CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL), .id(32'hFFFF_FFFF), .data(soc_ifc_hw_error_wdata), .resp(wresp));
                            soc_ifc_hw_error_wdata = '0;
                        end
                        else if (ras_test_ctrl.do_no_lock_access) begin
                            fork
                                begin
                                    $display("SoC: Reading the Data Out Register without lock\n");
                                    dw_count = 1;
                                    rdata_array = new[dw_count];
                                    rresp_array = new[dw_count];
                                    s_axi_if.axi_read(.addr(`CLP_MBOX_CSR_MBOX_DATAOUT),
                                                      .burst(AXI_BURST_FIXED),
                                                      .len(dw_count-1),
                                                      .id (32'hFFFF_FFFF),
                                                      .data(rdata_array),
                                                      .resp(rresp_array));
                                end
                            join
                        end
                        else if (ras_test_ctrl.do_ooo_access) begin
                            fork
                                begin
                                    $write ("SoC: Requesting mailbox lock...");
                                    poll_count = 0;
                                    do begin
                                        s_axi_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_LOCK), .id(32'hFFFF_FFFF), .data(rdata), .resp(rresp));
                                        poll_count++;
                                    end while (rdata[`MBOX_CSR_MBOX_LOCK_LOCK_LOW] == 1);
                                    $display ("\n  >>> SoC: Lock granted after polling %d times\n", poll_count);

                                    $display("SoC: Reading the Data Length Register...\n");
                                    s_axi_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_DLEN), .id(32'hFFFF_FFFF), .data(rdata), .resp(rresp));

                                    $display("SoC: Reading the Data Out Register\n");
                                    dw_count = 1;
                                    rdata_array = new[dw_count];
                                    rresp_array = new[dw_count];
                                    s_axi_if.axi_read(.addr(`CLP_MBOX_CSR_MBOX_DATAOUT),
                                                      .burst(AXI_BURST_FIXED),
                                                      .len(dw_count-1),
                                                      .id (32'hFFFF_FFFF),
                                                      .data(rdata_array),
                                                      .resp(rresp_array));
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
                            s_axi_if.axi_read_single(.addr(`CLP_MBOX_CSR_MBOX_DLEN), .id(32'hFFFF_FFFF), .data(rdata), .resp(rresp));

                            $display("SoC: Reading the Data Out Register\n");
                            for (int xfer4k = 0; xfer4k < rdata; xfer4k += 4096) begin
                                byte_count = (rdata - xfer4k) > 4096 ? 4096 : (rdata - xfer4k);
                                dw_count = byte_count/(`CALIPTRA_AXI_DATA_WIDTH/8) + |byte_count[$clog2(`CALIPTRA_AXI_DATA_WIDTH/8)-1:0];
                                rdata_array = new[dw_count];
                                rresp_array = new[dw_count];
                                s_axi_if.axi_read(.addr(`CLP_MBOX_CSR_MBOX_DATAOUT),
                                                  .burst(AXI_BURST_FIXED),
                                                  .len(dw_count-1),
                                                  .id (32'hFFFF_FFFF),
                                                  .data(rdata_array),
                                                  .resp(rresp_array));
                            end

                            $display ("SoC: Writing the Mbox Status Register\n");
                            s_axi_if.axi_write_single(.addr(`CLP_MBOX_CSR_MBOX_STATUS), .id(32'hFFFF_FFFF), .data(32'h1), .resp(wresp));
                        end
                        @(posedge core_clk);
                    end
                end: BOOT_AND_CMD_FLOW
                begin: CLK_GATE_FLOW
                    wait(cycleCnt_smpl_en);
                    repeat(2000) @(negedge core_clk);

                    if (int_flag)
                        $display("SoC (clk_gate_flow): Forcing soft_int = 1. cycleCnt [%d]\n", cycleCnt);
                        force caliptra_top_dut.soft_int = 1'b1;
                    repeat(2) @(negedge core_clk);
                        $display("SoC (clk_gate_flow): Releasing soft_int = 1. cycleCnt [%d]\n", cycleCnt);
                        release caliptra_top_dut.soft_int;

                    repeat(5000) @(negedge core_clk);

                    if (int_flag)
                        $display("SoC (clk_gate_flow): Forcing timer_int = 1. cycleCnt [%d]\n", cycleCnt);
                        force caliptra_top_dut.timer_int = 1'b1;
                    repeat(2) @(negedge core_clk);
                        $display("SoC (clk_gate_flow): Releasing timer_int = 1. cycleCnt [%d]\n", cycleCnt);
                        release caliptra_top_dut.timer_int;

                    repeat(8000) @(negedge core_clk);

                    if (int_flag)
                        $display("SoC (clk_gate_flow): Forcing soft_int = 1. cycleCnt [%d]\n", cycleCnt);
                        force caliptra_top_dut.soft_int = 1'b1;
                    repeat(2) @(negedge core_clk);
                        $display("SoC (clk_gate_flow): Releasing soft_int = 1. cycleCnt [%d]\n", cycleCnt);
                        release caliptra_top_dut.soft_int;

                    wait(cptra_rst_b == 0);
                end: CLK_GATE_FLOW
                begin: RESET_FLOW
                    @(negedge cptra_rst_b);
                    $display("CLP: Observed cptra_rst_b assertion\n");
//                    disable BOOT_AND_CMD_FLOW; 
                    if (boot_and_cmd_flow != null) boot_and_cmd_flow.kill();
                    assert_rst_flag_from_fatal = 1'b0;
                    s_axi_if.rst_mgr();
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
    .jtag_tdoEn(jtag_tdoEn),
    
    //SoC AXI Interface
    .s_axi_w_if(s_axi_if.w_sub),
    .s_axi_r_if(s_axi_if.r_sub),

    //AXI DMA Interface
    .m_axi_w_if(m_axi_if.w_mgr),
    .m_axi_r_if(m_axi_if.r_mgr),

    .qspi_clk_o (qspi_clk),
    .qspi_cs_no (qspi_cs_n),
    .qspi_d_i   (qspi_data_device_to_host),
    .qspi_d_o   (qspi_data_host_to_device),
    .qspi_d_en_o(qspi_data_host_to_device_en),

`ifdef CALIPTRA_INTERNAL_UART
    .uart_tx(uart_loopback),
    .uart_rx(uart_loopback),
`endif

    .el2_mem_export(el2_mem_export.veer_sram_src),

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

    .recovery_data_avail(1'b1/*TODO*/),

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
    .el2_mem_export (el2_mem_export.veer_sram_sink),

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

always_comb begin
    // AXI AR
    axi_sram_if.araddr        = m_axi_if.araddr[AXI_SRAM_ADDR_WIDTH-1:0];
    axi_sram_if.arburst       = m_axi_if.arburst;
    axi_sram_if.arsize        = m_axi_if.arsize ;
    axi_sram_if.arlen         = m_axi_if.arlen  ;
    axi_sram_if.aruser        = m_axi_if.aruser ;
    axi_sram_if.arid          = m_axi_if.arid   ;
    axi_sram_if.arlock        = m_axi_if.arlock ;
    axi_sram_if.arvalid       = m_axi_if.arvalid && m_axi_if.araddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH];
    m_axi_if.arready          = axi_sram_if.arready;
                                                
    // AXI R                                    
    m_axi_if.rdata            = axi_sram_if.rdata ;
    m_axi_if.rresp            = axi_sram_if.rresp ;
    m_axi_if.rid              = axi_sram_if.rid   ;
    m_axi_if.rlast            = axi_sram_if.rlast ;
    m_axi_if.rvalid           = axi_sram_if.rvalid;
    axi_sram_if.rready        = m_axi_if.rready ;
                                                
    // AXI AW                                   
    axi_sram_if.awaddr        = m_axi_if.awaddr[AXI_SRAM_ADDR_WIDTH-1:0];
    axi_sram_if.awburst       = m_axi_if.awburst;
    axi_sram_if.awsize        = m_axi_if.awsize ;
    axi_sram_if.awlen         = m_axi_if.awlen  ;
    axi_sram_if.awuser        = m_axi_if.awuser ;
    axi_sram_if.awid          = m_axi_if.awid   ;
    axi_sram_if.awlock        = m_axi_if.awlock ;
    axi_sram_if.awvalid       = m_axi_if.awvalid && m_axi_if.awaddr[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH] == AXI_SRAM_BASE_ADDR[`CALIPTRA_AXI_DMA_ADDR_WIDTH-1:AXI_SRAM_ADDR_WIDTH];
    m_axi_if.awready          = axi_sram_if.awready;
                                                
    // AXI W                                    
    axi_sram_if.wdata         = m_axi_if.wdata  ;
    axi_sram_if.wstrb         = m_axi_if.wstrb  ;
    axi_sram_if.wvalid        = m_axi_if.wvalid ;
    axi_sram_if.wlast         = m_axi_if.wlast  ;
    m_axi_if.wready           = axi_sram_if.wready ;
                                                
    // AXI B                                    
    m_axi_if.bresp            = axi_sram_if.bresp  ;
    m_axi_if.bid              = axi_sram_if.bid    ;
    m_axi_if.bvalid           = axi_sram_if.bvalid ;
    axi_sram_if.bready        = m_axi_if.bready ;
end

caliptra_axi_sram #(
    .AW(AXI_SRAM_ADDR_WIDTH),
    .DW(CPTRA_AXI_DMA_DATA_WIDTH),
    .UW(CPTRA_AXI_DMA_USER_WIDTH),
    .IW(CPTRA_AXI_DMA_ID_WIDTH),
    .EX_EN(0)
) i_axi_sram (
    .clk(core_clk),
    .rst_n(cptra_rst_b),

    // AXI INF
    .s_axi_w_if(axi_sram_if.w_sub),
    .s_axi_r_if(axi_sram_if.r_sub)
);
`ifdef VERILATOR
initial i_axi_sram.i_sram.ram = '{default:'{default:8'h00}};
`else
initial i_axi_sram.i_sram.ram = '{default:8'h00};
`endif

`define RV_INST caliptra_top_dut.rvtop
`define RV_IDMA_RESP_INST caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_IDMA]
`define RV_DDMA_RESP_INST caliptra_top_dut.responder_inst[`CALIPTRA_SLAVE_SEL_DDMA]
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

caliptra_top_sva sva();

endmodule
