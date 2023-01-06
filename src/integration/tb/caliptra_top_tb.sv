// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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

`include "config_defines.svh"
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
    logic                       mailbox_write;
    logic                       mailbox_data_val;
    int                         commit_count;

    logic                       wb_valid;
    logic [4:0]                 wb_dest;
    logic [31:0]                wb_data;

    logic        [31:0]         trace_rv_i_insn_ip;
    logic        [31:0]         trace_rv_i_address_ip;
    logic                       trace_rv_i_valid_ip;
    logic                       trace_rv_i_exception_ip;
    logic        [4:0]          trace_rv_i_ecause_ip;
    logic                       trace_rv_i_interrupt_ip;
    logic        [31:0]         trace_rv_i_tval_ip;

    bit                         hex_file_is_empty;
    logic                       start_apb_fuse_sequence;
    logic                       cptra_pwrgood;
    logic                       cptra_rst_b;

    logic [7:0][31:0]           cptra_obf_key;
    logic [0:7][31:0]           cptra_obf_key_uds, cptra_obf_key_fe;
    
    logic [0:11][31:0]          cptra_uds_tb;
    logic [0:31][31:0]          cptra_fe_tb;

    enum logic [5:0] {
        S_APB_IDLE,
        S_APB_WR_UDS,
        S_APB_WR_FE,
        S_APB_WR_FUSE_DONE,
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

    wire[31:0] WriteData;
    string                      abi_reg[32]; // ABI register names
    //jtag interface
    logic                       jtag_tck;    // JTAG clk
    logic                       jtag_tms;    // JTAG TMS
    logic                       jtag_tdi;    // JTAG tdi
    logic                       jtag_trst_n; // JTAG Reset
    logic                       jtag_tdo;    // JTAG TDO
    //APB Interface
    logic [`CALIPTRA_APB_ADDR_WIDTH-1:0] PADDR;
    logic [3:0]                 PPROT;
    logic                       PSEL;
    logic                       PENABLE;
    logic                       PWRITE;
    logic [`CALIPTRA_APB_DATA_WIDTH-1:0] PWDATA;
    logic [`CALIPTRA_APB_USER_WIDTH-1:0] PAUSER;

    logic                       PREADY;
    logic                       PSLVERR;
    logic [`CALIPTRA_APB_DATA_WIDTH-1:0] PRDATA;

    logic ready_for_fuses;
    logic ready_for_fw_push;
    logic mbox_sram_cs;
    logic mbox_sram_we;
    logic [14:0] mbox_sram_addr;
    logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_wdata;
    logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_wdata_bitflip;
    logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_rdata;

    logic imem_cs;
    logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] imem_addr;
    logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] imem_rdata;

    //TIE-OFF device lifecycle
    security_state_t security_state = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1};

    logic [63:0] generic_input_wires;

    //Interrupt flags
    //logic nmi_int;
    //logic soft_int;
    //logic timer_int;
    logic int_flag;

`define DEC caliptra_top_dut.rvtop.swerv.dec

`define LMEM mbox_ram1.ram 

    el2_mem_if el2_mem_export ();

    parameter MEMTYPE_LMEM = 3'h1;
    parameter MEMTYPE_DCCM = 3'h2;
    parameter MEMTYPE_ICCM = 3'h3;

    parameter MBOX_UDS_ADDR = 32'h3003_0200;
    parameter MBOX_FE_ADDR  = 32'h3003_0230;
    parameter MBOX_FUSE_DONE_ADDR = 32'h3003_03f0; //FIXME need to not hardcode these

    parameter MBOX_ADDR_BASE        = 32'h30020000;
    parameter MBOX_ADDR_LOCK        = MBOX_ADDR_BASE;
    parameter MBOX_ADDR_CMD         = MBOX_ADDR_BASE + 32'h00000008;
    parameter MBOX_ADDR_DLEN        = MBOX_ADDR_BASE + 32'h0000000C;
    parameter MBOX_ADDR_DATAIN      = MBOX_ADDR_BASE + 32'h00000010;
    parameter MBOX_ADDR_DATAOUT     = MBOX_ADDR_BASE + 32'h00000014;
    parameter MBOX_ADDR_EXECUTE     = MBOX_ADDR_BASE + 32'h00000018;
    parameter FW_NUM_DWORDS         = 256;

    logic [FW_NUM_DWORDS-1:0][31:0] fw_blob;

    logic [2:0] memtype; 
    // NOTE: This aperture into the mailbox is heavily overloaded right now by
    //       various firmware "STDOUT" use-cases.
    //       Functionality currently implemented at this offset is as follows
    //       (relative to the WriteData used to trigger that function):
    //         8'h0         - Do nothing
    //         8'h1         - Kill the simulation with a Failed status
    //         8'h2 : 8'h5  - Do nothing
    //         8'h6 : 8'h7E - WriteData is an ASCII character - dump to console.log
    //         8'h7F        - Do nothing
    //         8'hf8        - Assert interrupt flags at fixed intervals to wake up halted core
    //         8'hf9        - Lock debug in security state
    //         8'hfa        - Unlock debug in security state
    //         8'hfb        - Set the isr_active bit
    //         8'hfc        - Clear the isr_active bit
    //         8'hfd        - Toggle random SRAM single bit error injection
    //         8'hfe        - Toggle random SRAM double bit error injection
    //         8'hff        - End the simulation with a Success status
    assign mailbox_write = caliptra_top_dut.soc_ifc_top1.i_soc_ifc_reg.field_combo.generic_output_wires[0].generic_wires.load_next;
    assign WriteData = caliptra_top_dut.soc_ifc_top1.i_soc_ifc_reg.field_combo.generic_output_wires[0].generic_wires.next;
    assign mailbox_data_val = WriteData[7:0] > 8'h5 && WriteData[7:0] < 8'h7f;

    parameter MAX_CYCLES = 20_000_000;

    integer fd, tp, el, sm, i;
    integer ifu_p, lsu_p, sl_p[`CALIPTRA_AHB_SLAVES_NUM];

    integer j;

    string slaveLog_fileName[`CALIPTRA_AHB_SLAVES_NUM];

`ifndef VERILATOR
    always
    begin : clk_gen
      core_clk = #5ns ~core_clk;
    end // clk_gen
`endif
    
    logic [7:0] isr_active = 8'h0;
    always @(negedge core_clk) begin
        if ((WriteData[7:0] == 8'hfc) && mailbox_write) begin
            isr_active--;
        end
        else if ((WriteData[7:0] == 8'hfb) && mailbox_write) begin
            isr_active++;
        end
    end
    logic [1:0] inject_rand_sram_error = 2'b0;
    always @(negedge core_clk) begin
        if ((WriteData[7:0] == 8'hfd) && mailbox_write) begin
            inject_rand_sram_error ^= 2'b01;
        end
        else if ((WriteData[7:0] == 8'hfe) && mailbox_write) begin
            inject_rand_sram_error ^= 2'b10;
        end
    end

    always @(negedge core_clk) begin
        //lock debug mode
        if ((WriteData[7:0] == 8'hf9) && mailbox_write) begin
            security_state.debug_locked <= 1'b1;
        end
        //unlock debug mode
        else if ((WriteData[7:0] == 8'hfa) && mailbox_write) begin
            security_state.debug_locked <= 1'b0;
        end
    end

    always @(negedge core_clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) int_flag <= 'b0;
        else if((WriteData[7:0] == 8'hf8) && mailbox_write) begin
            int_flag <= 1'b1;
        end
    end

    bit flip_bit;
    `ifndef VERILATOR
        initial begin
            bitflip_mask_generator #(MBOX_DATA_AND_ECC_W) bitflip_gen = new();
            forever begin
                @(posedge core_clk)
                if (~|inject_rand_sram_error) begin
                    mbox_sram_wdata_bitflip <= '0;
                end
                else if (mbox_sram_cs & mbox_sram_we) begin
                    // Corrupt 10% of the writes
                    flip_bit = $urandom_range(0,99) < 10;
                    mbox_sram_wdata_bitflip <= flip_bit ? bitflip_gen.get_mask(inject_rand_sram_error[1]) : '0;
//                    if (flip_bit) $display("%t Injecting bit flips", $realtime);
//                    else          $display("%t No bit flips injected", $realtime);
                end
            end
        end
    `else
        always @(posedge core_clk) begin
            // Corrupt 10% of the writes
            flip_bit <= ($urandom % 100) < 10;
            if (~|inject_rand_sram_error) begin
                mbox_sram_wdata_bitflip <= '0;
            end
            else if (mbox_sram_cs & mbox_sram_we) begin
                mbox_sram_wdata_bitflip <= flip_bit ? get_bitflip_mask(inject_rand_sram_error[1]) : '0;
            end
        end
    `endif

    always@(negedge core_clk) begin
        if((cycleCnt == 'h3000) && int_flag) begin
            force caliptra_top_dut.rvtop.soft_int = 'b1;
        end
        
        else if((cycleCnt == 'h4000) && int_flag) begin
            force caliptra_top_dut.rvtop.timer_int = 'b1;
        end
        
        else if((cycleCnt == 'h5000) && int_flag) begin
            generic_input_wires <= 'h4000;
        end
        
        else if((cycleCnt == 'h6000) && int_flag) begin
            force caliptra_top_dut.rvtop.soft_int = 'b1;
            int_flag <= 'b0;
        end
        
        else begin
            release caliptra_top_dut.rvtop.soft_int;
            release caliptra_top_dut.rvtop.timer_int;
            generic_input_wires <= 'h0;
        end
    end

    always @(negedge core_clk) begin
        cycleCnt <= cycleCnt+1;
        // Test timeout monitor
        if(cycleCnt == MAX_CYCLES) begin
            $display ("Hit max cycle count (%0d) .. stopping",cycleCnt);
            dump_memory_contents(MEMTYPE_LMEM, 32'h8000_0110, 32'h8000_0180);
            dump_memory_contents(MEMTYPE_DCCM, `RV_DCCM_SADR, `RV_DCCM_EADR);
            dump_memory_contents(MEMTYPE_ICCM, `RV_ICCM_SADR, `RV_ICCM_EADR);
            $finish;
        end
        // console Monitor
        if( mailbox_data_val & mailbox_write) begin
            $fwrite(fd,"%c", WriteData[7:0]);
            $write("%c", WriteData[7:0]);
            if (WriteData[7:0] inside {8'h0A,8'h0D}) begin // CR/LF
                $fflush(fd);
            end
        end
        // End Of test monitor
        if(mailbox_write && WriteData[7:0] == 8'hff) begin
            $display("* TESTCASE PASSED");
            $display("\nFinished : minstret = %0d, mcycle = %0d", `DEC.tlu.minstretl[31:0],`DEC.tlu.mcyclel[31:0]);
            $display("See \"exec.log\" for execution trace with register updates..\n");
            dump_memory_contents(MEMTYPE_LMEM, 32'h0000_0000, 32'h001_FFFF);
            dump_memory_contents(MEMTYPE_DCCM, `RV_DCCM_SADR, `RV_DCCM_EADR);
            dump_memory_contents(MEMTYPE_ICCM, `RV_ICCM_SADR, `RV_ICCM_EADR);
            $finish;
        end
        else if(mailbox_write && WriteData[7:0] == 8'h1) begin
            $display("* TESTCASE FAILED");
            dump_memory_contents(MEMTYPE_LMEM, 32'h0000_0000, 32'h001_FFFF);
            dump_memory_contents(MEMTYPE_DCCM, `RV_DCCM_SADR, `RV_DCCM_EADR);
            dump_memory_contents(MEMTYPE_ICCM, `RV_ICCM_SADR, `RV_ICCM_EADR);
            $finish;
        end
    end


    // trace monitor
    always @(posedge core_clk) begin
        wb_valid  <= `DEC.dec_i0_wen_r;
        wb_dest   <= `DEC.dec_i0_waddr_r;
        wb_data   <= `DEC.dec_i0_wdata_r;
        if (caliptra_top_dut.trace_rv_i_valid_ip) begin
           $fwrite(tp,"%b,%h,%h,%0h,%0h,3,%b,%h,%h,%b\n", caliptra_top_dut.trace_rv_i_valid_ip, 0, caliptra_top_dut.trace_rv_i_address_ip,
                  0, caliptra_top_dut.trace_rv_i_insn_ip,caliptra_top_dut.trace_rv_i_exception_ip,caliptra_top_dut.trace_rv_i_ecause_ip,
                  caliptra_top_dut.trace_rv_i_tval_ip,caliptra_top_dut.trace_rv_i_interrupt_ip);
           // Basic trace - no exception register updates
           // #1 0 ee000000 b0201073 c 0b02       00000000
           commit_count++;
           $fwrite (el, "%10d : %8s 0 %h %h%13s ; %s\n", cycleCnt, $sformatf("#%0d",commit_count),
                        caliptra_top_dut.trace_rv_i_address_ip, caliptra_top_dut.trace_rv_i_insn_ip,
                        (wb_dest !=0 && wb_valid)?  $sformatf("%s=%h", abi_reg[wb_dest], wb_data) : "             ",
                        dasm(caliptra_top_dut.trace_rv_i_insn_ip, caliptra_top_dut.trace_rv_i_address_ip, wb_dest & {5{wb_valid}}, wb_data)
                   );
        end
        if(`DEC.dec_nonblock_load_wen) begin
            $fwrite (el, "%10d : %32s=%h ; nbL\n", cycleCnt, abi_reg[`DEC.dec_nonblock_load_waddr], `DEC.lsu_nonblock_load_data);
            caliptra_top_tb.gpr[0][`DEC.dec_nonblock_load_waddr] = `DEC.lsu_nonblock_load_data;
        end
        if(`DEC.exu_div_wren) begin
            $fwrite (el, "%10d : %32s=%h ; nbD\n", cycleCnt, abi_reg[`DEC.div_waddr_wb], `DEC.exu_div_result);
            caliptra_top_tb.gpr[0][`DEC.div_waddr_wb] = `DEC.exu_div_result;
        end
    end

// FIXME -- this should work in Verilator 4.106+
//`ifndef VERILATOR
    // IFU Initiator monitor
    always @(posedge core_clk) begin
        $fstrobe(ifu_p, "%10d : 0x%0h %h %b %h %h %h %b 0x%08h_%08h %b %b\n", cycleCnt, 
                        caliptra_top_dut.ic_haddr, caliptra_top_dut.ic_hburst, caliptra_top_dut.ic_hmastlock, 
                        caliptra_top_dut.ic_hprot, caliptra_top_dut.ic_hsize, caliptra_top_dut.ic_htrans, 
                        caliptra_top_dut.ic_hwrite, caliptra_top_dut.ic_hrdata[63:32], caliptra_top_dut.ic_hrdata[31:0], 
                        caliptra_top_dut.ic_hready, caliptra_top_dut.ic_hresp);
    end

    // LSU Initiator monitor
    always @(posedge core_clk) begin
        $fstrobe(lsu_p, "%10d : 0x%0h %h %h %b 0x%08h_%08h 0x%08h_%08h %b %b\n", cycleCnt, 
                        caliptra_top_dut.initiator_inst.haddr, caliptra_top_dut.initiator_inst.hsize, caliptra_top_dut.initiator_inst.htrans, 
                        caliptra_top_dut.initiator_inst.hwrite, caliptra_top_dut.initiator_inst.hrdata[63:32], caliptra_top_dut.initiator_inst.hrdata[31:0], 
                        caliptra_top_dut.initiator_inst.hwdata[63:32], caliptra_top_dut.initiator_inst.hwdata[31:0], 
                        caliptra_top_dut.initiator_inst.hready, caliptra_top_dut.initiator_inst.hresp);
    end

    // AHB responder interfaces monitor
    genvar sl_i;
    generate
        for (sl_i = 0; sl_i < `CALIPTRA_AHB_SLAVES_NUM; sl_i = sl_i + 1) begin: gen_responder_inf_monitor
            always @(posedge core_clk) begin
                $fstrobe(sl_p[sl_i], "%10d : 0x%0h %h %h %b 0x%08h_%08h 0x%08h_%08h %b %b %b %b\n", cycleCnt, 
                        caliptra_top_dut.responder_inst[sl_i].haddr, caliptra_top_dut.responder_inst[sl_i].hsize, caliptra_top_dut.responder_inst[sl_i].htrans, 
                        caliptra_top_dut.responder_inst[sl_i].hwrite, caliptra_top_dut.responder_inst[sl_i].hrdata[63:32], caliptra_top_dut.responder_inst[sl_i].hrdata[31:0], 
                        caliptra_top_dut.responder_inst[sl_i].hwdata[63:32], caliptra_top_dut.responder_inst[sl_i].hwdata[31:0], 
                        caliptra_top_dut.responder_inst[sl_i].hready, caliptra_top_dut.responder_inst[sl_i].hreadyout, caliptra_top_dut.responder_inst[sl_i].hresp, caliptra_top_dut.responder_inst[sl_i].hsel);
            end
        end
    endgenerate
//`endif


    initial begin
        cptra_pwrgood = 1'b0;
        cptra_rst_b = 1'b0;
        start_apb_fuse_sequence = 1'b0;
        abi_reg[0] = "zero";
        abi_reg[1] = "ra";
        abi_reg[2] = "sp";
        abi_reg[3] = "gp";
        abi_reg[4] = "tp";
        abi_reg[5] = "t0";
        abi_reg[6] = "t1";
        abi_reg[7] = "t2";
        abi_reg[8] = "s0";
        abi_reg[9] = "s1";
        abi_reg[10] = "a0";
        abi_reg[11] = "a1";
        abi_reg[12] = "a2";
        abi_reg[13] = "a3";
        abi_reg[14] = "a4";
        abi_reg[15] = "a5";
        abi_reg[16] = "a6";
        abi_reg[17] = "a7";
        abi_reg[18] = "s2";
        abi_reg[19] = "s3";
        abi_reg[20] = "s4";
        abi_reg[21] = "s5";
        abi_reg[22] = "s6";
        abi_reg[23] = "s7";
        abi_reg[24] = "s8";
        abi_reg[25] = "s9";
        abi_reg[26] = "s10";
        abi_reg[27] = "s11";
        abi_reg[28] = "t3";
        abi_reg[29] = "t4";
        abi_reg[30] = "t5";
        abi_reg[31] = "t6";
        //tie offs
        jtag_tck = 1'b0;    // JTAG clk
        jtag_tms = 1'b0;    // JTAG TMS
        jtag_tdi = 1'b0;    // JTAG tdi
        jtag_trst_n = 1'b0; // JTAG Reset
        //TIE-OFF
        PPROT = '0;

        hex_file_is_empty = $system("test -s program.hex");
        if (!hex_file_is_empty) $readmemh("program.hex",  imem_inst1.ram,0,32'h00007FFF);
        hex_file_is_empty = $system("test -s mailbox.hex");
        if (!hex_file_is_empty) $readmemh("mailbox.hex",  dummy_mbox_preloader.ram,0,32'h0001_FFFF);
        hex_file_is_empty = $system("test -s dccm.hex");
        if (!hex_file_is_empty) $readmemh("dccm.hex",     dummy_dccm_preloader.ram,0,32'h0001_FFFF);
        hex_file_is_empty = $system("test -s iccm.hex");
        if (!hex_file_is_empty) $readmemh("iccm.hex",     dummy_iccm_preloader.ram,0,32'h0001_FFFF);
        tp = $fopen("trace_port.csv","w");
        el = $fopen("exec.log","w");
        ifu_p = $fopen("ifu_master_ahb_trace.log", "w");
        lsu_p = $fopen("lsu_master_ahb_trace.log", "w");
        $fwrite (el, "//   Cycle : #inst    0    pc    opcode    reg=value   ; mnemonic\n");
        $fwrite(ifu_p, "//   Cycle: ic_haddr     ic_hburst     ic_hmastlock     ic_hprot     ic_hsize     ic_htrans     ic_hwrite     ic_hrdata     ic_hwdata     ic_hready     ic_hresp\n");
        $fwrite(lsu_p, "//   Cycle: lsu_haddr     lsu_hsize     lsu_htrans     lsu_hwrite     lsu_hrdata     lsu_hwdata     lsu_hready     lsu_hresp\n");

//`ifndef VERILATOR
        for (j = 0; j < `CALIPTRA_AHB_SLAVES_NUM; j = j + 1) begin
            slaveLog_fileName[j] = {$sformatf("slave%0d_ahb_trace.log", j)};
            sl_p[j] = $fopen(slaveLog_fileName[j], "w");
            $fwrite(sl_p[j], "//   Cycle: haddr     hsize     htrans     hwrite     hrdata     hwdata     hready     hreadyout     hresp\n");
        end
//`endif

        fd = $fopen("console.log","w");
        commit_count = 0;
        preload_dccm();
        preload_iccm();
        preload_mbox();

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
        if (cycleCnt == 15) begin
            $display ("\n\n\n\n\n\n");
            $display ("SoC: Asserting cptra_pwrgood\n");
            //assert power good
            cptra_pwrgood <= 1'b1;
        end
        else if (cycleCnt == 20) begin
            $display ("SoC: De-Asserting cptra_rst_b\n");
            //de-assert reset
            cptra_rst_b <= 1'b1;
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
                    n_state_apb = S_APB_WAIT_FW_READY;
                end
                else begin
                    n_state_apb = S_APB_WR_FUSE_DONE;
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
                PADDR      = MBOX_UDS_ADDR + 4 * apb_wr_count;
                PWDATA     = cptra_uds_tb[apb_wr_count];
            end
            S_APB_WR_FE: begin
                PADDR      = MBOX_FE_ADDR + 4 * apb_wr_count;
                PWDATA     = cptra_fe_tb[apb_wr_count];
            end
            S_APB_WR_FUSE_DONE: begin
                PADDR      = MBOX_FUSE_DONE_ADDR;
                PWDATA     = 32'h00000001;
            end
            S_APB_POLL_LOCK: begin
                PADDR      = MBOX_ADDR_LOCK;
                PWDATA     = '0;
            end
            S_APB_WR_CMD: begin
                PADDR      = MBOX_ADDR_CMD;
                PWDATA     = 32'hBA5EBA11;
            end
            S_APB_WR_DLEN: begin
                PADDR      = MBOX_ADDR_DLEN;
                PWDATA     = FW_NUM_DWORDS*4;
            end
            S_APB_WR_DATAIN: begin
                PADDR      = MBOX_ADDR_DATAIN;
                PWDATA     = fw_blob[apb_wr_count];
            end
            S_APB_WR_EXEC: begin
                PADDR      = MBOX_ADDR_EXECUTE;
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
    .PPROT(),
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
    .BootFSM_BrkPoint('x), //FIXME TIE-OFF

    .generic_input_wires(generic_input_wires),
    .generic_output_wires(),

    .security_state(security_state) //FIXME TIE-OFF
    /*
    .nmi_int(nmi_int),
    .timer_int(timer_int),
    .soft_int(soft_int)
    */
);

caliptra_swerv_sram_export swerv_sram_export_inst (
    .el2_mem_export(el2_mem_export.top)
);

//SRAM for mbox (preload raw data here)
caliptra_sram 
#(
    .DATA_WIDTH(MBOX_DATA_W),
    .DEPTH     (MBOX_DEPTH )
)
dummy_mbox_preloader
(
    .clk_i(core_clk),

    .cs_i   (),
    .we_i   (),
    .addr_i (),
    .wdata_i(),
    .rdata_o()
);
// Actual Mailbox RAM -- preloaded with data from
// dummy_mbox_preloader with ECC bits appended
caliptra_sram 
#(
    .DATA_WIDTH(MBOX_DATA_AND_ECC_W),
    .DEPTH     (MBOX_DEPTH         )
)
mbox_ram1
(
    .clk_i(core_clk),

    .cs_i(mbox_sram_cs),
    .we_i(mbox_sram_we),
    .addr_i(mbox_sram_addr),
    .wdata_i(mbox_sram_wdata ^ mbox_sram_wdata_bitflip),

    .rdata_o(mbox_sram_rdata)
);

//SRAM for imem
caliptra_sram #(
    .DEPTH     (`CALIPTRA_IMEM_DEPTH     ), // Depth in WORDS
    .DATA_WIDTH(`CALIPTRA_IMEM_DATA_WIDTH),
    .ADDR_WIDTH(`CALIPTRA_IMEM_ADDR_WIDTH)
) imem_inst1 (
    .clk_i   (core_clk   ),

    .cs_i    (imem_cs),
    .we_i    (1'b0/*sram_write && sram_dv*/      ),
    .addr_i  (imem_addr                          ),
    .wdata_i (`CALIPTRA_IMEM_DATA_WIDTH'(0)/*sram_wdata   */),
    .rdata_o (imem_rdata                         )
);

// This is used to load the generated ICCM hexfile prior to
// running slam_iccm_ram
caliptra_sram #(
     .DEPTH     (16384        ), // 128KiB
     .DATA_WIDTH(64           ),
     .ADDR_WIDTH($clog2(16384))

) dummy_iccm_preloader (
    .clk_i   (core_clk),

    .cs_i    (        ),
    .we_i    (        ),
    .addr_i  (        ),
    .wdata_i (        ),
    .rdata_o (        )
);


// This is used to load the generated DCCM hexfile prior to
// running slam_dccm_ram
caliptra_sram #(
     .DEPTH     (16384        ), // 128KiB
     .DATA_WIDTH(64           ),
     .ADDR_WIDTH($clog2(16384))

) dummy_dccm_preloader (
    .clk_i   (core_clk),

    .cs_i    (        ),
    .we_i    (        ),
    .addr_i  (        ),
    .wdata_i (        ),
    .rdata_o (        )
);


task preload_mbox;
    // Variables
    mbox_sram_data_t      ecc_data;
    bit [MBOX_ADDR_W  :0] addr;
    int                   byt;
    localparam NUM_BYTES = MBOX_DATA_AND_ECC_W / 8 + ((MBOX_DATA_AND_ECC_W%8) ? 1 : 0);

    // Init
    `ifndef VERILATOR
    mbox_ram1.ram = '{default:8'h0};
    `endif

    // Slam
    $display("MBOX pre-load from %h to %h", 0, MBOX_DEPTH);
    for (addr = 0; addr < MBOX_DEPTH; addr++) begin
        ecc_data.data = {dummy_mbox_preloader.ram[addr][3],
                         dummy_mbox_preloader.ram[addr][2],
                         dummy_mbox_preloader.ram[addr][1],
                         dummy_mbox_preloader.ram[addr][0]};
        ecc_data.ecc  = |ecc_data.data ? riscv_ecc32(ecc_data.data) : 0;
        for (byt = 0; byt < NUM_BYTES; byt++) begin
            mbox_ram1.ram[addr][byt] = ecc_data[byt*8+:8];
        end
    end
    $display("MBOX pre-load completed");
endtask

task preload_iccm;
    bit[31:0] data;
    bit[31:0] addr, eaddr, saddr;

    /*
    addresses:
     0x00007ff0 - ICCM start address to load
     0x00007ff4 - ICCM end address to load
    */
    `ifndef VERILATOR
    init_iccm();
    `endif
    addr = 'h0000_7ff0;
    // FIXME hardcoded address indices?
    saddr = {imem_inst1.ram [addr[14:3]] [{addr[2],2'h3}],
             imem_inst1.ram [addr[14:3]] [{addr[2],2'h2}],
             imem_inst1.ram [addr[14:3]] [{addr[2],2'h1}],
             imem_inst1.ram [addr[14:3]] [{addr[2],2'h0}]};
    //saddr = {imem_inst1.ram[addr+3],caliptra_top_dut.imem.mem[addr+2],caliptra_top_dut.imem.mem[addr+1],caliptra_top_dut.imem.mem[addr]};
    if ( (saddr < `RV_ICCM_SADR) || (saddr > `RV_ICCM_EADR)) return;
    `ifndef RV_ICCM_ENABLE
        $display("********************************************************");
        $display("ICCM preload: there is no ICCM in SweRV, terminating !!!");
        $display("********************************************************");
        $finish;
    `endif
    addr += 4;
    eaddr = {imem_inst1.ram [addr[14:3]] [{addr[2],2'h3}],
             imem_inst1.ram [addr[14:3]] [{addr[2],2'h2}],
             imem_inst1.ram [addr[14:3]] [{addr[2],2'h1}],
             imem_inst1.ram [addr[14:3]] [{addr[2],2'h0}]};
    //eaddr = {caliptra_top_dut.imem.mem[addr+3],caliptra_top_dut.imem.mem[addr+2],caliptra_top_dut.imem.mem[addr+1],caliptra_top_dut.imem.mem[addr]};
    $display("ICCM pre-load from %h to %h", saddr, eaddr);

    for(addr= saddr; addr < eaddr; addr+=4) begin
        // FIXME hardcoded address indices?
        data = {dummy_iccm_preloader.ram [addr[16:3]] [{addr[2],2'h3}],
                dummy_iccm_preloader.ram [addr[16:3]] [{addr[2],2'h2}],
                dummy_iccm_preloader.ram [addr[16:3]] [{addr[2],2'h1}],
                dummy_iccm_preloader.ram [addr[16:3]] [{addr[2],2'h0}]};
        //data = {caliptra_top_dut.imem.mem[addr+3],caliptra_top_dut.imem.mem[addr+2],caliptra_top_dut.imem.mem[addr+1],caliptra_top_dut.imem.mem[addr]};
        slam_iccm_ram(addr, data == 0 ? 0 : {riscv_ecc32(data),data});
    end
    $display("ICCM pre-load completed");

endtask


task preload_dccm;
    bit[31:0] data;
    bit[31:0] addr, saddr, eaddr;

    /*
    addresses:
     0x0000_7ff8 - DCCM start address to load
     0x0000_7ffc - DCCM end address to load
    */
    `ifndef VERILATOR
    init_dccm();
    `endif
    addr = 'h0000_7ff8;
    // FIXME hardcoded address indices?
    saddr = {imem_inst1.ram [addr[14:3]] [{addr[2],2'h3}],
             imem_inst1.ram [addr[14:3]] [{addr[2],2'h2}],
             imem_inst1.ram [addr[14:3]] [{addr[2],2'h1}],
             imem_inst1.ram [addr[14:3]] [{addr[2],2'h0}]};
    if (saddr < `RV_DCCM_SADR || saddr > `RV_DCCM_EADR) return;
    `ifndef RV_DCCM_ENABLE
        $display("********************************************************");
        $display("DCCM preload: there is no DCCM in SweRV, terminating !!!");
        $display("********************************************************");
        $finish;
    `endif
    addr += 4;
    eaddr = {imem_inst1.ram [addr[14:3]] [{addr[2],2'h3}],
             imem_inst1.ram [addr[14:3]] [{addr[2],2'h2}],
             imem_inst1.ram [addr[14:3]] [{addr[2],2'h1}],
             imem_inst1.ram [addr[14:3]] [{addr[2],2'h0}]};
    $display("DCCM pre-load from %h to %h", saddr, eaddr);

    for(addr=saddr; addr < eaddr; addr+=4) begin
        // FIXME hardcoded address indices?
        data = {dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h3}],
                dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h2}],
                dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h1}],
                dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h0}]};
        slam_dccm_ram(addr, data == 0 ? 0 : {riscv_ecc32(data),data});
    end
    $display("DCCM pre-load completed");

endtask



`define ICCM_PATH swerv_sram_export_inst.Gen_iccm_enable
`ifdef VERILATOR
`define DRAM(bk) swerv_sram_export_inst.Gen_dccm_enable.dccm_loop[bk].ram.ram_core
`define IRAM(bk) `ICCM_PATH.iccm_loop[bk].iccm_bank.ram_core
`else
`define DRAM(bk) swerv_sram_export_inst.Gen_dccm_enable.dccm_loop[bk].dccm.dccm_bank.ram_core
`define IRAM(bk) `ICCM_PATH.iccm_loop[bk].iccm.iccm_bank.ram_core
`endif


task slam_dccm_ram(input [31:0] addr, input[38:0] data);
    int bank, indx;
    bank = get_dccm_bank(addr, indx);
    `ifdef RV_DCCM_ENABLE
    case(bank)
    0: `DRAM(0)[indx] = data;
    1: `DRAM(1)[indx] = data;
    `ifdef RV_DCCM_NUM_BANKS_4
    2: `DRAM(2)[indx] = data;
    3: `DRAM(3)[indx] = data;
    `endif
    `ifdef RV_DCCM_NUM_BANKS_8
    2: `DRAM(2)[indx] = data;
    3: `DRAM(3)[indx] = data;
    4: `DRAM(4)[indx] = data;
    5: `DRAM(5)[indx] = data;
    6: `DRAM(6)[indx] = data;
    7: `DRAM(7)[indx] = data;
    `endif
    endcase
    `endif
    //$display("Writing bank %0d indx=%0d A=%h, D=%h",bank, indx, addr, data);
endtask


task slam_iccm_ram( input[31:0] addr, input[38:0] data);
    int bank, idx;

    bank = get_iccm_bank(addr, idx);
    `ifdef RV_ICCM_ENABLE
    case(bank) // {
      0: `IRAM(0)[idx] = data;
      1: `IRAM(1)[idx] = data;
     `ifdef RV_ICCM_NUM_BANKS_4
      2: `IRAM(2)[idx] = data;
      3: `IRAM(3)[idx] = data;
     `endif
     `ifdef RV_ICCM_NUM_BANKS_8
      2: `IRAM(2)[idx] = data;
      3: `IRAM(3)[idx] = data;
      4: `IRAM(4)[idx] = data;
      5: `IRAM(5)[idx] = data;
      6: `IRAM(6)[idx] = data;
      7: `IRAM(7)[idx] = data;
     `endif

     `ifdef RV_ICCM_NUM_BANKS_16
      2: `IRAM(2)[idx] = data;
      3: `IRAM(3)[idx] = data;
      4: `IRAM(4)[idx] = data;
      5: `IRAM(5)[idx] = data;
      6: `IRAM(6)[idx] = data;
      7: `IRAM(7)[idx] = data;
      8: `IRAM(8)[idx] = data;
      9: `IRAM(9)[idx] = data;
      10: `IRAM(10)[idx] = data;
      11: `IRAM(11)[idx] = data;
      12: `IRAM(12)[idx] = data;
      13: `IRAM(13)[idx] = data;
      14: `IRAM(14)[idx] = data;
      15: `IRAM(15)[idx] = data;
     `endif
    endcase // }
    `endif
endtask

task init_iccm;
    `ifdef RV_ICCM_ENABLE
        `IRAM(0) = '{default:39'h0};
        `IRAM(1) = '{default:39'h0};
    `ifdef RV_ICCM_NUM_BANKS_4
        `IRAM(2) = '{default:39'h0};
        `IRAM(3) = '{default:39'h0};
    `endif
    `ifdef RV_ICCM_NUM_BANKS_8
        `IRAM(4) = '{default:39'h0};
        `IRAM(5) = '{default:39'h0};
        `IRAM(6) = '{default:39'h0};
        `IRAM(7) = '{default:39'h0};
    `endif

    `ifdef RV_ICCM_NUM_BANKS_16
        `IRAM(4) = '{default:39'h0};
        `IRAM(5) = '{default:39'h0};
        `IRAM(6) = '{default:39'h0};
        `IRAM(7) = '{default:39'h0};
        `IRAM(8) = '{default:39'h0};
        `IRAM(9) = '{default:39'h0};
        `IRAM(10) = '{default:39'h0};
        `IRAM(11) = '{default:39'h0};
        `IRAM(12) = '{default:39'h0};
        `IRAM(13) = '{default:39'h0};
        `IRAM(14) = '{default:39'h0};
        `IRAM(15) = '{default:39'h0};
     `endif
    `endif
endtask

task init_dccm;
    `ifdef RV_DCCM_ENABLE
        `DRAM(0) = '{default:39'h0};
        `DRAM(1) = '{default:39'h0};
    `ifdef RV_DCCM_NUM_BANKS_4
        `DRAM(2) = '{default:39'h0};
        `DRAM(3) = '{default:39'h0};
    `endif
    `ifdef RV_DCCM_NUM_BANKS_8
        `DRAM(4) = '{default:39'h0};
        `DRAM(5) = '{default:39'h0};
        `DRAM(6) = '{default:39'h0};
        `DRAM(7) = '{default:39'h0};
    `endif
    `endif
endtask

task dump_memory_contents;
    input [2:0] mem_type;
    input [31:0] start_addr;
    input [31:0] end_addr;

    bit [31:0] addr;
    bit [38:0] ecc_data;
    bit [7:0] data;
    string outfile;

    int bank, indx; 

    int of;

    //$display(`DRAM);

    case (mem_type)
        MEMTYPE_LMEM:  outfile = "lmem_data_dump.hex";
        MEMTYPE_DCCM:  outfile = "dccm_data_dump.hex";
        MEMTYPE_ICCM:  outfile = "iccm_data_dump.hex";
        default:       outfile = "";
    endcase

    of = $fopen(outfile, "w");
    for (addr = start_addr; addr <= start_addr + 112; addr = addr + 1) begin
        case (mem_type)
            MEMTYPE_LMEM: data = `LMEM[addr[31:2]][addr[1:0]];
            MEMTYPE_DCCM: begin
                            bank = get_dccm_bank(addr, indx);
                            `ifdef RV_DCCM_ENABLE
                            case(bank)
                                0: ecc_data = `DRAM(0)[indx];
                                1: ecc_data = `DRAM(1)[indx];
                                `ifdef RV_DCCM_NUM_BANKS_4
                                2: ecc_data = `DRAM(2)[indx];
                                3: ecc_data = `DRAM(3)[indx];
                                `endif
                                `ifdef RV_DCCM_NUM_BANKS_8
                                2: ecc_data = `DRAM(2)[indx];
                                3: ecc_data = `DRAM(3)[indx];
                                4: ecc_data = `DRAM(4)[indx];
                                5: ecc_data = `DRAM(5)[indx];
                                6: ecc_data = `DRAM(6)[indx];
                                7: ecc_data = `DRAM(7)[indx];
                                `endif
                            endcase
                            `endif
            end
            MEMTYPE_ICCM: begin
                            bank = get_iccm_bank(addr, indx);
                            `ifdef RV_ICCM_ENABLE
                            case(bank) // {
                                0: ecc_data =  `IRAM(0)[indx];
                                1: ecc_data = `IRAM(1)[indx];
                                `ifdef RV_ICCM_NUM_BANKS_4
                                2: ecc_data = `IRAM(2)[indx];
                                3: ecc_data = `IRAM(3)[indx];
                                `endif
                                `ifdef RV_ICCM_NUM_BANKS_8
                                2: ecc_data = `IRAM(2)[indx];
                                3: ecc_data = `IRAM(3)[indx];
                                4: ecc_data = `IRAM(4)[indx];
                                5: ecc_data = `IRAM(5)[indx];
                                6: ecc_data = `IRAM(6)[indx];
                                7: ecc_data = `IRAM(7)[indx];
                                `endif
                                `ifdef RV_ICCM_NUM_BANKS_16
                                2: ecc_data = `IRAM(2)[indx];
                                3: ecc_data = `IRAM(3)[indx];
                                4: ecc_data = `IRAM(4)[indx];
                                5: ecc_data = `IRAM(5)[indx];
                                6: ecc_data = `IRAM(6)[indx];
                                7: ecc_data = `IRAM(7)[indx];
                                8: ecc_data = `IRAM(8)[indx];
                                9: ecc_data = `IRAM(9)[indx];
                                10: ecc_data = `IRAM(10)[indx];
                                11: ecc_data = `IRAM(11)[indx];
                                12: ecc_data = `IRAM(12)[indx];
                                13: ecc_data = `IRAM(13)[indx];
                                14: ecc_data = `IRAM(14)[indx];
                                15: ecc_data = `IRAM(15)[indx];
                                `endif
                            endcase // }
                            `endif
            end
            default: begin
                data = 0;
                bank = 0;
                ecc_data = 0;
            end
        endcase

        case (mem_type)
            MEMTYPE_LMEM: begin 
                            if ((addr & 'hF) == 0) begin
                                $fwrite(of, "%0x:\t%x ", addr, data);
                            end
                            else if ((addr & 'hF) == 'hF) begin
                                $fwrite(of, "%x\n", data);
                            end
                            else begin
                                $fwrite(of, "%x ", data);
                            end
            end
            MEMTYPE_DCCM,
            MEMTYPE_ICCM: begin
                            if ((addr & 'hF) == 0) begin
                                $fwrite(of, "%0x:\t%x ", addr, ecc_data);
                            end
                            else if ((addr & 'hF) == 'hC) begin
                                $fwrite(of, "%x\n", ecc_data);
                            end
                            else if (((addr & 'hF) == 'h4)|| ((addr & 'hF) == 'h8)) begin
                                $fwrite(of, "%x ", ecc_data);
                            end
            end
            default: begin end
        endcase
    end
endtask



function[6:0] riscv_ecc32(input[31:0] data);
    reg[6:0] synd;
    synd[0] = ^(data & 32'h56aa_ad5b);
    synd[1] = ^(data & 32'h9b33_366d);
    synd[2] = ^(data & 32'he3c3_c78e);
    synd[3] = ^(data & 32'h03fc_07f0);
    synd[3] = ^(data & 32'h03fc_07f0);
    synd[4] = ^(data & 32'h03ff_f800);
    synd[5] = ^(data & 32'hfc00_0000);
    synd[6] = ^{data, synd[5:0]};
    return synd;
endfunction

function int get_dccm_bank(input[31:0] addr,  output int bank_idx);
    `ifdef RV_DCCM_NUM_BANKS_2
        bank_idx = int'(addr[`RV_DCCM_BITS-1:3]);
        return int'( addr[2]);
    `elsif RV_DCCM_NUM_BANKS_4
        bank_idx = int'(addr[`RV_DCCM_BITS-1:4]);
        return int'(addr[3:2]);
    `elsif RV_DCCM_NUM_BANKS_8
        bank_idx = int'(addr[`RV_DCCM_BITS-1:5]);
        return int'( addr[4:2]);
    `endif
endfunction

function int get_iccm_bank(input[31:0] addr,  output int bank_idx);
    `ifdef RV_DCCM_NUM_BANKS_2
        bank_idx = int'(addr[`RV_DCCM_BITS-1:3]);
        return int'( addr[2]);
    `elsif RV_ICCM_NUM_BANKS_4
        bank_idx = int'(addr[`RV_ICCM_BITS-1:4]);
        return int'(addr[3:2]);
    `elsif RV_ICCM_NUM_BANKS_8
        bank_idx = int'(addr[`RV_ICCM_BITS-1:5]);
        return int'( addr[4:2]);
    `elsif RV_ICCM_NUM_BANKS_16
        bank_idx = int'(addr[`RV_ICCM_BITS-1:6]);
        return int'( addr[5:2]);
    `endif
endfunction

/* verilator lint_off CASEINCOMPLETE */
`include "dasm.svi"
/* verilator lint_on CASEINCOMPLETE */

endmodule
