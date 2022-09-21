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

`ifndef VERILATOR
module caliptra_top_tb;
`else
module caliptra_top_tb ( 
    input bit core_clk,
    input bit rst_l
    ); 
`endif

    // Time formatting for %t in display tasks
    // -9 = ns units
    // 3  = 3 bits of precision (to the ps)
    // "ns" = nanosecond suffix for output time values
    // 15 = 15 bits minimum field width
    initial $timeformat(-9, 3, " ns", 15); // up to 99ms representable in this width

`ifndef VERILATOR
    bit                         core_clk;
`endif

    int                         cycleCnt;
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

    logic                       cptra_pwrgood;
    logic                       cptra_rst_b;

    logic [7:0][31:0]           cptra_obf_key;
    logic [0:7][31:0]           cptra_obf_key_uds, cptra_obf_key_fe;
    
    logic [0:11][31:0]          cptra_uds_tb;
    logic [0:31][31:0]          cptra_fe_tb;
    wire[31:0] WriteData;
    string                      abi_reg[32]; // ABI register names
    //jtag interface
    logic                       jtag_tck;    // JTAG clk
    logic                       jtag_tms;    // JTAG TMS
    logic                       jtag_tdi;    // JTAG tdi
    logic                       jtag_trst_n; // JTAG Reset
    logic                       jtag_tdo;    // JTAG TDO
    //APB Interface
    logic [`APB_ADDR_WIDTH-1:0] PADDR;
    logic [3:0]                 PPROT;
    logic                       PSEL;
    logic                       PENABLE;
    logic                       PWRITE;
    logic [`APB_DATA_WIDTH-1:0] PWDATA;
    logic [`APB_USER_WIDTH-1:0] PAUSER;

    logic                       PREADY;
    logic                       PSLVERR;
    logic [`APB_DATA_WIDTH-1:0] PRDATA;

    logic ready_for_fuses;

`define DEC caliptra_top_dut.rvtop.swerv.dec

`define LMEM caliptra_top_dut.mbox_top1.mbox1.mbox_ram1.ram 

    el2_mem_if el2_mem_export (.rst_b(cptra_rst_b)); // clock is provided inside the SweRV processor

    parameter MEMTYPE_LMEM = 3'h1;
    parameter MEMTYPE_DCCM = 3'h2;
    parameter MEMTYPE_ICCM = 3'h3;

    parameter MBOX_UDS_ADDR = 32'h3003_0200;
    parameter MBOX_FE_ADDR  = 32'h3003_0230;
    parameter MBOX_FUSE_DONE_ADDR = 32'h3003_0394;

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
    //         8'h80: 8'hfa - Clear the interrupt at sim_irq_gen for vector (WriteData-8'h80)
    //         8'hfb        - Set the isr_active bit
    //         8'hfc        - Clear the isr_active bit
    //         8'hfd        - Force reset on sim_irq_gen
    //         8'hfe        - Release reset on sim_irq_gen
    //         8'hff        - End the simulation with a Success status
    assign mailbox_write = caliptra_top_dut.mbox_top1.mbox_reg1.field_combo.FLOW_STATUS.status.load_next;
    assign WriteData = caliptra_top_dut.mbox_top1.mbox_reg1.field_combo.FLOW_STATUS.status.next;
    assign mailbox_data_val = WriteData[7:0] > 8'h5 && WriteData[7:0] < 8'h7f;

    parameter MAX_CYCLES = 20_000_000;

    integer fd, tp, el, sm, i;
    integer ifu_p, lsu_p, sl_p[`AHB_SLAVES_NUM];

    integer j;

    string slaveLog_fileName[`AHB_SLAVES_NUM];

`ifndef VERILATOR
    always
    begin : clk_gen
      core_clk = #5 ~core_clk;
    end // clk_gen
`endif
    
    logic isr_active;
    initial begin
        isr_active = 1'b0;
        force caliptra_top_dut.i_irq_gen.rst_n = 1'b0;
        forever begin
            @(negedge core_clk)
            if ((WriteData[7:0] == 8'hfe) && mailbox_write) begin
                release caliptra_top_dut.i_irq_gen.rst_n;
                $display("releasing irq rst_n");
                @(negedge core_clk)
                $display("irq rst_n value: 0x%x", caliptra_top_dut.i_irq_gen.rst_n);
            end
            else if ((WriteData[7:0] == 8'hfd) && mailbox_write) begin
                force caliptra_top_dut.i_irq_gen.rst_n = 1'b0;
                $display("force assertion of irq rst_n");
            end
            else if ((WriteData[7:0] == 8'hfc) && mailbox_write) begin
                isr_active = 1'b0;
            end
            else if ((WriteData[7:0] == 8'hfb) && mailbox_write) begin
                isr_active = 1'b1;
            end
            else if ((WriteData[7:0] inside {[8'h80:8'hfa]}) && mailbox_write) begin
                force caliptra_top_dut.i_irq_gen.intr_clr = `RV_PIC_TOTAL_INT'(1) << (WriteData[7:0] - 8'h80);
                @(negedge core_clk)
                release caliptra_top_dut.i_irq_gen.intr_clr;
            end
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

    // IFU Master monitor
    always @(posedge core_clk) begin
        $fstrobe(ifu_p, "%10d : 0x%0h %h %b %h %h %h %b 0x%08h_%08h %b %b\n", cycleCnt, 
                        caliptra_top_dut.ic_haddr, caliptra_top_dut.ic_hburst, caliptra_top_dut.ic_hmastlock, 
                        caliptra_top_dut.ic_hprot, caliptra_top_dut.ic_hsize, caliptra_top_dut.ic_htrans, 
                        caliptra_top_dut.ic_hwrite, caliptra_top_dut.ic_hrdata[63:32], caliptra_top_dut.ic_hrdata[31:0], 
                        caliptra_top_dut.ic_hready, caliptra_top_dut.ic_hresp);
    end

    // LSU Master monitor
    always @(posedge core_clk) begin
        $fstrobe(lsu_p, "%10d : 0x%0h %h %b %h %h %h %b 0x%08h_%08h 0x%08h_%08h %b %b\n", cycleCnt, 
                        caliptra_top_dut.s_smaster.haddr, caliptra_top_dut.s_smaster.hburst, caliptra_top_dut.s_smaster.hmastlock, 
                        caliptra_top_dut.s_smaster.hprot, caliptra_top_dut.s_smaster.hsize, caliptra_top_dut.s_smaster.htrans, 
                        caliptra_top_dut.s_smaster.hwrite, caliptra_top_dut.s_smaster.hrdata[63:32], caliptra_top_dut.s_smaster.hrdata[31:0], 
                        caliptra_top_dut.s_smaster.hwdata[63:32], caliptra_top_dut.s_smaster.hwdata[31:0], 
                        caliptra_top_dut.s_smaster.hready, caliptra_top_dut.s_smaster.hresp);
    end

    // AHB slave interfaces monitor
    genvar sl_i;
    generate
        for (sl_i = 0; sl_i < `AHB_SLAVES_NUM; sl_i = sl_i + 1) begin
            always @(posedge core_clk) begin
                $fstrobe(sl_p[sl_i], "%10d : 0x%0h %h %b %h %h %h %b 0x%08h_%08h 0x%08h_%08h %b %b %b %b\n", cycleCnt, 
                        caliptra_top_dut.s_slave[sl_i].haddr, caliptra_top_dut.s_slave[sl_i].hburst, caliptra_top_dut.s_slave[sl_i].hmastlock, 
                        caliptra_top_dut.s_slave[sl_i].hprot, caliptra_top_dut.s_slave[sl_i].hsize, caliptra_top_dut.s_slave[sl_i].htrans, 
                        caliptra_top_dut.s_slave[sl_i].hwrite, caliptra_top_dut.s_slave[sl_i].hrdata[63:32], caliptra_top_dut.s_slave[sl_i].hrdata[31:0], 
                        caliptra_top_dut.s_slave[sl_i].hwdata[63:32], caliptra_top_dut.s_slave[sl_i].hwdata[31:0], 
                        caliptra_top_dut.s_slave[sl_i].hready, caliptra_top_dut.s_slave[sl_i].hreadyout, caliptra_top_dut.s_slave[sl_i].hresp, caliptra_top_dut.s_slave[sl_i].hsel);
            end
        end
    endgenerate


    initial begin
        cptra_pwrgood = 1'b0;
        cptra_rst_b = 1'b0;
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
        PADDR = '0;
        PSEL = '0;
        PENABLE = '0;
        PWRITE = '0;
        PWDATA = '0;
        PAUSER = '0;
        PPROT = '0;

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

        //assert power good
        repeat (5) @(posedge core_clk);
        cptra_pwrgood = 1'b1;

        //de-assert reset
        repeat (5) @(posedge core_clk);
        cptra_rst_b = 1'b1;

        //wait for fuse indication
        wait (ready_for_fuses == 1'b1);

        //load fuses
        for (int i = 0; i < 12; i++)begin
            write_single_word_apb(MBOX_UDS_ADDR + i*4, cptra_uds_tb[i]);
        end
        for (int i = 0; i < 32; i++)begin
            write_single_word_apb(MBOX_FE_ADDR + i*4, cptra_fe_tb[i]);
        end
        //set fuse done
        write_single_word_apb(MBOX_FUSE_DONE_ADDR, 32'h00000001);  

        $readmemh("program.hex",  caliptra_top_dut.imem.sram_inst.ram,0,32'h00008000);
        $readmemh("mailbox.hex",  caliptra_top_dut.mbox_top1.mbox1.mbox_ram1.ram,0,32'h0002_0000);
        $readmemh("dccm.hex",     dummy_dccm_preloader.ram,0,32'h0001_0000);
        tp = $fopen("trace_port.csv","w");
        el = $fopen("exec.log","w");
        ifu_p = $fopen("ifu_master_ahb_trace.log", "w");
        lsu_p = $fopen("lsu_master_ahb_trace.log", "w");
        $fwrite (el, "//   Cycle : #inst    0    pc    opcode    reg=value   ; mnemonic\n");
        $fwrite(ifu_p, "//   Cycle: ic_haddr     ic_hburst     ic_hmsatlock     ic_hprot     ic_hsize     ic_htrans     ic_hwrite     ic_hrdata     ic_hwdata     ic_hready     ic_hresp\n");
        $fwrite(lsu_p, "//   Cycle: lsu_haddr     lsu_hburst     lsu_hmsatlock     lsu_hprot     lsu_hsize     lsu_htrans     lsu_hwrite     lsu_hrdata     lsu_hwdata     lsu_hready     lsu_hresp\n");

        for (j = 0; j < `AHB_SLAVES_NUM; j = j + 1) begin
            slaveLog_fileName[j] = {$sformatf("slave%0d_ahb_trace.log", j)};
            sl_p[j] = $fopen(slaveLog_fileName[j], "w");
            $fwrite(sl_p[j], "//   Cycle: haddr     hburst     hmsatlock     hprot     hsize     htrans     hwrite     hrdata     hwdata     hready     hreadyout     hresp\n");
        end

        fd = $fopen("console.log","w");
        commit_count = 0;
        preload_dccm();
        preload_iccm();

`ifndef VERILATOR
        if($test$plusargs("dumpon")) $dumpvars;
`endif
    end


   //=========================================================================-
   // DUT instance
   //=========================================================================-
caliptra_top caliptra_top_dut (
    .cptra_pwrgood              (cptra_pwrgood),
    .cptra_rst_b                (cptra_rst_b),
    .core_clk                   (core_clk),

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
    .ready_for_fw_push(),
    .ready_for_runtime(),

    .mailbox_data_avail(),
    .mailbox_flow_done(),
    .BootFSM_BrkPoint('x), //FIXME TIE-OFF

    .generic_input_wires('x), //FIXME TIE-OFF
    .generic_output_wires(),

    .security_state('x) //FIXME TIE-OFF
);

caliptra_swerv_sram_export swerv_sram_export_inst (
    .el2_mem_export(el2_mem_export.top)
);

// This is used to load the generated DCCM hexfile prior to
// running slam_dccm_ram
caliptra_sram #(
     .DEPTH     (8192         ), // 64KiB
     .DATA_WIDTH(64           ),
     .ADDR_WIDTH($clog2(8192) )

) dummy_dccm_preloader (
    .clk_i   (core_clk),

    .we_i    (        ),
    .waddr_i (        ),
    .wdata_i (        ),
    .rdaddr_i(        ),
    .rdata_o (        )
);


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
    saddr = {caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h3}],
             caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h2}],
             caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h1}],
             caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h0}]};
    //saddr = {caliptra_top_dut.imem.sram_inst.ram[addr+3],caliptra_top_dut.imem.mem[addr+2],caliptra_top_dut.imem.mem[addr+1],caliptra_top_dut.imem.mem[addr]};
    if ( (saddr < `RV_ICCM_SADR) || (saddr > `RV_ICCM_EADR)) return;
    `ifndef RV_ICCM_ENABLE
        $display("********************************************************");
        $display("ICCM preload: there is no ICCM in SweRV, terminating !!!");
        $display("********************************************************");
        $finish;
    `endif
    addr += 4;
    eaddr = {caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h3}],
             caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h2}],
             caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h1}],
             caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h0}]};
    //eaddr = {caliptra_top_dut.imem.mem[addr+3],caliptra_top_dut.imem.mem[addr+2],caliptra_top_dut.imem.mem[addr+1],caliptra_top_dut.imem.mem[addr]};
    $display("ICCM pre-load from %h to %h", saddr, eaddr);

    for(addr= saddr; addr <= eaddr; addr+=4) begin
        // FIXME hardcoded address indices?
        //       trying to read offset ee00_0000 from within mbox, out of bounds - error?
        data = {caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h3}],
                caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h2}],
                caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h1}],
                caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h0}]};
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
    saddr = {caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h3}],
             caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h2}],
             caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h1}],
             caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h0}]};
    if (saddr < `RV_DCCM_SADR || saddr > `RV_DCCM_EADR) return;
    `ifndef RV_DCCM_ENABLE
        $display("********************************************************");
        $display("DCCM preload: there is no DCCM in SweRV, terminating !!!");
        $display("********************************************************");
        $finish;
    `endif
    addr += 4;
    eaddr = {caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h3}],
             caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h2}],
             caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h1}],
             caliptra_top_dut.imem.sram_inst.ram [addr[14:3]] [{addr[2],2'h0}]};
    $display("DCCM pre-load from %h to %h", saddr, eaddr);

    for(addr=saddr; addr <= eaddr; addr+=4) begin
        // FIXME hardcoded address indices?
        data = {dummy_dccm_preloader.ram [addr[15:3]] [{addr[2],2'h3}],
                dummy_dccm_preloader.ram [addr[15:3]] [{addr[2],2'h2}],
                dummy_dccm_preloader.ram [addr[15:3]] [{addr[2],2'h1}],
                dummy_dccm_preloader.ram [addr[15:3]] [{addr[2],2'h0}]};
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

//apb interface tasks
//----------------------------------------------------------------
// write_single_word_apb()
//
// Write the given word to the DUT using the AHB-lite interface.
//----------------------------------------------------------------
task write_single_word_apb(input [31 : 0] address, input [31 : 0] word);
begin
    @(posedge core_clk);
    PADDR      <= address;
    PSEL       <= 1;
    PENABLE    <= 0;
    PWRITE     <= 1;
    PWDATA     <= word;
    PAUSER     <= 0;
    wait(PREADY == 1'b1);

    @(posedge core_clk);
    PENABLE    <= 1;
    wait(PREADY == 1'b1);

    @(posedge core_clk);
    PSEL       <= 0;
    PENABLE    <= 0;
end
endtask // write_single_word_apb

task read_single_word_apb(input [31 : 0] address);
begin
    @(posedge core_clk);
    PADDR      <= address;
    PSEL       <= 1;
    PENABLE    <= 0;
    PWRITE     <= 0;
    PWDATA     <= 0;
    PAUSER     <= 0;
    wait(PREADY == 1'b1);

    @(posedge core_clk);
    PENABLE    <= 1;
    wait(PREADY == 1'b1);

    @(posedge core_clk);
    PSEL       <= 0;
    PENABLE    <= 0;
end
endtask // read_single_word_apb

/* verilator lint_off CASEINCOMPLETE */
`include "dasm.svi"
/* verilator lint_on CASEINCOMPLETE */

endmodule
