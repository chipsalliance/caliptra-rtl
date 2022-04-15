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
module rust_top_tb;
`else
module rust_top_tb ( 
    input bit core_clk,
    input bit rst_l,
    input bit porst_l 
    ); 
`endif
    
`ifndef VERILATOR
    bit                         core_clk;
`endif

    logic                       nmi_int;
    logic        [31:0]         reset_vector;
    logic        [31:0]         nmi_vector;
    logic        [31:1]         jtag_id;
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

    logic                       rst_l;
    logic                       porst_l;

    wire[63:0] WriteData;
    string                      abi_reg[32]; // ABI register names

`define DEC rust_top_dut.rvtop.swerv.dec

`define LMEM `RUST_RV_TOP.lmem.mem 

    parameter MEMTYPE_LMEM = 3'h1;
    parameter MEMTYPE_DCCM = 3'h2;
    parameter MEMTYPE_ICCM = 3'h3;

    logic [2:0] memtype; 

    assign mailbox_write = rust_top_dut.lmem.mailbox_write;
    assign WriteData = rust_top_dut.lmem.WriteData;
    assign mailbox_data_val = WriteData[7:0] > 8'h5 && WriteData[7:0] < 8'h7f;

    parameter MAX_CYCLES = 2_000_000;

    integer fd, tp, el, sm, i;

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
        end
        // End Of test monitor
        if(mailbox_write && WriteData[7:0] == 8'hff) begin
            $display("* TESTCASE PASSED");
            $display("\nFinished : minstret = %0d, mcycle = %0d", `DEC.tlu.minstretl[31:0],`DEC.tlu.mcyclel[31:0]);
            $display("See \"exec.log\" for execution trace with register updates..\n");
            dump_memory_contents(MEMTYPE_LMEM, 32'h8000_0110, 32'h8000_0180);
            dump_memory_contents(MEMTYPE_DCCM, `RV_DCCM_SADR, `RV_DCCM_EADR);
            dump_memory_contents(MEMTYPE_ICCM, `RV_ICCM_SADR, `RV_ICCM_EADR);
            $finish;
        end
        else if(mailbox_write && WriteData[7:0] == 8'h1) begin
            $display("* TESTCASE FAILED");
            dump_memory_contents(MEMTYPE_LMEM, 32'h8000_0110, 32'h8000_0180);
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
        if (trace_rv_i_valid_ip) begin
           $fwrite(tp,"%b,%h,%h,%0h,%0h,3,%b,%h,%h,%b\n", trace_rv_i_valid_ip, 0, trace_rv_i_address_ip,
                  0, trace_rv_i_insn_ip,trace_rv_i_exception_ip,trace_rv_i_ecause_ip,
                  trace_rv_i_tval_ip,trace_rv_i_interrupt_ip);
           // Basic trace - no exception register updates
           // #1 0 ee000000 b0201073 c 0b02       00000000
           commit_count++;
           $fwrite (el, "%10d : %8s 0 %h %h%13s ; %s\n", cycleCnt, $sformatf("#%0d",commit_count),
                        trace_rv_i_address_ip, trace_rv_i_insn_ip,
                        (wb_dest !=0 && wb_valid)?  $sformatf("%s=%h", abi_reg[wb_dest], wb_data) : "             ",
                        dasm(trace_rv_i_insn_ip, trace_rv_i_address_ip, wb_dest & {5{wb_valid}}, wb_data)
                   );
        end
        if(`DEC.dec_nonblock_load_wen) begin
            $fwrite (el, "%10d : %32s=%h ; nbL\n", cycleCnt, abi_reg[`DEC.dec_nonblock_load_waddr], `DEC.lsu_nonblock_load_data);
            rust_top_tb.gpr[0][`DEC.dec_nonblock_load_waddr] = `DEC.lsu_nonblock_load_data;
        end
        if(`DEC.exu_div_wren) begin
            $fwrite (el, "%10d : %32s=%h ; nbD\n", cycleCnt, abi_reg[`DEC.div_waddr_wb], `DEC.exu_div_result);
            rust_top_tb.gpr[0][`DEC.div_waddr_wb] = `DEC.exu_div_result;
        end
    end




    initial begin
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
    // tie offs
        jtag_id[31:28] = 4'b1;
        jtag_id[27:12] = '0;
        jtag_id[11:1]  = 11'h45;
        reset_vector = `RV_RESET_VEC;
        nmi_vector   = 32'hee000000;
        nmi_int   = 0;

        $readmemh("program.hex",  rust_top_dut.lmem.mem);
        $readmemh("program.hex",  rust_top_dut.imem.mem);
        tp = $fopen("trace_port.csv","w");
        el = $fopen("exec.log","w");
        $fwrite (el, "//   Cycle : #inst    0    pc    opcode    reg=value   ; mnemonic\n");
        fd = $fopen("console.log","w");
        commit_count = 0;
        preload_dccm();
        preload_iccm();

`ifndef VERILATOR
        if($test$plusargs("dumpon")) $dumpvars;
        forever  core_clk = #5 ~core_clk;
`endif
    end


    assign rst_l = cycleCnt > 5;
    assign porst_l = cycleCnt > 2;

   //=========================================================================-
   // DUT instance
   //=========================================================================-
rust_top rust_top_dut (
    .rst_l                  ( rst_l         ),
    .porst_l              ( porst_l       ),
    .core_clk                    ( core_clk      ),
    .reset_vector               (reset_vector),
    .nmi_vector                 (nmi_vector),
    .nmi_int                    (nmi_int),
    .jtag_id                    (jtag_id)
);



task preload_iccm;
bit[31:0] data;
bit[31:0] addr, eaddr, saddr;

/*
addresses:
 0xfffffff0 - ICCM start address to load
 0xfffffff4 - ICCM end address to load
*/
`ifndef VERILATOR
init_iccm();
`endif
addr = 'hffff_fff0;
saddr = {rust_top_dut.lmem.mem[addr+3],rust_top_dut.lmem.mem[addr+2],rust_top_dut.lmem.mem[addr+1],rust_top_dut.lmem.mem[addr]};
if ( (saddr < `RV_ICCM_SADR) || (saddr > `RV_ICCM_EADR)) return;
`ifndef RV_ICCM_ENABLE
    $display("********************************************************");
    $display("ICCM preload: there is no ICCM in SweRV, terminating !!!");
    $display("********************************************************");
    $finish;
`endif
addr += 4;
eaddr = {rust_top_dut.lmem.mem[addr+3],rust_top_dut.lmem.mem[addr+2],rust_top_dut.lmem.mem[addr+1],rust_top_dut.lmem.mem[addr]};
$display("ICCM pre-load from %h to %h", saddr, eaddr);

for(addr= saddr; addr <= eaddr; addr+=4) begin
    data = {rust_top_dut.imem.mem[addr+3],rust_top_dut.imem.mem[addr+2],rust_top_dut.imem.mem[addr+1],rust_top_dut.imem.mem[addr]};
    slam_iccm_ram(addr, data == 0 ? 0 : {riscv_ecc32(data),data});
end

endtask


task preload_dccm;
bit[31:0] data;
bit[31:0] addr, saddr, eaddr;

/*
addresses:
 0xffff_fff8 - DCCM start address to load
 0xffff_fffc - DCCM end address to load
*/
`ifndef VERILATOR
init_dccm();
`endif
addr = 'hffff_fff8;
saddr = {rust_top_dut.lmem.mem[addr+3],rust_top_dut.lmem.mem[addr+2],rust_top_dut.lmem.mem[addr+1],rust_top_dut.lmem.mem[addr]};
if (saddr < `RV_DCCM_SADR || saddr > `RV_DCCM_EADR) return;
`ifndef RV_DCCM_ENABLE
    $display("********************************************************");
    $display("DCCM preload: there is no DCCM in SweRV, terminating !!!");
    $display("********************************************************");
    $finish;
`endif
addr += 4;
eaddr = {rust_top_dut.lmem.mem[addr+3],rust_top_dut.lmem.mem[addr+2],rust_top_dut.lmem.mem[addr+1],rust_top_dut.lmem.mem[addr]};
$display("DCCM pre-load from %h to %h", saddr, eaddr);

for(addr=saddr; addr <= eaddr; addr+=4) begin
    data = {rust_top_dut.lmem.mem[addr+3],rust_top_dut.lmem.mem[addr+2],rust_top_dut.lmem.mem[addr+1],rust_top_dut.lmem.mem[addr]};
    slam_dccm_ram(addr, data == 0 ? 0 : {riscv_ecc32(data),data});
end

endtask



`define ICCM_PATH `RV_TOP.mem.iccm.iccm
`ifdef VERILATOR
`define DRAM(bk) rust_top_dut.rvtop.mem.Gen_dccm_enable.dccm.mem_bank[bk].ram.ram_core
`define IRAM(bk) `ICCM_PATH.mem_bank[bk].iccm_bank.ram_core
`else
`define DRAM(bk) rust_top_dut.rvtop.mem.Gen_dccm_enable.dccm.mem_bank[bk].dccm.dccm_bank.ram_core
`define IRAM(bk) `ICCM_PATH.mem_bank[bk].iccm.iccm_bank.ram_core
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
            MEMTYPE_LMEM: data = `LMEM[addr];
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
        if ((addr & 'hF) == 'h0)
            $fwrite(of, "%0x\t", addr);
        else if ( (addr & 'hF) == 'hF) begin
            case (mem_type)
                MEMTYPE_LMEM: $fwrite(of, "%x\n", data);
                MEMTYPE_DCCM,
                MEMTYPE_ICCM: $fwrite(of, "%x\n", ecc_data);
            endcase
        end
        else begin
            case (mem_type)
                MEMTYPE_LMEM: $fwrite(of, "%x ", data);
                MEMTYPE_DCCM,
                MEMTYPE_ICCM: $fwrite(of, "%x ", ecc_data);
            endcase
        end
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
