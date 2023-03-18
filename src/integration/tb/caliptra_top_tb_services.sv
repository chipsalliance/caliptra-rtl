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

// =================== DESCRIPTION ===================
// This module provides supporting functionality that is shared between the standalone
// and UVM benches for caliptra_top.
// This includes the following:
//  - Contains all SRAM exports
//  - Mem init functions (from .hex files, with ECC functionality as applicable)
//  - RV Firmware STDOUT behavior (ASCII dump + sim kill + Error injection + interrupt + security_state)
//  - RV and internal AHB interface monitoring to activity dumps
// The purpose of this module is to centralize identical code that is shared to
// improve maintainability.
// ===================================================

`default_nettype none

`include "common_defines.sv"
`include "config_defines.svh"
`include "caliptra_reg_defines.svh"


module caliptra_top_tb_services import soc_ifc_pkg::*; #(
    parameter UVM_TB = 0
) (
    input logic                        clk,

    input logic                        cptra_rst_b,

    // Caliptra Memory Export Interface
    el2_mem_if.top                     el2_mem_export,

    //SRAM interface for mbox
    input  logic mbox_sram_cs,
    input  logic mbox_sram_we,
    input  logic [MBOX_ADDR_W-1:0] mbox_sram_addr,
    input  logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_wdata,
    output logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_rdata,

    //SRAM interface for imem
    input  logic imem_cs,
    input  logic [`CALIPTRA_IMEM_ADDR_WIDTH-1:0] imem_addr,
    output logic [`CALIPTRA_IMEM_DATA_WIDTH-1:0] imem_rdata,

    // Security State
    output var security_state_t security_state,

    // TB Controls
    output int   cycleCnt,

    //Interrupt flags
    output logic int_flag,
    output logic cycleCnt_smpl_en,

    //Reset flags
    output logic assert_hard_rst_flag,
    output logic assert_rst_flag,
    output logic deassert_hard_rst_flag,
    output logic deassert_rst_flag

);

   //=========================================================================-
   // Imports
   //=========================================================================-
    import caliptra_top_tb_pkg::*;

   //=========================================================================-
   // Parameters
   //=========================================================================-
    `ifndef VERILATOR
    int MAX_CYCLES;
    initial begin
        // To use this from the command line, add "+CLP_MAX_CYCLES=<value>"
        // to override the sim timeout
        if ($value$plusargs("CLP_MAX_CYCLES=%d", MAX_CYCLES)) begin
            $info("Received argument +CLP_MAX_CYCLES, with value %d", MAX_CYCLES);
        end
        else begin
            MAX_CYCLES = 20_000_000;
            $info("No argument provided for CLP_MAX_CYCLES, defaulting to %d", MAX_CYCLES);
        end
    end
    `else
    parameter MAX_CYCLES = 20_000_000;
    `endif

    parameter MEMTYPE_LMEM = 3'h1;
    parameter MEMTYPE_DCCM = 3'h2;
    parameter MEMTYPE_ICCM = 3'h3;

   //=========================================================================-
   // Signals
   //=========================================================================-
    logic                       mailbox_write;
    wire [31:0]                 WriteData;
    logic                       mailbox_data_val;
    int                         commit_count;

    logic                       wb_valid;
    logic [4:0]                 wb_dest;
    logic [31:0]                wb_data;

    bit                         hex_file_is_empty;
    bit                         flip_bit;

    string                      abi_reg[32]; // ABI register names

    logic [MBOX_DATA_AND_ECC_W-1:0] mbox_sram_wdata_bitflip;
    int cycleCntKillReq;

    int                         rst_cyclecnt = 0;

    logic                       cold_rst; 
    logic                       warm_rst; 
    logic                       timed_warm_rst; 
    logic                       cold_rst_done;

    logic                       inject_hmac_key;
    logic                       inject_ecc_seed;
    logic                       inject_sha_block;
    logic                       inject_random_data;

// Upwards name referencing per 23.8 of IEEE 1800-2017
`define DEC caliptra_top_dut.rvtop.veer.dec

`define LMEM mbox_ram1.ram 

   //=========================================================================-
   // STDOUT and Trace Logic
   //=========================================================================-
    // NOTE: This aperture into the mailbox is heavily overloaded right now by
    //       various firmware "STDOUT" use-cases.
    //       Functionality currently implemented at this offset is as follows
    //       (relative to the WriteData used to trigger that function):
    //         8'h0         - Do nothing
    //         8'h1         - Kill the simulation with a Failed status
    //         8'h2 : 8'h5  - Do nothing
    //         8'h6 : 8'h7E - WriteData is an ASCII character - dump to console.log
    //         8'h7F        - Do nothing
    //         8'h80: 8'h87 - Inject ECC_SEED to kv_key register
    //         8'h88: 8'h8f - Inject HMAC_KEY to kv_key register
    //         8'h90: 8'h97 - Inject SHA_BLOCK to kv_key register
    //         8'hf2        - Force clk_gating_en (to use in smoke_test only)
    //         8'hf3        - Make two clients write to KV
    //         8'hf4        - Write random data to KV entry0
    //         8'hf5        - Issue cold reset
    //         8'hf6        - Issue warm reset
    //         8'hf7        - Issue warm reset when DOE FSM is done
    //         8'hf8        - Assert interrupt flags at fixed intervals to wake up halted core
    //         8'hf9        - Lock debug in security state
    //         8'hfa        - Unlock debug in security state
    //         8'hfb        - Set the isr_active bit
    //         8'hfc        - Clear the isr_active bit
    //         8'hfd        - Toggle random SRAM single bit error injection
    //         8'hfe        - Toggle random SRAM double bit error injection
    //         8'hff        - End the simulation with a Success status
    assign mailbox_write = caliptra_top_dut.soc_ifc_top1.i_soc_ifc_reg.field_combo.CPTRA_GENERIC_OUTPUT_WIRES[0].generic_wires.load_next;
    assign WriteData = caliptra_top_dut.soc_ifc_top1.i_soc_ifc_reg.field_combo.CPTRA_GENERIC_OUTPUT_WIRES[0].generic_wires.next;
    assign mailbox_data_val = WriteData[7:0] > 8'h5 && WriteData[7:0] < 8'h7f;

    integer fd, tp, el, sm, i;
    integer ifu_p, lsu_p, sl_p[`CALIPTRA_AHB_SLAVES_NUM];

    integer j;
    string slaveLog_fileName[`CALIPTRA_AHB_SLAVES_NUM];

    logic [7:0] isr_active = 8'h0;
    always @(negedge clk) begin
        if ((WriteData[7:0] == 8'hfc) && mailbox_write) begin
            isr_active--;
        end
        else if ((WriteData[7:0] == 8'hfb) && mailbox_write) begin
            isr_active++;
        end
    end
    logic [1:0] inject_rand_sram_error = 2'b0;
    always @(negedge clk) begin
        if ((WriteData[7:0] == 8'hfd) && mailbox_write) begin
            inject_rand_sram_error ^= 2'b01;
        end
        else if ((WriteData[7:0] == 8'hfe) && mailbox_write) begin
            inject_rand_sram_error ^= 2'b10;
        end
    end

    //keyvault injection hooks
    //Inject data to KV key reg
    logic [0:11][31:0]   ecc_seed_tb    = 384'h8FA8541C82A392CA74F23ED1DBFD73541C5966391B97EA73D744B0E34B9DF59ED0158063E39C09A5A055371EDF7A5441;
    logic [0:11][31:0]   hmac_key_tb    = 384'h0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b;
    logic [0:11][31:0]   sha_block_tb   = 384'hb1eeef324b499f19eba322215fe3ce19c9f000b698d2b2dab7145015046cc86d049ee15ad59dcd1564f30112e06444cb;
    genvar dword_i, slot_id;
    generate 
        for (slot_id=0; slot_id < 8; slot_id++) begin : inject_slot_loop
            for (dword_i=0; dword_i < 12; dword_i++) begin : inject_dword_loop
                always @(negedge clk) begin
                    //inject valid seed dest and seed value to key reg
                    if(((WriteData[7:0] & 8'hf8) == 8'h80) && mailbox_write) begin
                        //$system("/home/mojtabab/workspace_aha_poc/ws1/Caliptra/src/ecc/tb/ecdsa_secp384r1.exe");
                        inject_ecc_seed <= 1'b1;
                        if (((WriteData[7:0] & 8'h07) == slot_id)) begin
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].dest_valid.we = 1'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].dest_valid.next = 6'b10000;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].last_dword.we = 1'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].last_dword.next = 'd11;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_ENTRY[slot_id][dword_i].data.we = 1'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_ENTRY[slot_id][dword_i].data.next = ecc_seed_tb[dword_i][31 : 0];
                        end
                    end
                    //inject valid hmac_key dest and hmac_key value to key reg
                    else if(((WriteData[7:0] & 8'hf8) == 8'h88) && mailbox_write) begin
                        inject_hmac_key <= 1'b1;
                        if (((WriteData[7:0] & 8'h07) == slot_id)) begin
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].dest_valid.we = 1'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].dest_valid.next = 6'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].last_dword.we = 1'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].last_dword.next = 'd11;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_ENTRY[slot_id][dword_i].data.we = 1'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_ENTRY[slot_id][dword_i].data.next = hmac_key_tb[dword_i][31 : 0];
                        end
                    end
                    //inject valid sha dest and sha_block value to key reg
                    else if(((WriteData[7:0] & 8'hf8) == 8'h90) && mailbox_write) begin
                        inject_sha_block <= 1'b1;
                        if (((WriteData[7:0] & 8'h07) == slot_id)) begin
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].dest_valid.we = 1'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].dest_valid.next = 6'b100;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].last_dword.we = 1'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].last_dword.next = 'd11;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_ENTRY[slot_id][dword_i].data.we = 1'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_ENTRY[slot_id][dword_i].data.next = sha_block_tb[dword_i][31 : 0];
                        end
                    end
                    else if((WriteData[7:0] == 8'hf4) && mailbox_write) begin
                        inject_random_data <= '1;
                        if (slot_id == 0) begin
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].dest_valid.we = 'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].dest_valid.next = (32'b10000 << `KV_REG_KEY_CTRL_0_DEST_VALID_LOW);
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].last_dword.we = 1'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].last_dword.next = 'd11;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_ENTRY[slot_id][dword_i].data.we = 1'b1;
                            force caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_ENTRY[slot_id][dword_i].data.next = $urandom();
                        end
                    end
                    else begin
                        inject_ecc_seed <= '0;
                        inject_hmac_key <= '0;
                        inject_sha_block <= '0;
                        inject_random_data <= '0;
                        release caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].dest_valid.we;
                        release caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].dest_valid.next;
                        release caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].last_dword.we;
                        release caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_CTRL[slot_id].last_dword.next;
                        release caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_ENTRY[slot_id][dword_i].data.we;
                        release caliptra_top_dut.key_vault1.kv_reg_hwif_in.KEY_ENTRY[slot_id][dword_i].data.next;
                    end
                end
            end // inject_dword_loop
        end // inject_slot_loop
    endgenerate
    

    //TIE-OFF device lifecycle
    initial security_state = '{device_lifecycle: DEVICE_PRODUCTION, debug_locked: 1'b1};
    always @(negedge clk) begin
        //lock debug mode
        if ((WriteData[7:0] == 8'hf9) && mailbox_write) begin
            security_state.debug_locked <= 1'b1;
            if (UVM_TB) $warning("WARNING! Detected FW write to manually set security_state.debug_locked, but Firmware can't do this in UVM. Use a sequence in the soc_ifc_ctrl_agent to modify this field.");
        end
        //unlock debug mode
        else if ((WriteData[7:0] == 8'hfa) && mailbox_write) begin
            security_state.debug_locked <= 1'b0;
            if (UVM_TB) $warning("WARNING! Detected FW write to manually clear security_state.debug_locked, but Firmware can't do this in UVM. Use a sequence in the soc_ifc_ctrl_agent to modify this field.");
        end
    end

    always@(negedge clk) begin
        if((WriteData == 'hf2) && mailbox_write) begin
            force caliptra_top_dut.soc_ifc_top1.clk_gating_en = 1;
        end
    end

    always@(negedge clk) begin
        if((WriteData[7:0] == 8'hf3) && mailbox_write) begin
            force caliptra_top_dut.hmac.hmac_inst.hmac_result_kv_write.kv_write.write_en = 1;
            force caliptra_top_dut.hmac.hmac_inst.hmac_result_kv_write.kv_write.write_entry = 6;
            force caliptra_top_dut.hmac.hmac_inst.hmac_result_kv_write.kv_write.write_offset = 3;
            force caliptra_top_dut.hmac.hmac_inst.hmac_result_kv_write.kv_write.write_data = 'hABCD_EF01;

            force caliptra_top_dut.doe.doe_inst.doe_fsm1.kv_write.write_en = 1;
            force caliptra_top_dut.doe.doe_inst.doe_fsm1.kv_write.write_entry = 6;
            force caliptra_top_dut.doe.doe_inst.doe_fsm1.kv_write.write_offset = 3;
            force caliptra_top_dut.doe.doe_inst.doe_fsm1.kv_write.write_data = 'h2233_4455;
        end
        else begin
            release caliptra_top_dut.hmac.hmac_inst.hmac_result_kv_write.kv_write.write_en;
            release caliptra_top_dut.hmac.hmac_inst.hmac_result_kv_write.kv_write.write_entry;
            release caliptra_top_dut.hmac.hmac_inst.hmac_result_kv_write.kv_write.write_offset;
            release caliptra_top_dut.hmac.hmac_inst.hmac_result_kv_write.kv_write.write_data;

            release caliptra_top_dut.doe.doe_inst.doe_fsm1.kv_write.write_en;
            release caliptra_top_dut.doe.doe_inst.doe_fsm1.kv_write.write_entry;
            release caliptra_top_dut.doe.doe_inst.doe_fsm1.kv_write.write_offset;
            release caliptra_top_dut.doe.doe_inst.doe_fsm1.kv_write.write_data;

        end
    end

    always@(negedge clk) begin

        if((WriteData == 'hf5) && mailbox_write) begin 
            cold_rst <= 'b1;
            rst_cyclecnt <= cycleCnt;
        end
        else if((WriteData == 'hf6) && mailbox_write) begin
            warm_rst <= 'b1;
            rst_cyclecnt <= cycleCnt;
        end
        else if((WriteData == 'hf7) && mailbox_write) begin
            timed_warm_rst <= 'b1;
        end


        if (cold_rst) begin
            assert_hard_rst_flag <= cold_rst_done ? 'b0 : 'b1;
            deassert_hard_rst_flag <= 'b0;
            deassert_rst_flag <= 'b0;
            

            if(cycleCnt == rst_cyclecnt + 'd10) begin
                assert_hard_rst_flag <= 'b0;
                deassert_hard_rst_flag <= 'b1;
                cold_rst_done <= 'b1;
            end
            else if(cycleCnt == rst_cyclecnt + 'd20) begin
                deassert_rst_flag <= 'b1;
                cold_rst <= 'b0;
                cold_rst_done <= 'b0;
            end
            else begin
                deassert_hard_rst_flag <= 'b0;
                deassert_rst_flag <= 'b0;
            end
        end
        else if(warm_rst) begin
            assert_rst_flag <= 'b1;
            deassert_rst_flag <= 'b0;
            

            if(cycleCnt == rst_cyclecnt + 'd10) begin
                assert_rst_flag <= 'b0;
                deassert_rst_flag <= 'b1;
                warm_rst <= 'b0;
            end
        end
        else if(timed_warm_rst) begin
            if((caliptra_top_dut.doe.doe_inst.doe_fsm1.kv_doe_fsm_ns == 'h5)) begin
                assert_rst_flag <= 'b1;
                deassert_rst_flag <= 'b0;
                rst_cyclecnt <= cycleCnt;
            end
            else if(assert_rst_flag && (cycleCnt == rst_cyclecnt + 'd5)) begin
                assert_rst_flag <= 0;
                deassert_rst_flag <= 1;
                timed_warm_rst <= 'b0;
            end
        end
        else begin
            deassert_hard_rst_flag <= 'b0;
            deassert_rst_flag <= 'b0;
        end
    end

    always @(negedge clk or negedge cptra_rst_b) begin
        if (!cptra_rst_b) begin
            int_flag <= 'b0;
            cycleCnt_smpl_en <= 'b0;
        end
        else if((WriteData[7:0] == 8'hf8) && mailbox_write) begin
            int_flag <= 1'b1;
            cycleCnt_smpl_en <= 'b1;
        end
        else cycleCnt_smpl_en <= 'b0;
    end


    `ifndef VERILATOR
        initial begin
            bitflip_mask_generator #(MBOX_DATA_AND_ECC_W) bitflip_gen = new();
            forever begin
                @(posedge clk)
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
        always @(posedge clk) begin
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

    initial cycleCnt = 0;
    initial cycleCntKillReq = 0;
    always @(negedge clk) begin
        cycleCnt <= cycleCnt+1;
        // Test timeout monitor
        if(cycleCnt == MAX_CYCLES && !UVM_TB) begin
            $display ("Hit max cycle count (%0d) .. stopping",cycleCnt);
            dump_memory_contents(MEMTYPE_LMEM, 32'h8000_0110, 32'h8000_0180);
            dump_memory_contents(MEMTYPE_DCCM, `RV_DCCM_SADR, `RV_DCCM_EADR);
            dump_memory_contents(MEMTYPE_ICCM, `RV_ICCM_SADR, `RV_ICCM_EADR);
            $finish;
        end
        // console Monitor
        if( mailbox_data_val & mailbox_write) begin
            $fwrite(fd,"%c", WriteData[7:0]);
            // Prints get lost in sim.log amidst a flurry of UVM_INFO
            // messages....  best to just omit and send to console.log
            if (!UVM_TB) begin
                $write("%c", WriteData[7:0]);
            end
            if (WriteData[7:0] inside {8'h0A,8'h0D}) begin // CR/LF
                $fflush(fd);
            end
        end
        // Disable this for UVM simulations since control is delegated to
        // uvm tests/sequences
        // End Of test monitor
        if(mailbox_write && WriteData[7:0] == 8'hff) begin
            if (UVM_TB) $warning("WARNING! Detected FW write to manually end the test with SUCCESS, but Firmware can't do this in UVM.");
            else if (|cycleCntKillReq) begin
                $error("ERROR! FW attempted to end the simulation with SUCCESS after previously requesting to end the sim with FAILURE!");
            end
            else begin
                $display("* TESTCASE PASSED");
                $display("\nFinished : minstret = %0d, mcycle = %0d", `DEC.tlu.minstretl[31:0],`DEC.tlu.mcyclel[31:0]);
                $display("See \"exec.log\" for execution trace with register updates..\n");
                dump_memory_contents(MEMTYPE_LMEM, 32'h0000_0000, 32'h001_FFFF);
                dump_memory_contents(MEMTYPE_DCCM, `RV_DCCM_SADR, `RV_DCCM_EADR);
                dump_memory_contents(MEMTYPE_ICCM, `RV_ICCM_SADR, `RV_ICCM_EADR);
                $finish;
            end
        end
        else if(mailbox_write && WriteData[7:0] == 8'h1) begin
            if (UVM_TB) $info("INFO: Detected FW write to manually end the test with FAIL; ignoring since the UVM environment will handle this.");
            else begin
                cycleCntKillReq <= cycleCnt;
                $display("* TESTCASE FAILED");
                $display(" -- Extending simulation for 100 clock cycles to capture ending waveform");
            end
        end
        if (|cycleCntKillReq && (cycleCnt == (cycleCntKillReq + 100))) begin
                $display("Dumping memory contents at simulation end due to FAILURE");
                dump_memory_contents(MEMTYPE_LMEM, 32'h0000_0000, 32'h001_FFFF);
                dump_memory_contents(MEMTYPE_DCCM, `RV_DCCM_SADR, `RV_DCCM_EADR);
                dump_memory_contents(MEMTYPE_ICCM, `RV_ICCM_SADR, `RV_ICCM_EADR);
                $finish;
        end
    end


    // trace monitor
    always @(posedge clk) begin
        wb_valid  <= `DEC.dec_i0_wen_r;
        wb_dest   <= `DEC.dec_i0_waddr_r;
        wb_data   <= `DEC.dec_i0_wdata_r;
        if (caliptra_top_dut.trace_rv_i_valid_ip && !$test$plusargs("CLP_REGRESSION")) begin

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
            if (!$test$plusargs("CLP_REGRESSION")) $fwrite (el, "%10d : %32s=%h ; nbL\n", cycleCnt, abi_reg[`DEC.dec_nonblock_load_waddr], `DEC.lsu_nonblock_load_data);
            caliptra_top_tb_services.gpr[0][`DEC.dec_nonblock_load_waddr] = `DEC.lsu_nonblock_load_data;
        end
        if(`DEC.exu_div_wren) begin
            if (!$test$plusargs("CLP_REGRESSION")) $fwrite (el, "%10d : %32s=%h ; nbD\n", cycleCnt, abi_reg[`DEC.div_waddr_wb], `DEC.exu_div_result);
            caliptra_top_tb_services.gpr[0][`DEC.div_waddr_wb] = `DEC.exu_div_result;
        end
    end

    // IFU Initiator monitor
    always @(posedge clk) begin
        if (!$test$plusargs("CLP_REGRESSION"))
        $fstrobe(ifu_p, "%10d : 0x%0h %h %b %h %h %h %b 0x%08h_%08h %b %b\n", cycleCnt, 
                        caliptra_top_dut.ic_haddr, caliptra_top_dut.ic_hburst, caliptra_top_dut.ic_hmastlock, 
                        caliptra_top_dut.ic_hprot, caliptra_top_dut.ic_hsize, caliptra_top_dut.ic_htrans, 
                        caliptra_top_dut.ic_hwrite, caliptra_top_dut.ic_hrdata[63:32], caliptra_top_dut.ic_hrdata[31:0], 
                        caliptra_top_dut.ic_hready, caliptra_top_dut.ic_hresp);
    end

    // LSU Initiator monitor
    always @(posedge clk) begin
        if (!$test$plusargs("CLP_REGRESSION"))
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
            always @(posedge clk) begin
                if (!$test$plusargs("CLP_REGRESSION"))
                $fstrobe(sl_p[sl_i], "%10d : 0x%0h %h %h %b 0x%08h_%08h 0x%08h_%08h %b %b %b %b\n", cycleCnt, 
                        caliptra_top_dut.responder_inst[sl_i].haddr, caliptra_top_dut.responder_inst[sl_i].hsize, caliptra_top_dut.responder_inst[sl_i].htrans, 
                        caliptra_top_dut.responder_inst[sl_i].hwrite, caliptra_top_dut.responder_inst[sl_i].hrdata[63:32], caliptra_top_dut.responder_inst[sl_i].hrdata[31:0], 
                        caliptra_top_dut.responder_inst[sl_i].hwdata[63:32], caliptra_top_dut.responder_inst[sl_i].hwdata[31:0], 
                        caliptra_top_dut.responder_inst[sl_i].hready, caliptra_top_dut.responder_inst[sl_i].hreadyout, caliptra_top_dut.responder_inst[sl_i].hresp, caliptra_top_dut.responder_inst[sl_i].hsel);
            end
        end
    endgenerate


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

        `ifndef VERILATOR
        imem_inst1.ram           = '{default:8'h0};
        dummy_mbox_preloader.ram = '{default:8'h0};
        dummy_iccm_preloader.ram = '{default:8'h0};
        dummy_dccm_preloader.ram = '{default:8'h0};
        `endif
        hex_file_is_empty = $system("test -s program.hex");
        if (!hex_file_is_empty) $readmemh("program.hex",  imem_inst1.ram,0,32'h00007FFF);
        hex_file_is_empty = $system("test -s mailbox.hex");
        if (!hex_file_is_empty) $readmemh("mailbox.hex",  dummy_mbox_preloader.ram,0,32'h0001_FFFF);
        hex_file_is_empty = $system("test -s dccm.hex");
        if (!hex_file_is_empty) $readmemh("dccm.hex",     dummy_dccm_preloader.ram,0,32'h0001_FFFF);
        hex_file_is_empty = $system("test -s iccm.hex");
        if (!hex_file_is_empty) $readmemh("iccm.hex",     dummy_iccm_preloader.ram,0,32'h0001_FFFF);
        if (!$test$plusargs("CLP_REGRESSION")) begin
            tp = $fopen("trace_port.csv","w");
            el = $fopen("exec.log","w");
            ifu_p = $fopen("ifu_master_ahb_trace.log", "w");
            lsu_p = $fopen("lsu_master_ahb_trace.log", "w");
        end
        if (!$test$plusargs("CLP_REGRESSION")) begin
            $fwrite (el, "//   Cycle : #inst    0    pc    opcode    reg=value   ; mnemonic\n");
            $fwrite(ifu_p, "//   Cycle: ic_haddr     ic_hburst     ic_hmastlock     ic_hprot     ic_hsize     ic_htrans     ic_hwrite     ic_hrdata     ic_hwdata     ic_hready     ic_hresp\n");
            $fwrite(lsu_p, "//   Cycle: lsu_haddr     lsu_hsize     lsu_htrans     lsu_hwrite     lsu_hrdata     lsu_hwdata     lsu_hready     lsu_hresp\n");

            for (j = 0; j < `CALIPTRA_AHB_SLAVES_NUM; j = j + 1) begin
                slaveLog_fileName[j] = {$sformatf("slave%0d_ahb_trace.log", j)};
                sl_p[j] = $fopen(slaveLog_fileName[j], "w");
                $fwrite(sl_p[j], "//   Cycle: haddr     hsize     htrans     hwrite     hrdata     hwdata     hready     hreadyout     hresp\n");
            end
        end

        fd = $fopen("console.log","w");
        commit_count = 0;
        preload_dccm();
        preload_iccm();
        preload_mbox();

        assert_hard_rst_flag = 0;
        deassert_hard_rst_flag = 0;
        assert_rst_flag = 0;
        deassert_rst_flag = 0;

        cold_rst = 0;
        warm_rst = 0;
        timed_warm_rst = 0;
        cold_rst_done = 0;
    end

   //=========================================================================-
   // SRAM instances
   //=========================================================================-
caliptra_veer_sram_export veer_sram_export_inst (
    .el2_mem_export(el2_mem_export)
);

//SRAM for mbox (preload raw data here)
caliptra_sram 
#(
    .DATA_WIDTH(MBOX_DATA_W),
    .DEPTH     (MBOX_DEPTH )
)
dummy_mbox_preloader
(
    .clk_i(clk),

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
    .clk_i(clk),

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
    .clk_i   (clk   ),

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
    .clk_i   (clk),

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
    .clk_i   (clk),

    .cs_i    (        ),
    .we_i    (        ),
    .addr_i  (        ),
    .wdata_i (        ),
    .rdata_o (        )
);


   //=========================================================================-
   // SRAM preload services
   //=========================================================================-
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

    `ifndef VERILATOR
    init_iccm();
    `endif
    saddr = `RV_ICCM_SADR;
    if ( (saddr < `RV_ICCM_SADR) || (saddr > `RV_ICCM_EADR)) return;
    `ifndef RV_ICCM_ENABLE
        $display("********************************************************");
        $display("ICCM preload: there is no ICCM in VeeR, terminating !!!");
        $display("********************************************************");
        $finish;
    `endif
    eaddr = `RV_ICCM_EADR;
    $display("ICCM pre-load from %h to %h", saddr, eaddr);

    for(addr= saddr; addr <= eaddr; addr+=4) begin
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

    `ifndef VERILATOR
    init_dccm();
    `endif
    saddr = `RV_DCCM_SADR;
    if (saddr < `RV_DCCM_SADR || saddr > `RV_DCCM_EADR) return;
    `ifndef RV_DCCM_ENABLE
        $display("********************************************************");
        $display("DCCM preload: there is no DCCM in VeeR, terminating !!!");
        $display("********************************************************");
        $finish;
    `endif
    eaddr = `RV_DCCM_EADR;
    $display("DCCM pre-load from %h to %h", saddr, eaddr);

    for(addr=saddr; addr <= eaddr; addr+=4) begin
        // FIXME hardcoded address indices?
        data = {dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h3}],
                dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h2}],
                dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h1}],
                dummy_dccm_preloader.ram [addr[16:3]] [{addr[2],2'h0}]};
        slam_dccm_ram(addr, data == 0 ? 0 : {riscv_ecc32(data),data});
    end
    $display("DCCM pre-load completed");

endtask



`define ICCM_PATH veer_sram_export_inst.Gen_iccm_enable
`ifdef VERILATOR
`define DRAM(bk) veer_sram_export_inst.Gen_dccm_enable.dccm_loop[bk].ram.ram_core
`define IRAM(bk) `ICCM_PATH.iccm_loop[bk].iccm_bank.ram_core
`else
`define DRAM(bk) veer_sram_export_inst.Gen_dccm_enable.dccm_loop[bk].dccm.dccm_bank.ram_core
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
