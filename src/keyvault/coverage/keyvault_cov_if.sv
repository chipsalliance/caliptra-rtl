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

// This file contains cross coverage for keyvault at the dut level
// This interface is instantiated in uvmf_kv for coverage during randomized UVM tests

`ifndef VERILATOR

interface keyvault_cov_if     
    import kv_defines_pkg::*;
    (
    //Keyvault IO
    input logic clk,
    input logic rst_b,
    input logic core_only_rst_b,
    input logic cptra_pwrgood,
    input logic debugUnlock_or_scan_mode_switch,
    input logic cptra_in_debug_scan_mode
);

    //Intermediate wires
    logic [KV_NUM_KEYS-1:0] key_ctrl_lock_wr;
    logic [KV_NUM_KEYS-1:0] key_ctrl_lock_use;
    logic [KV_NUM_KEYS-1:0] key_ctrl_clear;

    logic clear_secrets_wr;
    logic clear_secrets_sel;
    logic [KV_NUM_WRITE-1:0] kv_write_en;
    logic ahb_write, ahb_read;
    
    //Assign clear and locks of each KEY_CTRL reg to corresponding bit in the intermediate bus
    generate
        for(genvar i = 0; i < KV_NUM_KEYS; i++) begin
            assign key_ctrl_lock_wr[i] = kv.kv_reg_hwif_out.KEY_CTRL[i].lock_wr;
            assign key_ctrl_lock_use[i] = kv.kv_reg_hwif_out.KEY_CTRL[i].lock_use;
            assign key_ctrl_clear[i] = kv.kv_reg_hwif_out.KEY_CTRL[i].clear;
        end
    endgenerate

    //CLEAR_SECRETS
    assign clear_secrets_wr = kv.kv_reg_hwif_out.CLEAR_SECRETS.wr_debug_values;
    assign clear_secrets_sel = kv.kv_reg_hwif_out.CLEAR_SECRETS.sel_debug_value;

    //Crypto interface write_en
    generate
        for(genvar client = 0; client < KV_NUM_WRITE; client++) begin
            assign kv_write_en[client] = kv.kv_write[client].write_en;
        end
    endgenerate

    //AHB signals
    assign ahb_write = kv.kv_ahb_slv1.dv & kv.kv_ahb_slv1.write;
    assign ahb_read  = kv.kv_ahb_slv1.dv & ~kv.kv_ahb_slv1.write;

    covergroup keyvault_top_cov_grp @(posedge clk);
        option.per_instance = 1;
        debug: coverpoint cptra_in_debug_scan_mode; //debugUnlock_or_scan_mode_switch;

        //Note: Bit transitions and values for lock_wr, lock_use and clear are covered
        //in UVM reg coverage. This coverpoint bins the 32-bit lock/clear bus so that
        //they can be used to cross with other signals
        lock_wr: coverpoint key_ctrl_lock_wr {
            bins bin0 = {[0:'hFF]};
            bins bin1 = {['h100:'hFFF]};
            bins bin2 = {['h1000:'hFFFF]};
            bins bin3 = {['h1_0000:'hF_FFFF]};
            bins bin4 = {['h10_0000: 'hFF_FFFF]};
        }
        lock_use: coverpoint key_ctrl_lock_use {
            bins bin0 = {[0:'hFF]};
            bins bin1 = {['h100:'hFFF]};
            bins bin2 = {['h1000:'hFFFF]};
            bins bin3 = {['h1_0000:'hF_FFFF]};
            bins bin4 = {['h10_0000: 'hFF_FFFF]};
        }
        clear: coverpoint key_ctrl_clear {
            bins bin0 = {[0:'hFF]};
            bins bin1 = {['h100:'hFFF]};
            bins bin2 = {['h1000:'hFFFF]};
            bins bin3 = {['h1_0000:'hF_FFFF]};
            bins bin4 = {['h10_0000: 'hFF_FFFF]};
        }
        kv_write_en_cp: coverpoint kv_write_en {
            bins bin0 = {0};
            bins bin1 = {1};
            bins bin2 = {2};
            bins bin4 = {4};
            bins bin8 = {8};
        }
        cp_clear_secrets_sel: coverpoint clear_secrets_sel;
        cp_clear_secrets_wr : coverpoint clear_secrets_wr;
        cp_ahb_write        : coverpoint ahb_write;
        cp_ahb_read         : coverpoint ahb_read;

        //Cover debug mode unlocked while regs are locked/cleared
        debugXlock_wr:                  cross debug, lock_wr;
        debugXlock_use:                 cross debug, lock_use;
        debugXclear:                    cross debug, clear;
        debugXlock_wrXlock_useXclear:   cross debug, lock_wr, lock_use, clear;
        debugXclear_secrets:            cross debug, cp_clear_secrets_wr, cp_clear_secrets_sel;
        debugXkv_write:                 cross debug, kv_write_en_cp;

        //Cover warm reset assertion while regs are locked/cleared
        // lock_wrXwarm_rst:   cross lock_wr, rst_b;
        // lock_useXwarm_rst:  cross lock_use, rst_b;
        // clearXwarm_rst:     cross clear, rst_b;

        //Cover cold reset while regs are locked/cleared
        // lock_wrXcold_rst:   cross lock_wr, cptra_pwrgood;
        // lock_useXcold_rst:  cross lock_use, cptra_pwrgood;
        // clearXcold_rst:     cross clear, cptra_pwrgood;

        //Cover core reset while regs are locked/cleared
        // lock_wrXcore_rst:   cross lock_wr, core_only_rst_b;
        // lock_useXcore_rst:  cross lock_use, core_only_rst_b;
        // clearXcore_rst:     cross clear, core_only_rst_b;

        //Cover simultaneous locks/clear settings
        lock_wrXlock_useXclearXclear_secrets: cross lock_wr, lock_use, clear, cp_clear_secrets_wr, cp_clear_secrets_sel;
        
        //Cross with crypto write. There's no cross with read since reads are async
        //Due to this, at any given time, all signals are by default crossed with read IF
        lock_wrXkv_write:   cross lock_wr, kv_write_en_cp;
        lock_useXkv_write:  cross lock_use, kv_write_en_cp;
        clearXkv_write:     cross clear, kv_write_en_cp;

        clear_secretsXkv_write: cross kv_write_en_cp, cp_clear_secrets_wr, cp_clear_secrets_sel;

        //Cover ahb write/read during crypto write and debug mode unlocked
        ahb_writeXkv_write:      cross cp_ahb_write, kv_write_en_cp;
        ahb_writeXdebug:         cross cp_ahb_write, debug;
        ahb_readXkv_write:       cross cp_ahb_read, kv_write_en_cp;
        ahb_readXdebug:          cross cp_ahb_read, debug;
        

    endgroup


    keyvault_top_cov_grp keyvault_top_cov_grp1 = new();
    
endinterface

`endif