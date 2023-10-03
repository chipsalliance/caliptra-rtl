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

`ifndef VERILATOR

interface pcrvault_cov_if     
    import pv_defines_pkg::*;
    (
    input logic clk,
    input logic rst_b,
    input logic cptra_pwrgood
);

    logic [PV_NUM_PCR-1:0] pcr_ctrl_lock;
    logic [PV_NUM_PCR-1:0] pcr_ctrl_clear;

    logic [PV_NUM_WRITE-1:0] pv_write_en;
    logic ahb_write, ahb_read;
    
    //Assign clear and locks of each PCR_CTRL reg to corresponding bit in the intermediate bus
    generate
        for(genvar i = 0; i < PV_NUM_PCR; i++) begin
            assign pcr_ctrl_lock[i] = pv.pv_reg_hwif_out.PCR_CTRL[i].lock;
        end
    endgenerate

    generate
        for(genvar client = 0; client < PV_NUM_WRITE; client++) begin
            assign pv_write_en[client] = pv.pv_write[client].write_en;
        end
    endgenerate

    //AHB signals
    assign ahb_write = pv.pv_ahb_slv1.dv & pv.pv_ahb_slv1.write;
    assign ahb_read  = pv.pv_ahb_slv1.dv & ~pv.pv_ahb_slv1.write;

    covergroup pcrvault_top_cov_grp @(posedge clk);
        option.per_instance = 1;

        //Note: Bit transitions and values for lock and clear are covered
        //in UVM reg coverage. This coverpoint bins the 32-bit lock/clear bus so that
        //they can be used to cross with other signals
        lock: coverpoint pcr_ctrl_lock {
            bins bin0 = {[0:'hFFFF]};
            bins bin1 = {['h1_0000:'hF_FFFF]};
            bins bin2 = {['h10_0000:'hFF_FFFF]};
            bins bin3 = {['h100_0000:'hFFF_FFFF]};
            bins bin4 = {['h1000_0000: 'hFFFF_FFFF]};
        }
        clear: coverpoint pcr_ctrl_clear {
            bins bin0 = {[0:'hFFFF]};
            bins bin1 = {['h1_0000:'hF_FFFF]};
            bins bin2 = {['h10_0000:'hFF_FFFF]};
            bins bin3 = {['h100_0000:'hFFF_FFFF]};
            bins bin4 = {['h1000_0000: 'hFFFF_FFFF]};
        }

        //Cover warm reset assertion while regs are locked/cleared
        lockXwarm_rst:      cross lock, rst_b;
        clearXwarm_rst:     cross clear, rst_b;

        //Cover cold reset assertion while regs are locked/cleared
        lockXcold_rst:      cross lock, cptra_pwrgood;
        clearXcold_rst:     cross clear, cptra_pwrgood;

        // lockXcore_rst:      cross lock, core_only_rst_b;
        // clearXcore_rst:     cross clear, core_only_rst_b;

        //Cover crypto writes to locked/cleared regs
        lockXpv_write:      cross lock, pv_write_en;
        clearXpv_write:     cross clear, pv_write_en;

        //Cover ahb write and read when crypto writes are happening
        ahbXpv_write:       cross ahb_write, ahb_read, pv_write_en;
        

    endgroup


    pcrvault_top_cov_grp pcrvault_top_cov_grp1 = new();
    
endinterface

`endif