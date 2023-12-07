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

`include "config_defines.svh"

module clk_gate (
    input logic clk,
    input logic cptra_rst_b,
    input logic psel,
    input logic clk_gate_en,
    input logic rdc_clk_dis,
    input logic rdc_clk_dis_uc,
    input logic cpu_halt_status,
    input logic [63:0] generic_input_wires,
    input logic cptra_error_fatal,
    input logic cptra_in_debug_scan_mode,
    output logic clk_cg,
    output logic soc_ifc_clk_cg,
    output logic rdc_clk_cg,
    output logic uc_clk_cg,
    input  logic cptra_dmi_reg_en_preQ //JTAG access
);

logic disable_clk;
logic disable_soc_ifc_clk;
logic disable_uc_clk;
logic [63:0] generic_input_wires_f;
logic change_in_generic_wires;
logic sleep_condition;


/**********************************************************************
cpu_halt_status     psel    generic_input_wires    Expected behavior
-----------------------------------------------------------------------
        0            X              X               clk_cg = active
                                                    soc_ifc_clk_cg = active

        1            0              0               clk_cg = inactive
                                                    soc_ifc_clk_cg = inactive

        1            0              1               clk_cg = active (as long as generic_input_wires != 0)
                                                    soc_ifc_clk_cg = active (as long as generic input wires != 0)

        1            1              0               clk_cg = inactive
                                                    soc_ifc_clk_cg = active (as long as psel = 1)

        1            1              1               clk_cg = active (as long as wires != 0)
                                                    soc_ifc_clk_cg = active (as long as wires != 0 || psel = 1)

**********************************************************************/

//Flop generic input wires to detect change
always_ff@(posedge clk or negedge cptra_rst_b) begin
    if(!cptra_rst_b) begin
        generic_input_wires_f <= 'h0;
    end
    else begin 
        generic_input_wires_f <= generic_input_wires;
    end
end

//Generate clk disable signal
always_comb begin
    change_in_generic_wires = ((generic_input_wires ^ generic_input_wires_f) != 'h0);
    sleep_condition         = (cpu_halt_status && !change_in_generic_wires && !cptra_error_fatal && !cptra_in_debug_scan_mode && !cptra_dmi_reg_en_preQ);
    disable_clk             = (clk_gate_en && sleep_condition) | rdc_clk_dis;
    disable_soc_ifc_clk     = (clk_gate_en && (sleep_condition && !psel)) | rdc_clk_dis;
    disable_uc_clk          = (rdc_clk_dis | rdc_clk_dis_uc);
end


`ifdef TECH_SPECIFIC_ICG
    `USER_ICG user_icg (.clk(clk), .en(!disable_clk), .clk_cg(clk_cg));
    `USER_ICG user_soc_ifc_icg (.clk(clk), .en(!disable_soc_ifc_clk), .clk_cg(soc_ifc_clk_cg));
    `USER_ICG user_rdc_icg (.clk(clk), .en(!rdc_clk_dis), .clk_cg(rdc_clk_cg));
    `USER_ICG user_rdc_uc_icg (.clk(clk), .en(!disable_uc_clk), .clk_cg(uc_clk_cg));
`else
    `CALIPTRA_ICG caliptra_icg (.clk(clk), .en(!disable_clk), .clk_cg(clk_cg));
    `CALIPTRA_ICG caliptra_soc_ifc_icg (.clk(clk), .en(!disable_soc_ifc_clk), .clk_cg(soc_ifc_clk_cg));
    `CALIPTRA_ICG caliptra_rdc_icg (.clk(clk), .en(!rdc_clk_dis), .clk_cg(rdc_clk_cg));
    `CALIPTRA_ICG caliptra_rdc_uc_icg (.clk(clk), .en(!disable_uc_clk), .clk_cg(uc_clk_cg));
`endif

endmodule
