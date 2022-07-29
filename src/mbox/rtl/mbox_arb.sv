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

`include "mbox_defines.svh"

module mbox_arb (
    input  logic clk,
    input  logic rst_b,

    //UC inf
    input  logic uc_req_dv,
    output logic uc_req_hold,
    input mbox_req_t uc_req_data,
    output logic [MBOX_DATA_W-1:0] uc_rdata,
    output logic uc_error,
    //SOC inf
    input  logic soc_req_dv,
    output logic soc_req_hold,
    input mbox_req_t soc_req_data,
    output logic [MBOX_DATA_W-1:0] soc_rdata,
    output logic soc_error,
    //MBOX inf
    output logic mbox_req_dv,
    input  logic mbox_req_hold,
    output mbox_req_t mbox_req_data,
    input  logic [MBOX_DATA_W-1:0] mbox_rdata,
    input  logic mbox_error,
    //mbox reg inf
    output logic mbox_reg_req_dv,
    input  logic mbox_reg_req_hold,
    output mbox_req_t mbox_reg_req_data,
    input  logic [MBOX_DATA_W-1:0] mbox_reg_rdata,
    input  logic mbox_reg_error
    
);
logic uc_has_priority;
logic soc_has_priority;
logic toggle_priority;
logic req_collision;

//dv for each req/target
logic soc_mbox_req;
logic soc_mbox_reg_req;
logic uc_mbox_req;
logic uc_mbox_reg_req;

//simple arbitration scheme, track most recently granted client (SOC or UC)
//give priority in case of collision to the least recently granted client
`CLP_EN_RST_FF(soc_has_priority, ~soc_has_priority, clk, toggle_priority, rst_b)
assign uc_has_priority = ~soc_has_priority;

//toggle the priority when collision is detected
always_comb toggle_priority = req_collision;

//figure out which client is requesting which block
always_comb uc_mbox_req = (uc_req_dv & (uc_req_data.addr inside {[MBOX_MEM_START_ADDR:MBOX_MEM_END_ADDR]}));
always_comb soc_mbox_req = (soc_req_dv & (soc_req_data.addr inside {[MBOX_MEM_START_ADDR:MBOX_MEM_END_ADDR]}));

always_comb uc_mbox_reg_req = (uc_req_dv & (uc_req_data.addr inside {[MBOX_REG_MEM_START_ADDR:MBOX_REG_MEM_END_ADDR]}));
always_comb soc_mbox_reg_req = (soc_req_dv & (soc_req_data.addr inside {[MBOX_REG_MEM_START_ADDR:MBOX_REG_MEM_END_ADDR]}));

//check for collisions
always_comb req_collision = (uc_mbox_req & soc_mbox_req) |
                            (uc_mbox_reg_req & soc_mbox_reg_req);

//drive the dv to the appropriate destination if either client is trying to 
always_comb mbox_req_dv = uc_mbox_req | soc_mbox_req;
always_comb mbox_reg_req_dv = uc_mbox_reg_req | soc_mbox_reg_req;

//drive the appropriate request to each destination
always_comb mbox_req_data = (soc_mbox_req & (~req_collision | soc_has_priority)) ? soc_req_data : uc_req_data;
always_comb mbox_reg_req_data = (soc_mbox_reg_req & (~req_collision | soc_has_priority)) ? soc_req_data : uc_req_data;

//drive the appropriate read data back to uc or soc
//AND/OR mux here, assert that requests are always mutex
always_comb uc_rdata = {MBOX_DATA_W{uc_mbox_req}} & mbox_rdata | 
                       {MBOX_DATA_W{uc_mbox_reg_req}} & mbox_reg_rdata;

always_comb soc_rdata = {MBOX_DATA_W{soc_mbox_req}} & mbox_rdata | 
                        {MBOX_DATA_W{soc_mbox_reg_req}} & mbox_reg_rdata;

//drive the appropraite holds back to uc or soc
//AND/OR mux here, assert that requests are always mutex
always_comb uc_req_hold = (req_collision & soc_has_priority) |
                          (uc_mbox_req & mbox_req_hold) |
                          (uc_mbox_reg_req & mbox_reg_req_hold);

always_comb soc_req_hold = (req_collision & uc_has_priority) |
                           (soc_mbox_req & mbox_req_hold) |
                           (soc_mbox_reg_req & mbox_reg_req_hold);

always_comb uc_error = (uc_mbox_req & mbox_error) |
                       (uc_mbox_reg_req & mbox_reg_error) |
                       (uc_req_dv & ~(uc_mbox_req | uc_mbox_reg_req));

always_comb soc_error = (soc_mbox_req & mbox_error) |
                        (soc_mbox_reg_req & mbox_reg_error) |
                        (soc_req_dv & ~(soc_mbox_req | soc_mbox_reg_req));

endmodule