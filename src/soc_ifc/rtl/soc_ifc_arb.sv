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

module soc_ifc_arb 
    import soc_ifc_pkg::*;
    #(
        parameter AXI_USER_WIDTH = 32
    )(
    input  logic clk,
    input  logic rst_b,

    input logic [4:0][AXI_USER_WIDTH-1:0] valid_mbox_users,
    input logic valid_fuse_user,
    input logic valid_sha_user,
    //UC inf
    input  logic uc_req_dv,
    output logic uc_req_hold,
    input soc_ifc_req_t uc_req_data,
    output logic [SOC_IFC_DATA_W-1:0] uc_rdata,
    output logic uc_error,
    //SOC inf
    input  logic soc_req_dv,
    output logic soc_req_hold,
    input soc_ifc_req_t soc_req_data,
    output logic [SOC_IFC_DATA_W-1:0] soc_rdata,
    output logic soc_error,
    //MBOX inf
    output logic mbox_req_dv,
    output logic mbox_dir_req_dv,
    input  logic mbox_req_hold,
    output soc_ifc_req_t mbox_req_data,
    input  logic [SOC_IFC_DATA_W-1:0] mbox_rdata,
    input  logic [SOC_IFC_DATA_W-1:0] mbox_dir_rdata,
    input  logic mbox_error,
    //SHA inf
    output logic sha_req_dv,
    input  logic sha_req_hold,
    output soc_ifc_req_t sha_req_data,
    input  logic [SOC_IFC_DATA_W-1:0] sha_rdata,
    input  logic sha_error,
    // AXI DMA INF
    output logic                      dma_reg_req_dv,
    output soc_ifc_req_t              dma_reg_req_data,
    input  logic                      dma_reg_req_hold,
    input  logic [SOC_IFC_DATA_W-1:0] dma_reg_rdata,
    input  logic                      dma_reg_error,

    //SOC IFC REG inf
    output logic soc_ifc_reg_req_dv,
    input  logic soc_ifc_reg_req_hold,
    output soc_ifc_req_t soc_ifc_reg_req_data,
    input  logic [SOC_IFC_DATA_W-1:0] soc_ifc_reg_rdata,
    input  logic soc_ifc_reg_error
    
);
//track priority
logic soc_priority;
logic uc_has_priority;
logic soc_has_priority;
logic toggle_priority;
logic req_collision;

//dv for each req/target
logic soc_mbox_req;
logic soc_reg_req;
logic soc_sha_req;
logic soc_dma_req;

logic uc_mbox_req;
logic uc_mbox_reg_req;
logic uc_mbox_dir_req;
logic uc_reg_req;
logic uc_sha_req;
logic uc_dma_req;

//grant for each request
logic soc_mbox_gnt;
logic soc_reg_gnt;
logic soc_sha_gnt;
logic soc_dma_gnt;

logic uc_mbox_gnt;
logic uc_reg_gnt;
logic uc_sha_gnt;
logic uc_dma_gnt;

//track in-progress grants
logic soc_req_ip;

logic uc_req_ip;

//filter mailbox requests by user
logic valid_mbox_req;


//simple arbitration scheme, track most recently granted client (SOC or UC)
//give priority in case of collision to the least recently granted client
always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        soc_priority <= '0;

        soc_req_ip <= '0;

        uc_req_ip <= '0;
    end
    else begin
        soc_priority <= toggle_priority ? ~soc_priority : soc_priority;

        soc_req_ip <= (soc_mbox_gnt & mbox_req_hold) | (soc_reg_gnt & soc_ifc_reg_req_hold) | (soc_sha_gnt & sha_req_hold) | (soc_dma_gnt & dma_reg_req_hold);

        uc_req_ip <= (uc_mbox_gnt & mbox_req_hold) | (uc_reg_gnt & soc_ifc_reg_req_hold) | (uc_sha_gnt & sha_req_hold) | (uc_dma_gnt & dma_reg_req_hold);
    end
end
//Assign priority - first to the client who's already in progress and held
//                  second to the client with priority pointing to them, unless there is a req ip
//                  This condition only matters for collisions. Simultaneous transactions to different
//                  destinations can result in both signals being asserted together.
always_comb uc_has_priority  = uc_req_ip  | (~soc_priority & ~soc_req_ip);
always_comb soc_has_priority = soc_req_ip | ( soc_priority & ~uc_req_ip);

//toggle the priority when collision is detected
always_comb toggle_priority = req_collision;

//figure out which client is requesting which block
//uC requests to mailbox
always_comb uc_mbox_req = uc_mbox_reg_req | uc_mbox_dir_req;
always_comb uc_mbox_reg_req = (uc_req_dv & (uc_req_data.addr inside {[MBOX_REG_START_ADDR:MBOX_REG_END_ADDR]}));
/* verilator lint_off UNSIGNED */
always_comb uc_mbox_dir_req = (uc_req_dv & (uc_req_data.addr inside {[MBOX_DIR_START_ADDR:MBOX_DIR_END_ADDR]}));
/* verilator lint_on UNSIGNED */
//SoC requests to mailbox
always_comb soc_mbox_req = (valid_mbox_req & (soc_req_data.addr inside {[MBOX_REG_START_ADDR:MBOX_REG_END_ADDR]}));
//Requests to arch/fuse register block
//Ensure that requests to fuse block match the appropriate user value
always_comb uc_reg_req = (uc_req_dv & (uc_req_data.addr inside {[SOC_IFC_REG_START_ADDR:SOC_IFC_REG_END_ADDR]}));
always_comb soc_reg_req = (soc_req_dv & (soc_req_data.addr inside {[SOC_IFC_REG_START_ADDR:SOC_IFC_REG_END_ADDR]}) &
                                        (~(soc_req_data.addr inside {[SOC_IFC_FUSE_START_ADDR:SOC_IFC_FUSE_END_ADDR]}) | valid_fuse_user));

//Requests to SHA
always_comb uc_sha_req = (uc_req_dv & (uc_req_data.addr inside {[SHA_REG_START_ADDR:SHA_REG_END_ADDR]}));
always_comb soc_sha_req = (soc_req_dv & (soc_req_data.addr inside {[SHA_REG_START_ADDR:SHA_REG_END_ADDR]})) & valid_sha_user;

// Requests to DMA
always_comb uc_dma_req = (uc_req_dv & (uc_req_data.addr inside {[DMA_REG_START_ADDR:DMA_REG_END_ADDR]}));
always_comb soc_dma_req = (soc_req_dv & (soc_req_data.addr inside {[DMA_REG_START_ADDR:DMA_REG_END_ADDR]}));

//Check if SoC request is coming from a valid user
//There are 5 valid user registers, check if user attribute matches any of them
//Check if user matches Default Valid user parameter - this user value is always valid
always_comb begin
    valid_mbox_req = '0;
    for (int i=0; i < 5; i++) begin
        valid_mbox_req |= soc_req_dv & (soc_req_data.user == valid_mbox_users[i]);
    end
    valid_mbox_req |= soc_req_dv & (soc_req_data.user == CPTRA_DEF_MBOX_VALID_AXI_USER[SOC_IFC_USER_W-1:0]);
end

//check for collisions
//don't toggle priority if the request was held
always_comb req_collision = (uc_mbox_req & soc_mbox_req & ~mbox_req_hold) |
                            (uc_reg_req & soc_reg_req & ~soc_ifc_reg_req_hold) |
                            (uc_sha_req & soc_sha_req & ~sha_req_hold) |
                            (uc_dma_req & soc_dma_req & ~dma_reg_req_hold);

//drive the dv to the appropriate destination if either client is trying to 
always_comb mbox_req_dv = uc_mbox_reg_req | soc_mbox_gnt;
always_comb mbox_dir_req_dv = uc_mbox_dir_req & uc_mbox_gnt;
always_comb soc_ifc_reg_req_dv = uc_reg_req | soc_reg_req;
always_comb sha_req_dv = uc_sha_req | soc_sha_req;
always_comb dma_reg_req_dv = uc_dma_req | soc_dma_req;

//determine which requests get granted
//if a request is colliding with another, grant the one with priority
//ignore priority if one of the requests was already in progress
//this prevents the "priority" request from interrupting an in progress request
always_comb soc_mbox_gnt = soc_mbox_req & (~uc_mbox_req | soc_has_priority);
always_comb soc_reg_gnt  = soc_reg_req  & (~uc_reg_req  | soc_has_priority);
always_comb soc_sha_gnt  = soc_sha_req  & (~uc_sha_req  | soc_has_priority);
always_comb soc_dma_gnt  = soc_dma_req  & (~uc_dma_req  | soc_has_priority);

always_comb uc_mbox_gnt = uc_mbox_req & (~soc_mbox_req | uc_has_priority);
always_comb uc_reg_gnt  = uc_reg_req  & (~soc_reg_req  | uc_has_priority);
always_comb uc_sha_gnt  = uc_sha_req  & (~soc_sha_req  | uc_has_priority);
always_comb uc_dma_gnt  = uc_dma_req  & (~soc_dma_req  | uc_has_priority);

//drive the appropriate request to each destination
always_comb mbox_req_data = ({$bits(soc_ifc_req_t){soc_mbox_gnt}} & soc_req_data) |
                            ({$bits(soc_ifc_req_t){uc_mbox_gnt}} & uc_req_data);

always_comb soc_ifc_reg_req_data = ({$bits(soc_ifc_req_t){soc_reg_gnt}} & soc_req_data) | 
                                   ({$bits(soc_ifc_req_t){uc_reg_gnt}} & uc_req_data);

always_comb sha_req_data = ({$bits(soc_ifc_req_t){soc_sha_gnt}} & soc_req_data) | 
                           ({$bits(soc_ifc_req_t){uc_sha_gnt}} & uc_req_data);

always_comb dma_reg_req_data = ({$bits(soc_ifc_req_t){soc_dma_gnt}} & soc_req_data) | 
                               ({$bits(soc_ifc_req_t){uc_dma_gnt}} & uc_req_data);

//drive the appropriate read data back to uc or soc
//AND/OR mux here, assert that requests are always mutex
always_comb uc_rdata = ({SOC_IFC_DATA_W{uc_mbox_reg_req}} & mbox_rdata) |
                       ({SOC_IFC_DATA_W{uc_mbox_dir_req}} & mbox_dir_rdata) |
                       ({SOC_IFC_DATA_W{uc_reg_req}} & soc_ifc_reg_rdata) | 
                       ({SOC_IFC_DATA_W{uc_sha_req}} & sha_rdata) | 
                       ({SOC_IFC_DATA_W{uc_dma_req}} & dma_reg_rdata);

always_comb soc_rdata = ({SOC_IFC_DATA_W{soc_mbox_req}} & mbox_rdata) | 
                        ({SOC_IFC_DATA_W{soc_reg_req}} & soc_ifc_reg_rdata) | 
                        ({SOC_IFC_DATA_W{soc_sha_req}} & sha_rdata) | 
                        ({SOC_IFC_DATA_W{soc_dma_req}} & dma_reg_rdata);

//drive the appropraite holds back to uc or soc
//AND/OR mux here, assert that requests are always mutex
always_comb uc_req_hold = (uc_mbox_req & (~uc_mbox_gnt | mbox_req_hold)) |
                          (uc_reg_req & (~uc_reg_gnt | soc_ifc_reg_req_hold)) |
                          (uc_sha_req & (~ uc_sha_gnt | sha_req_hold)) |
                          (uc_dma_req & (~ uc_dma_gnt | dma_reg_req_hold));

always_comb soc_req_hold = (soc_mbox_req & (~soc_mbox_gnt | mbox_req_hold)) |
                           (soc_reg_req & (~soc_reg_gnt | soc_ifc_reg_req_hold)) |
                           (soc_sha_req & (~soc_sha_gnt | sha_req_hold)) |
                           (soc_dma_req & (~soc_dma_gnt | dma_reg_req_hold));

//Assert error when requested client drives error back, or a request is made that doesn't map to any of the clients
always_comb uc_error = (uc_mbox_gnt & mbox_error) |
                       (uc_reg_gnt & soc_ifc_reg_error) |
                       (uc_sha_gnt & sha_error) |
                       (uc_dma_gnt & dma_reg_error) |
                       (uc_req_dv & ~(uc_mbox_req | uc_reg_req | uc_sha_req | uc_dma_req));

always_comb soc_error = (soc_mbox_gnt & mbox_error) |
                        (soc_reg_gnt & soc_ifc_reg_error) |
                        (soc_sha_gnt & sha_error) |
                        (soc_dma_gnt & dma_reg_error) |
                        (soc_req_dv & ~(soc_mbox_req | soc_reg_req | soc_sha_req | soc_dma_req));

`CALIPTRA_ASSERT      (ERR_ARB_MBOX_ADDR     , mbox_req_dv     -> mbox_req_data.addr inside {[MBOX_REG_START_ADDR:MBOX_REG_END_ADDR]}, clk, !rst_b)
`CALIPTRA_ASSERT      (ERR_ARB_MBOX_DIR_ADDR , mbox_dir_req_dv -> mbox_req_data.addr inside {[MBOX_DIR_START_ADDR:MBOX_DIR_END_ADDR]}, clk, !rst_b)

`CALIPTRA_ASSERT_MUTEX(ERR_ARB_MBOX_ACCESS_MUTEX, {uc_mbox_gnt,soc_mbox_gnt}, clk, !rst_b)
`CALIPTRA_ASSERT_MUTEX(ERR_ARB_REG_ACCESS_MUTEX , {uc_reg_gnt,soc_reg_gnt}, clk, !rst_b)
`CALIPTRA_ASSERT_MUTEX(ERR_ARB_SHA_ACCESS_MUTEX , {uc_sha_gnt,soc_sha_gnt}, clk, !rst_b)
`CALIPTRA_ASSERT_MUTEX(ERR_ARB_DMA_ACCESS_MUTEX , {uc_dma_gnt,soc_dma_gnt}, clk, !rst_b)
`CALIPTRA_ASSERT_MUTEX(ERR_ARB_MBOX_REG_AND_DIR_ACCESS_MUTEX, {mbox_req_dv,mbox_dir_req_dv}, clk, !rst_b)

endmodule
