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

// -------------------------------------------------------------
// AHB Lite 2:1 Mux
// -------------------------------------------------------------

`include "caliptra_sva.svh"

module ahb_lite_2to1_mux #(
    parameter AHB_LITE_ADDR_WIDTH   = 32,
    parameter AHB_LITE_DATA_WIDTH   = 32
) (
    // ---------------------------------------
    // Global clock/reset
    // ---------------------------------------
    input logic     hclk,
    input logic     hreset_n,

    // ---------------------------------------
    // From Initiator 0
    // ---------------------------------------
    input logic                                 hsel_i_0,
    input logic     [AHB_LITE_ADDR_WIDTH-1:0]   haddr_i_0,
    input logic     [AHB_LITE_DATA_WIDTH-1:0]   hwdata_i_0,
    input logic                                 hwrite_i_0,
    input logic     [1:0]                       htrans_i_0, 
    input logic     [2:0]                       hsize_i_0,
    input logic                                 hready_i_0,

    output logic                                hresp_o_0,
    output logic                                hready_o_0,
    output logic    [AHB_LITE_DATA_WIDTH-1:0]   hrdata_o_0,

    // ---------------------------------------
    // From Initiator 1
    // ---------------------------------------
    input logic                                 hsel_i_1,
    input logic     [AHB_LITE_ADDR_WIDTH-1:0]   haddr_i_1,
    input logic     [AHB_LITE_DATA_WIDTH-1:0]   hwdata_i_1,
    input logic                                 hwrite_i_1,
    input logic     [1:0]                       htrans_i_1, 
    input logic     [2:0]                       hsize_i_1,
    input logic                                 hready_i_1,

    output logic                                hresp_o_1,
    output logic                                hready_o_1,
    output logic    [AHB_LITE_DATA_WIDTH-1:0]   hrdata_o_1,

    // ---------------------------------------
    // To Responder Interface Port
    // ---------------------------------------
    input logic                                 hresp_i,
    input logic     [AHB_LITE_DATA_WIDTH-1:0]   hrdata_i, 
    input logic                                 hreadyout_i,

    output logic    [AHB_LITE_ADDR_WIDTH-1:0]   haddr_o, 
    output logic    [AHB_LITE_DATA_WIDTH-1:0]   hwdata_o, 
    output logic                                hsel_o, 
    output logic                                hwrite_o, 
    output logic                                hready_o,
    output logic    [1:0]                       htrans_o,
    output logic    [2:0]                       hsize_o

);

//This is a fixed priority 2:1 mux for AHB-Lite protocol
//Initiator 0 always takes priority

logic initiator0_address_ph, initiator1_address_ph;
logic initiator0_data_ph, initiator1_data_ph;
logic initiator0_pend_addr_ph, initiator1_pend_addr_ph;
logic initiator0_gnt, initiator1_gnt;
logic [AHB_LITE_ADDR_WIDTH-1:0] initiator0_pend_haddr, initiator1_pend_haddr;
logic [AHB_LITE_ADDR_WIDTH-1:0] initiator0_haddr, initiator1_haddr;
logic [1:0] initiator0_pend_htrans, initiator1_pend_htrans;
logic [1:0] initiator0_htrans, initiator1_htrans;
logic [2:0] initiator0_pend_hsize, initiator1_pend_hsize;
logic [2:0] initiator0_hsize, initiator1_hsize;
logic initiator0_pend_hwrite, initiator1_pend_hwrite;
logic initiator0_hwrite, initiator1_hwrite;

//Detect address phase
always_comb initiator0_address_ph = hsel_i_0 & hready_i_0 & htrans_i_0 inside {2'b10, 2'b11};
always_comb initiator1_address_ph = hsel_i_1 & hready_i_1 & htrans_i_1 inside {2'b10, 2'b11};

always_ff @(posedge hclk or negedge hreset_n) begin
    if (~hreset_n) begin
        initiator0_pend_haddr <= '0;
        initiator1_pend_haddr <= '0;
        initiator0_pend_htrans <= '0;
        initiator1_pend_htrans <= '0;
        initiator0_pend_hsize <= '0;
        initiator1_pend_hsize <= '0;
        initiator0_pend_hwrite <= '0;
        initiator1_pend_hwrite <= '0;
        initiator0_pend_addr_ph <= '0;
        initiator1_pend_addr_ph <= '0;
        initiator0_data_ph <= '0;
        initiator1_data_ph <= '0;
    end
    else begin
        //Capture the address during the address phase for each initiator
        initiator0_pend_haddr <= initiator0_address_ph ? haddr_i_0 : initiator0_pend_haddr;
        initiator1_pend_haddr <= initiator1_address_ph ? haddr_i_1 : initiator1_pend_haddr;
        initiator0_pend_htrans <= initiator0_address_ph ? htrans_i_0 : initiator0_pend_htrans;
        initiator1_pend_htrans <= initiator1_address_ph ? htrans_i_1 : initiator1_pend_htrans;
        initiator0_pend_hsize <= initiator0_address_ph ? hsize_i_0 : initiator0_pend_hsize;
        initiator1_pend_hsize <= initiator1_address_ph ? hsize_i_1 : initiator1_pend_hsize;
        initiator0_pend_hwrite <= initiator0_address_ph ? hwrite_i_0 : initiator0_pend_hwrite;
        initiator1_pend_hwrite <= initiator1_address_ph ? hwrite_i_1 : initiator1_pend_hwrite;

        //Capture pending address phase when initiators collide
        initiator0_pend_addr_ph <= (initiator0_address_ph | initiator0_pend_addr_ph) & ~initiator0_gnt;
        initiator1_pend_addr_ph <= (initiator1_address_ph | initiator1_pend_addr_ph) & ~initiator1_gnt; 

        //Transition to data phase when endpoint accepts address phase, hold when not ready
        initiator0_data_ph <= (initiator0_gnt) | (initiator0_data_ph & ~hreadyout_i);
        initiator1_data_ph <= (initiator1_gnt) | (initiator1_data_ph & ~hreadyout_i);
    end
end

always_comb initiator0_haddr = initiator0_pend_addr_ph ? initiator0_pend_haddr : haddr_i_0;
always_comb initiator0_htrans = initiator0_pend_addr_ph ? initiator0_pend_htrans : htrans_i_0;
always_comb initiator0_hsize = initiator0_pend_addr_ph ? initiator0_pend_hsize : hsize_i_0;
always_comb initiator0_hwrite = initiator0_pend_addr_ph ? initiator0_pend_hwrite : hwrite_i_0;

always_comb initiator1_haddr = initiator1_pend_addr_ph ? initiator1_pend_haddr : haddr_i_1;
always_comb initiator1_htrans = initiator1_pend_addr_ph ? initiator1_pend_htrans : htrans_i_1;
always_comb initiator1_hsize = initiator1_pend_addr_ph ? initiator1_pend_hsize : hsize_i_1;
always_comb initiator1_hwrite = initiator1_pend_addr_ph ? initiator1_pend_hwrite : hwrite_i_1;

//Select the appropriate initiator
//Initiator 0 gets priority
//Stall the grant if initiator 1 is processing a data phase and address phase b2b
always_comb initiator0_gnt = (initiator0_address_ph | initiator0_pend_addr_ph) & hreadyout_i;// & ~(initiator1_data_ph & initiator1_address_ph);

//Initiator 1 gets through only if initiator 0 isn't getting granted
always_comb initiator1_gnt = (initiator1_address_ph | initiator1_pend_addr_ph) & hreadyout_i & ~initiator0_gnt;

//Mux the appropriate initiator and send out
//Keep driving initiator 1 controls on data phase if init0 isn't getting a grant in that cycle
always_comb haddr_o  = initiator1_gnt | (initiator1_data_ph & ~initiator0_gnt) ? initiator1_haddr : initiator0_haddr;
always_comb htrans_o = initiator1_gnt | (initiator1_data_ph & ~initiator0_gnt) ? initiator1_htrans : initiator0_htrans;
always_comb hsize_o  = initiator1_gnt | (initiator1_data_ph & ~initiator0_gnt) ? initiator1_hsize : initiator0_hsize;
always_comb hwrite_o = initiator1_gnt | (initiator1_data_ph & ~initiator0_gnt) ? initiator1_hwrite : initiator0_hwrite;
always_comb hsel_o   = initiator1_gnt | (initiator1_data_ph & ~initiator0_gnt) ? hsel_i_1 : hsel_i_0;
always_comb hwdata_o = initiator1_gnt | (initiator1_data_ph & ~initiator0_gnt) ? hwdata_i_1 : hwdata_i_0;
always_comb hready_o = initiator1_gnt | (initiator1_data_ph & ~initiator0_gnt) ? (hready_i_1 | initiator1_pend_addr_ph) : (hready_i_0 | initiator0_pend_addr_ph);

//Send response to the initiator
//Mask the ready when it's a pending address phase
//Send the data coming from responder when selected
always_comb hresp_o_0  = initiator0_data_ph ? hresp_i : '0;
always_comb hrdata_o_0 = initiator0_data_ph ? hrdata_i : '0;
always_comb hready_o_0 = initiator0_pend_addr_ph ? '0 : 
                         initiator0_data_ph ? hreadyout_i : '1;

always_comb hresp_o_1  = initiator1_data_ph? hresp_i: '0;
always_comb hrdata_o_1 = initiator1_data_ph ? hrdata_i: '0;
always_comb hready_o_1 = initiator1_pend_addr_ph ? '0 : 
                         initiator1_data_ph ? hreadyout_i : '1;

`CALIPTRA_ASSERT_MUTEX(ERR_2TO1MUX_MUTEX_DATA_PH, {initiator0_data_ph,initiator1_data_ph}, hclk, hreset_n)
`CALIPTRA_ASSERT_NEVER(ERR_2TO1MUX_BAD_HTRANS, (htrans_o == 2'b01), hclk, hreset_n)
endmodule
