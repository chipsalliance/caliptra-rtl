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
// AHB Lite Address Decoder
// -------------------------------------------------------------

module ahb_lite_address_decoder #(
    parameter AHB_LITE_ADDR_WIDTH   = 32,
    parameter AHB_LITE_DATA_WIDTH   = 32,
    parameter NUM_RESPONDERS        = 8
) (
    // ---------------------------------------
    // Global clock/reset
    // ---------------------------------------
    input logic     hclk,
    input logic     hreset_n,

    // ---------------------------------------
    // From Initiator Interface Port
    // ---------------------------------------
    input logic     [AHB_LITE_ADDR_WIDTH-1:0]   haddr_i,
    input logic     [AHB_LITE_DATA_WIDTH-1:0]   hwdata_i,
    input logic                                 hwrite_i,
    input logic     [1:0]                       htrans_i, 
    input logic     [2:0]                       hsize_i,

    output logic                                hresp_o,
    output logic                                hinitiatorready_o,
    output logic    [AHB_LITE_DATA_WIDTH-1:0]   hrdata_o,

    // ---------------------------------------
    // To Responder Interface Port
    // ---------------------------------------
    input logic     [NUM_RESPONDERS-1:0]                            hresp_i,
    input logic     [NUM_RESPONDERS-1:0][AHB_LITE_DATA_WIDTH-1:0]   hrdata_i, 
    input logic     [NUM_RESPONDERS-1:0]                            hreadyout_i,

    output logic    [NUM_RESPONDERS-1:0][AHB_LITE_ADDR_WIDTH-1:0]   haddr_o, 
    output logic    [NUM_RESPONDERS-1:0][AHB_LITE_DATA_WIDTH-1:0]   hwdata_o, 
    output logic    [NUM_RESPONDERS-1:0]                            hsel_o, 
    output logic    [NUM_RESPONDERS-1:0]                            hwrite_o, 
    output logic    [NUM_RESPONDERS-1:0]                            hresponderready_o,
    output logic    [NUM_RESPONDERS-1:0][1:0]                       htrans_o,
    output logic    [NUM_RESPONDERS-1:0][2:0]                       hsize_o,

    // ----------------------------------------------
    // Respnder Disable
    // ----------------------------------------------
    input logic     [NUM_RESPONDERS-1:0]                            responder_disable_i,
    output logic    [NUM_RESPONDERS-1:0]                            access_blocked_o,

    // -----------------------------------------------
    // Responder Address Map (Start and End Addresses)
    // -----------------------------------------------
    input logic     [NUM_RESPONDERS-1:0][AHB_LITE_ADDR_WIDTH-1:0]   responder_start_addr_i,
    input logic     [NUM_RESPONDERS-1:0][AHB_LITE_ADDR_WIDTH-1:0]   responder_end_addr_i

);

    localparam AHB_XFER_IDLE   = 2'b00;
    localparam AHB_XFER_BUSY   = 2'b01;
    localparam AHB_XFER_NONSEQ = 2'b10;
    localparam AHB_XFER_SEQ    = 2'b11;

    logic [NUM_RESPONDERS-1:0]                          pending_hsel;
    logic                                               hinitiator_ready_default;
    logic                                               hinitiator_ready_int;
    logic [NUM_RESPONDERS-1:0]                          hsel_o_int_pre;
    logic [NUM_RESPONDERS-1:0]                          hsel_blocked;
    logic [NUM_RESPONDERS-1:0]                          hsel_o_int;
    logic                                               hresp_error;
    logic                                               hresp_error_r;



    // Decode the address to appropriate Responder HSEL
    genvar resp_num;
    generate
        for (resp_num = 0; resp_num < NUM_RESPONDERS; resp_num++) begin: gen_responder_hsel
            assign hsel_o_int_pre[resp_num] = (haddr_i >= responder_start_addr_i[resp_num]) && (haddr_i <= responder_end_addr_i[resp_num]);
            assign hsel_blocked  [resp_num] = hsel_o_int_pre[resp_num] &&  responder_disable_i[resp_num];
            assign hsel_o_int    [resp_num] = hsel_o_int_pre[resp_num] && !responder_disable_i[resp_num];
        end
    endgenerate

    // Pulse during address phase indicating an access was attempted to a disabled responder
    always @(posedge hclk or negedge hreset_n) begin
        if (!hreset_n)
            access_blocked_o <= '0;
        else if (|htrans_i && hinitiator_ready_int && |hsel_blocked)
            access_blocked_o <= hsel_blocked;
        else
            access_blocked_o <= '0;
    end

    always @(posedge hclk or negedge hreset_n) begin
        if (!hreset_n)
            pending_hsel    <= '0;
        else if (|htrans_i && hinitiator_ready_int)
            pending_hsel    <= hsel_o_int;
        else if (hinitiator_ready_int)
            pending_hsel    <= '0;
    end

    always_comb begin
        // Only flag errors for NONSEQ or SEQ type transfers
        // (BUSY transfers require OKAY response)
        hresp_error = htrans_i inside {AHB_XFER_NONSEQ, AHB_XFER_SEQ} && hinitiator_ready_int && ~|hsel_o_int;
    end

    always @(posedge hclk or negedge hreset_n) begin
        if (!hreset_n)
            hinitiator_ready_default <= 1'b1;
        else
            hinitiator_ready_default <= !hresp_error;
    end

    always @(posedge hclk or negedge hreset_n) begin
        if (!hreset_n)
            hresp_error_r <= 1'b0;
        else if (hresp_error)
            hresp_error_r <= 1'b1;
        else if (hinitiator_ready_int)
            hresp_error_r <= 1'b0;
        else
            hresp_error_r <= hresp_error_r;
    end

    // Drive the address phase of the AHB Lite Transaction
    always_comb begin
        for (int rr = 0; rr < NUM_RESPONDERS; rr++) begin
            hresponderready_o[rr]    = hinitiator_ready_int;
            hwrite_o[rr]             = hwrite_i;
            htrans_o[rr]             = htrans_i;
            hsize_o[rr]              = hsize_i;
            haddr_o[rr]              = haddr_i;
            hwdata_o[rr]             = hwdata_i;
        end
    end

    // Use retimed select to drive response / data phase of the AHB Lite Transaction
    // Default (for the case where an access does not hit any responder) is to
    // return rdata = 0 and hresp = 1
    // This code will inject hresp = 1 for non-decoded addresses or blocked accesses
    always_comb begin
        hrdata_o                = {AHB_LITE_DATA_WIDTH{1'b0}};
        hresp_o                 = hresp_error_r;
        hinitiator_ready_int    = hinitiator_ready_default; // Deassert for hresp = 1, first cycle
        for (int rr = 0; rr < NUM_RESPONDERS; rr++) begin
            if (hsel_o_int[rr] == 1'b1) begin
                hinitiator_ready_int    = hreadyout_i[rr];
            end
        end
        for (int rr = 0; rr < NUM_RESPONDERS; rr++) begin
            if (pending_hsel[rr] == 1'b1) begin
                hrdata_o                = hrdata_i[rr];
                hresp_o                 = hresp_i[rr];
                hinitiator_ready_int    = hreadyout_i[rr];
            end
        end
    end

    assign hsel_o               = hsel_o_int;
    assign hinitiatorready_o    = hinitiator_ready_int;

endmodule
