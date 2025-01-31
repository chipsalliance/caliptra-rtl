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
// AHB Lite Bus
// -------------------------------------------------------------

module ahb_lite_bus #(
    parameter AHB_LITE_ADDR_WIDTH = 32, 
    parameter AHB_LITE_DATA_WIDTH = 32, 
    parameter NUM_RESPONDERS = 8
) (
    // ---------------------------------------
    // Global clock/reset
    // ---------------------------------------
    input logic     hclk,
    input logic     hreset_n,

    // ---------------------------------------
    // Initiator Interface Port
    // ---------------------------------------
    CALIPTRA_AHB_LITE_BUS_INF.Initiator_Interface_Ports ahb_lite_initiator,

    // --------------------------------------
    // Responder Interface Port
    // --------------------------------------
    CALIPTRA_AHB_LITE_BUS_INF.Responder_Interface_Ports ahb_lite_responders[0:NUM_RESPONDERS-1],

    // ----------------------------------------------
    // Respnder Disable
    // ----------------------------------------------
    input  logic [NUM_RESPONDERS-1:0]                         ahb_lite_resp_disable_i,
    output logic [NUM_RESPONDERS-1:0]                         ahb_lite_resp_access_blocked_o,

    // ----------------------------------------------
    // Responder Address Map (Start and End addresses)
    // ----------------------------------------------
    input logic [NUM_RESPONDERS-1:0][AHB_LITE_ADDR_WIDTH-1:0] ahb_lite_start_addr_i,
    input logic [NUM_RESPONDERS-1:0][AHB_LITE_ADDR_WIDTH-1:0] ahb_lite_end_addr_i,

    // ----------------------------------------------
    // Force bus idle during uc reset to prevent RDC violations
    // ----------------------------------------------
    input logic force_bus_idle
);

    logic   [NUM_RESPONDERS-1:0][AHB_LITE_ADDR_WIDTH-1:0]   haddr;
    logic   [NUM_RESPONDERS-1:0][AHB_LITE_DATA_WIDTH-1:0]   hwdata;
    logic   [NUM_RESPONDERS-1:0][AHB_LITE_DATA_WIDTH-1:0]   hrdata;
    logic   [NUM_RESPONDERS-1:0]                            hsel;
    logic   [NUM_RESPONDERS-1:0]                            hwrite;
    logic   [NUM_RESPONDERS-1:0]                            hready;
    logic   [NUM_RESPONDERS-1:0][1:0]                       htrans;
    logic   [NUM_RESPONDERS-1:0][2:0]                       hsize;
    logic   [NUM_RESPONDERS-1:0]                            hresp;
    logic   [NUM_RESPONDERS-1:0]                            hreadyout;

    // Hook up the responder ports

    genvar ii;
    generate
        for (ii = 0; ii < NUM_RESPONDERS; ii++) begin: gen_responder_hook_up
            assign ahb_lite_responders[ii].haddr         = haddr[ii];
            assign ahb_lite_responders[ii].hwdata        = hwdata[ii];
            assign ahb_lite_responders[ii].hsel          = hsel[ii];
            assign ahb_lite_responders[ii].hwrite        = hwrite[ii];
            assign ahb_lite_responders[ii].hready        = hready[ii];
            assign ahb_lite_responders[ii].htrans        = htrans[ii];
            assign ahb_lite_responders[ii].hsize         = hsize[ii];

            assign hrdata[ii]       = ahb_lite_responders[ii].hrdata;
            assign hresp[ii]        = ahb_lite_responders[ii].hresp;
            assign hreadyout[ii]    = ahb_lite_responders[ii].hreadyout;
        end
    endgenerate

    // Instantiate AHB Lite Address Decoder
    ahb_lite_address_decoder #(
        .AHB_LITE_ADDR_WIDTH    (AHB_LITE_ADDR_WIDTH),
        .AHB_LITE_DATA_WIDTH    (AHB_LITE_DATA_WIDTH),
        .NUM_RESPONDERS         (NUM_RESPONDERS)
    ) u_ahb_lite_address_decoder (
        // -------------------------------------
        // Global clock/reset
        // -------------------------------------
        .hclk           (hclk),
        .hreset_n       (hreset_n),

        // --------------------------------------
        // From Initiator
        // --------------------------------------

        // Inputs
        .haddr_i            (ahb_lite_initiator.haddr),
        .hwdata_i           (ahb_lite_initiator.hwdata),
        .hwrite_i           (ahb_lite_initiator.hwrite),
        .htrans_i           (ahb_lite_initiator.htrans),
        .hsize_i            (ahb_lite_initiator.hsize),
        // Outputs
        .hresp_o            (ahb_lite_initiator.hresp),
        .hinitiatorready_o  (ahb_lite_initiator.hreadyout),
        .hrdata_o           (ahb_lite_initiator.hrdata),

        // --------------------------------------
        // To Responder
        // --------------------------------------

        // Inputs
        .hresp_i            (hresp),
        .hrdata_i           (hrdata),
        .hreadyout_i        (hreadyout),
        // Outputs
        .haddr_o            (haddr),
        .hwdata_o           (hwdata),
        .hsel_o             (hsel),
        .hwrite_o           (hwrite),
        .hresponderready_o  (hready),
        .htrans_o           (htrans),
        .hsize_o            (hsize),

        .force_bus_idle     (force_bus_idle),

        // ----------------------------------------------
        // Responder Disable
        // ----------------------------------------------
        .responder_disable_i          (ahb_lite_resp_disable_i),
        .access_blocked_o             (ahb_lite_resp_access_blocked_o),

        // -----------------------------------------
        // Configuration Address Port
        // -----------------------------------------
        .responder_start_addr_i       (ahb_lite_start_addr_i),
        .responder_end_addr_i         (ahb_lite_end_addr_i)

    );
endmodule
