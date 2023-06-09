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
// AHB Lite Interface
// -------------------------------------------------------------

`ifndef CALIPTRA_AHB_LITE_BUS_INF
`define CALIPTRA_AHB_LITE_BUS_INF

interface CALIPTRA_AHB_LITE_BUS_INF
#(
    parameter AHB_LITE_ADDR_WIDTH = 32,
    parameter AHB_LITE_DATA_WIDTH = 32
);

    logic   [AHB_LITE_ADDR_WIDTH-1:0]   haddr;
    logic   [AHB_LITE_DATA_WIDTH-1:0]   hwdata;
    logic   [AHB_LITE_DATA_WIDTH-1:0]   hrdata;
    logic                               hsel;
    logic                               hwrite;
    logic   [2:0]                       hsize;
    logic   [1:0]                       htrans;
    logic                               hready;
    logic                               hreadyout;
    logic                               hresp;

    // ----------------------------------
    // Initiator ports - single initiator
    // ----------------------------------

    modport Initiator_Interface_Ports (
        input    haddr, hwdata, hwrite, hsize, htrans, // from AHB Initiator to AHB Responder
        output   hresp, hrdata, hreadyout                    // from AHB Responder to AHB Initiator
    );

    // -------------------------------------------
    // Responder Ports - go to multiple responders
    // -------------------------------------------

    modport Responder_Interface_Ports (
        input   hresp, hrdata, hreadyout,                   // from AHB Responder to AHB Initiator
        output  haddr, hwdata, hsel, hwrite, hsize, htrans, hready // AHB Initiator to AHB Responder
    );


endinterface

`endif //CALIPTRA_AHB_LITE_BUS_INF
