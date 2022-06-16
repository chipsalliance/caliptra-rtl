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

module mbox #(
     parameter APB_DATA_WIDTH = 64
    ,parameter APB_ADDR_WIDTH = 32
    ,parameter APB_USER_REQ_WIDTH = 32

    )(
    input logic clk,

    //SoC boot signals
    input logic cptra_pwrgood,
    input logic cptra_rst_b,

    //SoC APB Interface
    input logic [APB_ADDR_WIDTH-1:0]     apb_paddr,
    input logic [2:0]                    apb_pprot,
    input logic                          apb_psel,
    input logic                          apb_penable,
    input logic                          apb_pwrite,
    input logic [APB_DATA_WIDTH-1:0]     apb_pwdata,
    input logic [(APB_DATA_WIDTH/8)-1:0] apb_pstrb,
    input logic [APB_USER_REQ_WIDTH-1:0] apb_pauser,
    output logic                         apb_pready,
    output logic [APB_DATA_WIDTH-1:0]    apb_prdata,
    output logic                         apb_pslverr,

    //uC AHB Lite Interface

    //SoC Interrupts

    //uC Interrupts

    //uC reset
    output logic cptra_uc_rst_b
);

//Boot FSM
//This module contains the logic required to control the Caliptra Boot Flow
//Once the SoC has powered on Caliptra and de-asserted RESET, we can request fuses
//This FSM will de-assert reset and allow the Caliptra uC to boot after fuses are downloaded
mbox_boot_fsm mbox_boot_fsm1 (
    .clk(clk),
    .cptra_pwrgood(cptra_pwrgood),
    .cptra_rst_b (cptra_rst_b),

    .fuse_done('1), //FIXME TIE-OFF

    .cptra_uc_rst_b(cptra_uc_rst_b)
);

//APB Interface
//This module contains the logic for interfacing with the SoC over the APB Interface
//The SoC sends read and write requests using APB Protocol
//This wrapper decodes that protocol and issues requests to the arbitration block

//TODO: APB Wrapper

//AHB-Lite Interface
//This module contains the logic for interfacing with the Caliptra uC over the AHB-Lite Interface
//The Caliptra uC sends read and write requests using AHB-Lite Protocol
//This wrapper decodes that protocol and issues requests to the arbitration block

//TODO: AHB-Lite Wrapper

//mailbox_arb
//This module contains the arbitration logic between SoC and Caliptra uC requests
//Requests are serviced using round robin arbitration

//TODO: mbox_arb

//Functional Registers
//This module contains the functional registers maintained by the Caliptra Mailbox
//These registers are memory mapped per the Caliptra Specification
//Read and Write permissions are controlled within this block

//TODO: mbox_func_reg

//Fuses
//This module contains the fuse registers maintained by the Caliptra Mailbox
//These fuses are memory mapped per the Caliptra Specification
//Read and Write permissions are controlled within this block

//TODO: mbox_fuse_reg

//Mailbox
//This module contains the Caliptra Mailbox and associated control logic
//The SoC and uC can read and write to the mailbox by following the Caliptra Mailbox Protocol

//TODO: mbox


endmodule