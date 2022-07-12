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

`include "caliptra_macros.svh"
`include "caliptra_sva.svh"

module apb_slv_sif #(
    parameter DATA_WIDTH = 32
   ,parameter ADDR_WIDTH = 32
   ,parameter USER_WIDTH = 32

   )
   (
    //AMBA APB INF
    input  logic                       PCLK,
    input  logic                       PRESETn,
    input  logic [ADDR_WIDTH-1:0]      PADDR,
    input  logic [2:0]                 PPROT,
    input  logic                       PSEL,
    input  logic                       PENABLE,
    input  logic                       PWRITE,
    input  logic [DATA_WIDTH-1:0]      PWDATA,
    input  logic [USER_WIDTH-1:0]      PAUSER,

    output logic                       PREADY,
    output logic                       PSLVERR,
    output logic [DATA_WIDTH-1:0]      PRDATA,

    //COMPONENT INF
    output logic                       dv,
    input  logic                       hold,
    output logic                       write,
    output logic [USER_WIDTH-1:0]      user,
    output logic [DATA_WIDTH-1:0]      wdata,
    output logic [ADDR_WIDTH-1:0]      addr,
    input  logic                       slverr,
    input  logic [DATA_WIDTH-1:0]      rdata
   );

logic setup_phase;
logic access_phase;


//setup phase of apb transaction
//select and ~enable
//flop the addr, write, write data and user attribute
always_comb setup_phase = PSEL & ~PENABLE;

`CLP_EN_FF(addr, PADDR, PCLK, setup_phase)
`CLP_EN_FF(write, PWRITE, PCLK, setup_phase)
`CLP_EN_FF(wdata, PWDATA, PCLK, setup_phase & PWRITE)
`CLP_EN_FF(user, PAUSER, PCLK, setup_phase)

//access phase of apb transaction
//select and enable

always_comb access_phase = PSEL & PENABLE;

//drive ready if no hold from component
always_comb PREADY = (dv & access_phase) ? ~hold : '1;
//drive read data from component
always_comb PRDATA = (dv & access_phase) ? rdata : '0;
//drive error from component for valid access, drive error for invalid access phase
always_comb PSLVERR = (dv & access_phase) ? slverr : 
                             access_phase ? '1 : '0;

//drive dv to component during access phase
//assume that access will necessarily follow setup phase
//setup phase becomes dv, gets cleared after seeing access phase and PREADY
`CLP_EN_RST_FF(dv, setup_phase, PCLK, (setup_phase | (access_phase & PREADY)), PRESETn)

//TODO ASSERTS
//assert that PADDR, PWRITE, PWDATA, PAUSER are constant while in access_phase
//`ASSERT(ERR_PADDR_NOT_CONST, (addr == PADDR), PCLK, PRESETn | ~access_phase)
//assert that access_phase always follows a setup_phase
//`ASSERT_NEVER(ERR_ACCESS_PHASE_WO_SETUP, access_phase & ~dv, PCLK, PRESETn)
//assert that access_phase is de-asserted the clock after ready is asserted
//`ASSERT(ERR_ACCESS_PHASE_NOT_COMPLETING, (dv & access_phase & PREADY) |-> ##1 ~access_phase, PCLK, PRESETn)

endmodule