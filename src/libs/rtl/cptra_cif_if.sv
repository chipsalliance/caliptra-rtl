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
// Description:
//      Signals for caliptra's internal fabric interface
//

interface cptra_cif_if #(parameter integer ADDR_WIDTH = 32, parameter integer DATA_WIDTH = 32, parameter integer ID_WIDTH = 8, parameter integer USER_WIDTH = 32) (input logic clk, input logic rst_b);

    typedef struct packed {
        logic                       write;
        logic   [ADDR_WIDTH-1:0]    addr;
        logic   [DATA_WIDTH-1:0]    wdata;
        logic   [DATA_WIDTH/8-1:0]  wstrb;
        logic   [2:0]               size;
        logic                       last;
        logic   [USER_WIDTH-1:0]    user;
        logic   [ID_WIDTH-1:0]      id;
    } cif_req_data_t;

    logic                       dv;
    logic                       hold;
    logic   [DATA_WIDTH-1:0]    rdata;
    logic                       error;
    cif_req_data_t              req_data;


    // Modport for read manager
    modport request (

        output  dv,
        output  req_data,
        
        input   hold,
        input   rdata,
        input   error
    );

    // Modport for write manager
    modport response (
        input   dv,
        input   req_data,
        
        output  hold,
        output  rdata,
        output  error
    );

endinterface
