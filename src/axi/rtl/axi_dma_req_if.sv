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
//      Signals for internal transaction requests inside the Caliptra DMA
//      hardware assist block
//      Does not include any datapath signals (data, strb, wuser, ruser)
//      as these flow separately through the FIFO.
//

interface axi_dma_req_if #(parameter AW = 32) (input logic clk, input logic rst_n);

    import axi_pkg::*;

    logic valid;
    logic ready;
    logic [AW-1:0] addr;
    logic [AXI_LEN_BC_WIDTH-1:0] byte_len; // Byte count, max value per AXI spec
    logic fixed;
    logic lock;
    logic resp_valid;
    logic [$bits(axi_resp_e)-1:0] resp;

    modport src (
        output valid,
        input  ready,
        output addr,
        output byte_len,
        output fixed,
        output lock,
        input  resp_valid,
        input  resp
    );

    modport snk (
        input  valid,
        output ready,
        input  addr,
        input  byte_len,
        input  fixed,
        input  lock,
        output resp_valid,
        output resp
    );

endinterface
