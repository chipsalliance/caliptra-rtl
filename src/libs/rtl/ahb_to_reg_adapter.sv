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
//======================================================================
//
// ahb_to_reg_adapter.sv
// --------
// This module converts the output of the ahb slave interface to a register
// interface.
//
//======================================================================


module ahb_to_reg_adapter#(
    parameter DATA_WIDTH = 32,
    parameter DATA_BYTE_WIDTH = DATA_WIDTH / 8,
    parameter ADDR_WIDTH = 32
  ) (
    input  logic                       clk,
    input  logic                       rst_n,
    // Signals from  ahb slave interface
    input  logic                       ahb_reg_dv,
    output logic                       ahb_reg_hld,
    output logic                       ahb_reg_err,
    input  logic                       ahb_reg_write,
    input  logic [DATA_WIDTH-1:0]      ahb_reg_wdata,
    input  logic [ADDR_WIDTH-1:0]      ahb_reg_addr,
    output logic [DATA_WIDTH-1:0]      ahb_reg_rdata,
    // register interface signals
    output logic                       reg_we,
    output logic                       reg_re,
    output logic [ADDR_WIDTH-1:0]      reg_addr,
    output logic [DATA_WIDTH-1:0]      reg_wdata,
    output logic [DATA_BYTE_WIDTH-1:0] reg_be,
    input  logic [DATA_WIDTH-1:0]      reg_rdata,
    input  logic                       reg_error,
    input  logic                       reg_busy
    );

  always_comb begin
    // default
    ahb_reg_rdata = reg_rdata;
    ahb_reg_err   = reg_error;
    ahb_reg_hld   = reg_busy;
    reg_addr      = ahb_reg_addr;
    reg_wdata     = ahb_reg_wdata;
    reg_we        = ahb_reg_dv && ahb_reg_write && !ahb_reg_hld;
  end

  assign reg_re = ahb_reg_dv && !ahb_reg_write;

  // Write all bytes at any given time.  The AHB interface module only accepts hsize_i
  // when it is set to 'h2 = Word(32b) and 'h3 = Double Word(64b).
  assign reg_be = {DATA_BYTE_WIDTH{1'b1}};
endmodule
