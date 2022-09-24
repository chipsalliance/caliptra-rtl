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


// Instantiate caliptra_top, providing a port connection for el2_mem_export, to
// resolve a VCS error that is produced about illegal missing port connection
// (only results in an "ERROR" for the interface-type ports).
// The error occurs because caliptra_top_tb, which does provide the port
// connection, is compiled later in a separate process.
// This module has no other function than to assist in the iterative compilation
// flow.
module caliptra_top_dummy();

logic cptra_rst_b;
initial begin
    cptra_rst_b = 1'b0;
    #100ns cptra_rst_b = 1'b1;
end


bit                          clk;
initial clk = 1'b0;
always #10ns clk <= ~clk;


el2_mem_if el2_mem_export (); // clock is provided inside the SweRV processor

logic                        cptra_pwrgood;

logic [255:0]                cptra_obf_key;

//JTAG Interface
logic                        jtag_tck;    // JTAG clk
logic                        jtag_tms;    // JTAG TMS
logic                        jtag_tdi;    // JTAG tdi
logic                        jtag_trst_n; // JTAG Reset //TODO optional needs review
logic                       jtag_tdo;    // JTAG TDO

//APB Interface
logic [`APB_ADDR_WIDTH-1:0] PADDR;
logic [2:0]                 PPROT;
logic                       PSEL;
logic                       PENABLE;
logic                       PWRITE;
logic [`APB_DATA_WIDTH-1:0] PWDATA;
logic [`APB_USER_WIDTH-1:0] PAUSER;

logic                       PREADY;
logic                       PSLVERR;
logic [`APB_DATA_WIDTH-1:0] PRDATA;

//QSPI Interface
logic                       qspi_clk_o;
logic [`QSPI_CS_WIDTH-1:0]  qspi_cs_no;
wire  [`QSPI_IO_WIDTH-1:0]  qspi_d_io;

//UART Interface
//TODO update with UART interface signals

//I3C Interface
//TODO update with I3C interface signals

logic                       ready_for_fuses;
logic                       ready_for_fw_push;
logic                       ready_for_runtime;

logic                       mailbox_data_avail;
logic                       mailbox_flow_done;

logic                        BootFSM_BrkPoint;

logic  [63:0]                generic_input_wires;
logic [63:0]                generic_output_wires;

logic  [`SOC_SEC_STATE_WIDTH-1:0] security_state;







caliptra_top dut (
    .clk(clk),

    .cptra_pwrgood(cptra_pwrgood),
    .cptra_rst_b(cptra_rst_b),

    .cptra_obf_key(cptra_obf_key),

    //JTAG Interface
    .jtag_tck(jtag_tck),    // JTAG clk
    .jtag_tms(jtag_tms),    // JTAG TMS
    .jtag_tdi(jtag_tdi),    // JTAG tdi
    .jtag_trst_n(jtag_trst_n), // JTAG Reset //TODO optional needs review
    .jtag_tdo(jtag_tdo),    // JTAG TDO

    //APB Interface
    .PADDR(PADDR),
    .PPROT(PPROT),
    .PSEL(PSEL),
    .PENABLE(PENABLE),
    .PWRITE(PWRITE),
    .PWDATA(PWDATA),
    .PAUSER(PAUSER),

    .PREADY(PREADY),
    .PSLVERR(PSLVERR),
    .PRDATA(PRDATA),

    //QSPI Interface
    .qspi_clk_o(qspi_clk_o),
    .qspi_cs_no(qspi_cs_no),
    .qspi_d_io(qspi_d_io),

    //UART Interface
    //TODO update with UART interface signals

    //I3C Interface
    //TODO update with I3C interface signals

    // Caliptra Memory Export Interface
    .el2_mem_export(el2_mem_export),

    .ready_for_fuses(ready_for_fuses),
    .ready_for_fw_push(ready_for_fw_push),
    .ready_for_runtime(ready_for_runtime),

    .mailbox_data_avail(mailbox_data_avail),
    .mailbox_flow_done(mailbox_flow_done),

    .BootFSM_BrkPoint(BootFSM_BrkPoint),

    .generic_input_wires(generic_input_wires),
    .generic_output_wires(generic_output_wires),

    .security_state(security_state)

);

endmodule
