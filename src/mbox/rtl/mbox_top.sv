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

module mbox_top #(
     parameter APB_ADDR_WIDTH = 18
    ,parameter APB_DATA_WIDTH = 32
    ,parameter APB_USER_WIDTH = 32
    ,parameter AHB_ADDR_WIDTH = 18
    ,parameter AHB_DATA_WIDTH = 32
    )
    (
    input logic clk,

    //SoC boot signals
    input logic cptra_pwrgood,
    input logic cptra_rst_b,

    output logic ready_for_fuses,
    output logic ready_for_fw_push,
    output logic ready_for_runtime,

    output logic mailbox_data_avail,
    output logic mailbox_flow_done,

    input logic  [63:0] generic_input_wires,
    output logic [63:0] generic_output_wires,

    //SoC APB Interface
    input logic [APB_ADDR_WIDTH-1:0]     paddr_i,
    input logic                          psel_i,
    input logic                          penable_i,
    input logic                          pwrite_i,
    input logic [APB_DATA_WIDTH-1:0]     pwdata_i,
    input logic [APB_USER_WIDTH-1:0]     pauser_i,
    output logic                         pready_o,
    output logic [APB_DATA_WIDTH-1:0]    prdata_o,
    output logic                         pslverr_o,

    //uC AHB Lite Interface
    input logic [AHB_ADDR_WIDTH-1:0]  haddr_i,
    input logic [AHB_DATA_WIDTH-1:0]  hwdata_i,
    input logic                       hsel_i,
    input logic                       hwrite_i,
    input logic                       hready_i,
    input logic [1:0]                 htrans_i,
    input logic [2:0]                 hsize_i,

    output logic                      hresp_o,
    output logic                      hreadyout_o,
    output logic [AHB_DATA_WIDTH-1:0] hrdata_o,

    //SoC Interrupts

    //uC Interrupts
    output wire              error_intr,
    output wire              notif_intr,

    //SRAM interface
    output mbox_sram_req_t  mbox_sram_req,
    input  mbox_sram_resp_t mbox_sram_resp,

    //Obfuscated UDS and FE
    input  logic [7:0][31:0] cptra_obf_key,
    output logic [7:0][31:0] cptra_obf_key_reg,
    output logic [31:0][31:0] obf_field_entropy,
    output logic [11:0][31:0] obf_uds_seed,

    //uC reset
    output logic cptra_uc_rst_b
);

//gasket to assemble mailbox request
logic soc_req_dv, soc_req_hold;
logic soc_req_error;
logic [APB_DATA_WIDTH-1:0] soc_req_rdata;
mbox_req_t soc_req;

//gasket to assemble mailbox request
logic uc_req_dv, uc_req_hold;
logic uc_req_error;
logic [MBOX_DATA_W-1:0] uc_req_rdata;
mbox_req_t uc_req;

//mbox req inf
logic mbox_req_dv;
logic mbox_dir_req_dv;
logic mbox_req_hold;
mbox_req_t mbox_req_data;
logic [MBOX_DATA_W-1:0] mbox_rdata;
logic mbox_error;

//mbox reg inf
logic mbox_reg_req_dv;
logic mbox_reg_req_hold;
mbox_reg_req_t mbox_reg_req_data;
logic [MBOX_DATA_W-1:0] mbox_reg_rdata;
logic mbox_reg_error, mbox_reg_read_error, mbox_reg_write_error;
logic clear_secrets;

// Pulse signals to trigger interrupts
logic uc_mbox_data_avail;
logic uc_mbox_data_avail_d;
logic uc_cmd_avail_p;

mbox_reg_pkg::mbox_reg__in_t mbox_reg_hwif_in;
mbox_reg_pkg::mbox_reg__out_t mbox_reg_hwif_out;

//Boot FSM
//This module contains the logic required to control the Caliptra Boot Flow
//Once the SoC has powered on Caliptra and de-asserted RESET, we can request fuses
//This FSM will de-assert reset and allow the Caliptra uC to boot after fuses are downloaded
mbox_boot_fsm mbox_boot_fsm1 (
    .clk(clk),
    .cptra_pwrgood(cptra_pwrgood),
    .cptra_rst_b (cptra_rst_b),

    .ready_for_fuses(ready_for_fuses),

    .fuse_done(mbox_reg_hwif_out.fuse_done.done.value),

    .cptra_uc_rst_b(cptra_uc_rst_b)
);

//APB Interface
//This module contains the logic for interfacing with the SoC over the APB Interface
//The SoC sends read and write requests using APB Protocol
//This wrapper decodes that protocol and issues requests to the arbitration block
apb_slv_sif #(
    .ADDR_WIDTH(APB_ADDR_WIDTH),
    .DATA_WIDTH(APB_DATA_WIDTH),
    .USER_WIDTH(APB_USER_WIDTH)
)
mailbox_apb_slv1 (
    //AMBA APB INF
    .PCLK(clk),
    .PRESETn(cptra_rst_b),
    .PADDR(paddr_i),
    .PPROT('x),
    .PSEL(psel_i),
    .PENABLE(penable_i),
    .PWRITE(pwrite_i),
    .PWDATA(pwdata_i),
    .PAUSER(pauser_i),

    .PREADY(pready_o),
    .PSLVERR(pslverr_o),
    .PRDATA(prdata_o),

    //COMPONENT INF
    .dv(soc_req_dv),
    .hold(soc_req_hold),
    .write(soc_req.write),
    .user(soc_req.user),
    .wdata(soc_req.wdata),
    .addr(soc_req.addr),
    .slverr(soc_req_error),
    .rdata(soc_req_rdata)
);
//req from apb is for soc always
always_comb soc_req.soc_req = 1'b1;

//AHB-Lite Interface
//This module contains the logic for interfacing with the Caliptra uC over the AHB-Lite Interface
//The Caliptra uC sends read and write requests using AHB-Lite Protocol
//This wrapper decodes that protocol and issues requests to the arbitration block
ahb_slv_sif #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(32)
)
mailbox_ahb_slv1 (
    //AMBA AHB Lite INF
    .hclk(clk),
    .hreset_n(cptra_uc_rst_b),
    .haddr_i(haddr_i),
    .hwdata_i(hwdata_i),
    .hsel_i(hsel_i),
    .hwrite_i(hwrite_i),
    .hready_i(hready_i),
    .htrans_i(htrans_i),
    .hsize_i(hsize_i),

    .hresp_o(hresp_o),
    .hreadyout_o(hreadyout_o),
    .hrdata_o(hrdata_o),


    //COMPONENT INF
    .dv(uc_req_dv),
    .hold(uc_req_hold),
    .error(uc_req_error),
    .write(uc_req.write),
    .wdata(uc_req.wdata),
    .addr(uc_req.addr),

    .rdata(uc_req_rdata)
);

always_comb uc_req.user = '1;
always_comb uc_req.soc_req = 1'b0;

//mailbox_arb
//This module contains the arbitration logic between SoC and Caliptra uC requests
//Requests are serviced using round robin arbitration

mbox_arb mbox_arb1 (
    .clk(clk),
    .rst_b(cptra_rst_b),
    //UC inf
    .uc_req_dv(uc_req_dv), 
    .uc_req_hold(uc_req_hold), 
    .uc_req_data(uc_req), 
    .uc_rdata(uc_req_rdata), 
    .uc_error(uc_req_error),
    //SOC inf
    .soc_req_dv(soc_req_dv),
    .soc_req_hold(soc_req_hold),
    .soc_req_data(soc_req),
    .soc_rdata(soc_req_rdata),
    .soc_error(soc_req_error),
    //MBOX inf
    .mbox_req_dv(mbox_req_dv),
    .mbox_dir_req_dv(mbox_dir_req_dv),
    .mbox_req_hold(mbox_req_hold),
    .mbox_req_data(mbox_req_data),
    .mbox_rdata(mbox_rdata),
    .mbox_error(mbox_error),
    //FUNC reg inf
    .mbox_reg_req_dv(mbox_reg_req_dv), 
    .mbox_reg_req_hold(1'b0),
    .mbox_reg_req_data(mbox_reg_req_data),
    .mbox_reg_rdata(mbox_reg_rdata),
    .mbox_reg_error(mbox_reg_error)

);

//Functional Registers and Fuses
//This module contains the functional registers maintained by the Caliptra Mailbox
//These registers are memory mapped per the Caliptra Specification
//Read and Write permissions are controlled within this block
always_comb mbox_reg_error = mbox_reg_read_error | mbox_reg_write_error;

always_comb mbox_reg_hwif_in.reset_b = cptra_rst_b;
always_comb mbox_reg_hwif_in.hard_reset_b = cptra_pwrgood;
always_comb mbox_reg_hwif_in.soc_req = mbox_reg_req_data.soc_req;

always_comb clear_secrets = mbox_reg_hwif_out.CLEAR_SECRETS.clear.value;

always_comb begin
    for (int i = 0; i < 8; i++) begin
        mbox_reg_hwif_in.obf_key[i].key.swwe = '0; //sw can't write to obf key
        mbox_reg_hwif_in.obf_key[i].key.wel = cptra_pwrgood; //capture value during pwrgood de-assertion
        mbox_reg_hwif_in.obf_key[i].key.next = cptra_obf_key[i];
        mbox_reg_hwif_in.obf_key[i].key.hwclr = clear_secrets;
        cptra_obf_key_reg[i] = mbox_reg_hwif_out.obf_key[i].key.value;
    end
    for (int i = 0; i < 12; i++) begin
        mbox_reg_hwif_in.uds_seed[i].seed.hwclr = clear_secrets; 
        obf_uds_seed[i] = mbox_reg_hwif_out.uds_seed[i].seed.value;
    end
    for (int i = 0; i < 32; i++) begin
        mbox_reg_hwif_in.field_entropy[i].seed.hwclr = clear_secrets;
        obf_field_entropy[i] = mbox_reg_hwif_out.field_entropy[i].seed.value;
    end

    //flow status
    ready_for_fw_push = mbox_reg_hwif_out.FLOW_STATUS.ready_for_fw.value;
    ready_for_runtime = mbox_reg_hwif_out.FLOW_STATUS.ready_for_runtime.value;

    //generic wires
    for (int i = 0; i < 2; i++) begin
        generic_output_wires[i*32+:32] = mbox_reg_hwif_out.generic_output_wires[i].generic_wires.value;
        mbox_reg_hwif_in.generic_input_wires[i].generic_wires.next = generic_input_wires[i*32+:32];
    end
end

// Pulse input to mbox_reg to set the interrupt status bit and generate interrupt output (if enabled)
always_comb mbox_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset  = 1'b0; // TODO @michnorris please assign
always_comb mbox_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_inv_dev_sts.hwset   = 1'b0; // TODO should decode from APB PAUSER
always_comb mbox_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_cmd_fail_sts.hwset  = 1'b0; // TODO @michnorris please assign -- should this be set by write of "FAIL" to mbox_csr.status if soc_req is set? (i.e. SoC cmd execution failed)
always_comb mbox_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_bad_fuse_sts.hwset  = 1'b0; // TODO @michnorris please assign
always_comb mbox_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_avail_sts.hwset = uc_cmd_avail_p; // TODO @michnorris to confirm



mbox_reg mbox_reg1 (
    .clk(clk),
    .rst('0),
    //qualify request so no addresses alias
    .s_cpuif_req(mbox_reg_req_dv & (mbox_reg_req_data.addr[MBOX_INF_ADDR_W-1:mbox_reg_pkg::MBOX_REG_ADDR_WIDTH] == MBOX_REG_MEM_START_ADDR[MBOX_INF_ADDR_W-1:mbox_reg_pkg::MBOX_REG_ADDR_WIDTH])),
    .s_cpuif_req_is_wr(mbox_reg_req_data.write),
    .s_cpuif_addr(mbox_reg_req_data.addr[mbox_reg_pkg::MBOX_REG_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data(mbox_reg_req_data.wdata),
    .s_cpuif_req_stall_wr(),
    .s_cpuif_req_stall_rd(),
    .s_cpuif_rd_ack(),
    .s_cpuif_rd_err(mbox_reg_read_error),
    .s_cpuif_rd_data(mbox_reg_rdata),
    .s_cpuif_wr_ack(),
    .s_cpuif_wr_err(mbox_reg_write_error),

    .hwif_in(mbox_reg_hwif_in),
    .hwif_out(mbox_reg_hwif_out)
);

assign error_intr = mbox_reg_hwif_out.intr_block_rf.error_global_intr_r.intr;
assign notif_intr = mbox_reg_hwif_out.intr_block_rf.notif_global_intr_r.intr;


//Mailbox
//This module contains the Caliptra Mailbox and associated control logic
//The SoC and uC can read and write to the mailbox by following the Caliptra Mailbox Protocol
mbox #(
    .DATA_W(APB_DATA_WIDTH),
    .SIZE_KB(MBOX_SIZE_KB)
    )
mbox1 (
    .clk(clk),
    .rst_b(cptra_uc_rst_b),
    .req_dv(mbox_req_dv), 
    .req_hold(mbox_req_hold),
    .dir_req_dv(mbox_dir_req_dv),
    .req_data(mbox_req_data),
    .mbox_error(mbox_error),
    .rdata(mbox_rdata),
    .mbox_sram_req(mbox_sram_req),
    .mbox_sram_resp(mbox_sram_resp),
    .soc_mbox_data_avail(mailbox_data_avail),
    .uc_mbox_data_avail(uc_mbox_data_avail)
);

// Generate a pulse to set the interrupt bit
always_ff @(posedge clk or negedge cptra_uc_rst_b) begin
    if (~cptra_uc_rst_b) begin
        uc_mbox_data_avail_d <= '0;
	end
	else begin
		uc_mbox_data_avail_d <= uc_mbox_data_avail;
	end
end

always_comb uc_cmd_avail_p = uc_mbox_data_avail & !uc_mbox_data_avail_d;

`ASSERT_KNOWN(ERR_AHB_INF_X, {hreadyout_o,hresp_o}, clk, cptra_rst_b)
//this generates an NMI in the core, but we don't have a handler so it just hangs
`ASSERT_NEVER(ERR_MBOX_AHB_ERR, hresp_o, clk, cptra_rst_b)
endmodule
