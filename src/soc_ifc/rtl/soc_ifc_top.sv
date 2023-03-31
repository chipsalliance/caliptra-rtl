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

`include "caliptra_sva.svh"
`include "caliptra_macros.svh"

module soc_ifc_top 
    import soc_ifc_pkg::*;
    import soc_ifc_reg_pkg::*;
    #(
     parameter APB_ADDR_WIDTH = 18
    ,parameter APB_DATA_WIDTH = 32
    ,parameter APB_USER_WIDTH = 32
    ,parameter AHB_ADDR_WIDTH = 18
    ,parameter AHB_DATA_WIDTH = 32
    )
    (
    input logic clk,
    input logic clk_cg,
    input logic soc_ifc_clk_cg,

    //SoC boot signals
    input logic cptra_pwrgood,
    input logic cptra_rst_b,

    output logic ready_for_fuses,
    output logic ready_for_fw_push,
    output logic ready_for_runtime,

    output logic mailbox_data_avail,
    output logic mailbox_flow_done,

    input var security_state_t security_state,

    input logic  [1:0][31:0] generic_input_wires,
    input logic BootFSM_BrkPoint,
    output logic [1:0][31:0] generic_output_wires,

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
    output logic             cptra_error_fatal,
    output logic             cptra_error_non_fatal,
    output logic             trng_req,

    //uC Interrupts
    output wire              soc_ifc_error_intr,
    output wire              soc_ifc_notif_intr,
    output wire              sha_error_intr,
    output wire              sha_notif_intr,

    //SRAM interface
    output mbox_sram_req_t  mbox_sram_req,
    input  mbox_sram_resp_t mbox_sram_resp,

    //Obfuscated UDS and FE
    input  logic clear_obf_secrets,
    input  logic scan_mode_f,
    input  logic [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key,
    output logic [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key_reg,
    output logic [`CLP_OBF_FE_DWORDS-1 :0][31:0] obf_field_entropy,
    output logic [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed,

    // NMI Vector 
    output logic [31:0] nmi_vector,
    output logic nmi_intr,

    // ICCM Lock
    output logic iccm_lock,
    input  logic iccm_axs_blocked,

    //Other blocks reset
    output logic cptra_noncore_rst_b,
    //uC reset
    output logic cptra_uc_rst_b,
    //Clock gating
    output logic clk_gating_en,

    //caliptra uncore jtag ports
    input  logic                            cptra_uncore_dmi_reg_en,
    input  logic                            cptra_uncore_dmi_reg_wr_en,
    output logic [31:0]                     cptra_uncore_dmi_reg_rdata,
    input  logic [6:0]                      cptra_uncore_dmi_reg_addr,
    input  logic [31:0]                     cptra_uncore_dmi_reg_wdata 
);

//gasket to assemble mailbox request
logic soc_req_dv, soc_req_hold;
logic soc_req_error;
logic [APB_DATA_WIDTH-1:0] soc_req_rdata;
soc_ifc_req_t soc_req;

//gasket to assemble mailbox request
logic uc_req_dv, uc_req_hold;
logic uc_req_error;
logic [SOC_IFC_DATA_W-1:0] uc_req_rdata;
soc_ifc_req_t uc_req;

//mbox req inf
logic mbox_req_dv;
logic mbox_dir_req_dv;
logic mbox_req_hold;
soc_ifc_req_t mbox_req_data;
logic [SOC_IFC_DATA_W-1:0] mbox_rdata;
logic mbox_error;

//sha req inf
logic sha_req_dv;
logic sha_req_hold;
soc_ifc_req_t sha_req_data;
logic [SOC_IFC_DATA_W-1:0] sha_rdata;
logic sha_error;

//mbox reg inf
logic soc_ifc_reg_req_dv;
logic soc_ifc_reg_req_hold;
soc_ifc_req_t soc_ifc_reg_req_data;
logic [SOC_IFC_DATA_W-1:0] soc_ifc_reg_rdata;
logic soc_ifc_reg_error, soc_ifc_reg_read_error, soc_ifc_reg_write_error;

logic sha_sram_req_dv;
logic [MBOX_ADDR_W-1:0] sha_sram_req_addr;
mbox_sram_resp_t sha_sram_resp;
logic sha_sram_hold;

logic [4:0][APB_USER_WIDTH-1:0] valid_mbox_users;

// Pulse signals to trigger interrupts
logic uc_mbox_data_avail;
logic uc_mbox_data_avail_d;
logic uc_cmd_avail_p;
logic security_state_debug_locked_d;
logic security_state_debug_locked_p;
logic sram_single_ecc_error;
logic sram_double_ecc_error;
logic soc_req_mbox_lock;

logic iccm_unlock;
logic fw_upd_rst_executed;
logic fuse_wr_done_reg_write_observed;

logic pwrgood_toggle_hint;
logic Warm_Reset_Capture_Flag;

logic BootFSM_BrkPoint_Latched;
logic BootFSM_BrkPoint_Flag;

logic dmi_inc_rdptr;
logic cptra_uncore_dmi_reg_dout_access_f;
mbox_dmi_reg_t mbox_dmi_reg;
logic [31:0] cptra_uncore_dmi_reg_rdata_in;

soc_ifc_reg__in_t soc_ifc_reg_hwif_in;
soc_ifc_reg__out_t soc_ifc_reg_hwif_out;

//WDT signals
logic [WDT_TIMEOUT_PERIOD_NUM_DWORDS-1:0][31:0] timer1_timeout_period;
logic [WDT_TIMEOUT_PERIOD_NUM_DWORDS-1:0][31:0] timer2_timeout_period;
logic timer1_en;
logic timer2_en;
logic timer1_restart;
logic timer2_restart;
logic t1_timeout;
logic t1_timeout_f; //To generate interrupt pulse
logic t1_timeout_p;
logic t2_timeout;
logic t2_timeout_f; //To generate interrupt pulse
logic t2_timeout_p;
logic wdt_notif_t1_intr_serviced;
logic wdt_notif_t2_intr_serviced;
logic soc_ifc_notif_intr_f;

//Boot FSM
//This module contains the logic required to control the Caliptra Boot Flow
//Once the SoC has powered on Caliptra and de-asserted RESET, we can request fuses
//This FSM will de-assert reset and allow the Caliptra uC to boot after fuses are downloaded
soc_ifc_boot_fsm i_soc_ifc_boot_fsm (
    .clk(clk),
    .cptra_pwrgood(cptra_pwrgood),
    .cptra_rst_b (cptra_rst_b),
    .fw_update_rst (soc_ifc_reg_hwif_out.internal_fw_update_reset.core_rst.value),
    .fw_update_rst_wait_cycles (soc_ifc_reg_hwif_out.internal_fw_update_reset_wait_cycles.wait_cycles.value),
    .ready_for_fuses(ready_for_fuses),

    .fuse_done(soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value),
    .fuse_wr_done_observed(fuse_wr_done_reg_write_observed),

    .BootFSM_BrkPoint(BootFSM_BrkPoint_Latched),
    .BootFSM_Continue(soc_ifc_reg_hwif_out.CPTRA_BOOTFSM_GO.GO.value),

    .cptra_noncore_rst_b(cptra_noncore_rst_b), //goes to all other blocks
    .cptra_uc_rst_b(cptra_uc_rst_b), //goes to veer core
    .iccm_unlock(iccm_unlock),
    .fw_upd_rst_executed(fw_upd_rst_executed)
);

always_comb soc_ifc_reg_hwif_in.CPTRA_RESET_REASON.FW_UPD_RESET.we = fw_upd_rst_executed;
always_comb soc_ifc_reg_hwif_in.CPTRA_RESET_REASON.FW_UPD_RESET.next = 1;

//APB Interface
//This module contains the logic for interfacing with the SoC over the APB Interface
//The SoC sends read and write requests using APB Protocol
//This wrapper decodes that protocol and issues requests to the arbitration block
apb_slv_sif #(
    .ADDR_WIDTH(APB_ADDR_WIDTH),
    .DATA_WIDTH(APB_DATA_WIDTH),
    .USER_WIDTH(APB_USER_WIDTH)
)
i_apb_slv_sif_soc_ifc (
    //AMBA APB INF
    .PCLK(soc_ifc_clk_cg),
    .PRESETn(cptra_rst_b),
    .PADDR(paddr_i),
    .PPROT('0),
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
    .req_hold(soc_req_hold),
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
i_ahb_slv_sif_soc_ifc (
    //AMBA AHB Lite INF
    .hclk(clk_cg),
    .hreset_n(cptra_noncore_rst_b),
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
    .hld(uc_req_hold),
    .err(uc_req_error),
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

soc_ifc_arb #(
    .APB_USER_WIDTH(APB_USER_WIDTH)
    )
    i_soc_ifc_arb (
    .clk(soc_ifc_clk_cg),
    .rst_b(cptra_rst_b),
    .valid_mbox_users(valid_mbox_users),
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
    //SHA inf
    .sha_req_dv(sha_req_dv),
    .sha_req_hold(sha_req_hold),
    .sha_req_data(sha_req_data),
    .sha_rdata(sha_rdata),
    .sha_error(sha_error),
    //FUNC reg inf
    .soc_ifc_reg_req_dv(soc_ifc_reg_req_dv), 
    .soc_ifc_reg_req_hold(1'b0),
    .soc_ifc_reg_req_data(soc_ifc_reg_req_data),
    .soc_ifc_reg_rdata(soc_ifc_reg_rdata),
    .soc_ifc_reg_error(soc_ifc_reg_error)

);


//Functional Registers and Fuses
//This module contains the functional registers maintained by the Caliptra Mailbox
//These registers are memory mapped per the Caliptra Specification
//Read and Write permissions are controlled within this block
always_comb soc_ifc_reg_error = soc_ifc_reg_read_error | soc_ifc_reg_write_error;

always_comb soc_ifc_reg_hwif_in.cptra_rst_b = cptra_rst_b;
always_comb soc_ifc_reg_hwif_in.cptra_pwrgood = cptra_pwrgood;
always_comb soc_ifc_reg_hwif_in.soc_req = soc_ifc_reg_req_data.soc_req;

`ifdef CALIPTRA_INTERNAL_TRNG
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.iTRNG_en.next = 1'b1;
`else
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.iTRNG_en.next = 1'b0;
`endif
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.QSPI_en.next = 1'b0;
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.I3C_en.next = 1'b0;

always_comb begin
    for (int i = 0; i < `CLP_OBF_KEY_DWORDS; i++) begin
        soc_ifc_reg_hwif_in.internal_obf_key[i].key.swwe = '0; //sw can't write to obf key
        //Sample only if its a pwrgood cycle, in debug locked state and scan mode is not asserted (as in do not sample if it was a warm reset or debug or scan mode)
        soc_ifc_reg_hwif_in.internal_obf_key[i].key.wel = ~pwrgood_toggle_hint || ~security_state.debug_locked || scan_mode_f;
        soc_ifc_reg_hwif_in.internal_obf_key[i].key.next = cptra_obf_key[i];
        soc_ifc_reg_hwif_in.internal_obf_key[i].key.hwclr = clear_obf_secrets;
        cptra_obf_key_reg[i] = soc_ifc_reg_hwif_out.internal_obf_key[i].key.value;
    end
    for (int i = 0; i < `CLP_OBF_UDS_DWORDS; i++) begin
        soc_ifc_reg_hwif_in.fuse_uds_seed[i].seed.hwclr = clear_obf_secrets; 
        obf_uds_seed[i] = soc_ifc_reg_hwif_out.fuse_uds_seed[i].seed.value;
    end
    for (int i = 0; i < `CLP_OBF_FE_DWORDS; i++) begin
        soc_ifc_reg_hwif_in.fuse_field_entropy[i].seed.hwclr = clear_obf_secrets;
        obf_field_entropy[i] = soc_ifc_reg_hwif_out.fuse_field_entropy[i].seed.value;
    end

    //flow status
    mailbox_flow_done = soc_ifc_reg_hwif_out.CPTRA_FLOW_STATUS.mailbox_flow_done.value;
    ready_for_fw_push = soc_ifc_reg_hwif_out.CPTRA_FLOW_STATUS.ready_for_fw.value;
    ready_for_runtime = soc_ifc_reg_hwif_out.CPTRA_FLOW_STATUS.ready_for_runtime.value;
    soc_ifc_reg_hwif_in.CPTRA_FLOW_STATUS.ready_for_fuses.next = ready_for_fuses;
    soc_ifc_reg_hwif_in.CPTRA_SECURITY_STATE.device_lifecycle.next = security_state.device_lifecycle;
    soc_ifc_reg_hwif_in.CPTRA_SECURITY_STATE.debug_locked.next     = security_state.debug_locked;
    soc_ifc_reg_hwif_in.CPTRA_SECURITY_STATE.scan_mode.next        = scan_mode_f;
    //generic wires
    for (int i = 0; i < 2; i++) begin
        generic_output_wires[i] = soc_ifc_reg_hwif_out.CPTRA_GENERIC_OUTPUT_WIRES[i].generic_wires.value;
        soc_ifc_reg_hwif_in.CPTRA_GENERIC_INPUT_WIRES[i].generic_wires.next = generic_input_wires[i];
    end

end

logic cptra_in_dbg_or_manuf_mode;

// Breakpoint value captured on a Caliptra reset deassertion (0->1 signal transition)
// BootFSM_Continue will allow the boot fsm to continue
// Security State in Debug or Manuf Mode
assign cptra_in_dbg_or_manuf_mode = ~(security_state.debug_locked) | 
                                     ((security_state.debug_locked) & (security_state.device_lifecycle == DEVICE_MANUFACTURING));

always_ff @(posedge clk or negedge cptra_rst_b) begin
    if (~cptra_rst_b) begin
        BootFSM_BrkPoint_Latched <= 0;
        BootFSM_BrkPoint_Flag <= 0;
    end
    // Breakpoint value captured on a Caliptra reset deassertion (0->1 signal transition) and is reset on BootFSM_Continue is set
    // BootFSM_Continue's reset value is zero
    else if(!BootFSM_BrkPoint_Flag) begin
        BootFSM_BrkPoint_Latched <= BootFSM_BrkPoint & cptra_in_dbg_or_manuf_mode;
        BootFSM_BrkPoint_Flag <= 1;
    end
end

// pwrgood_hint informs if the powergood toggled
always_ff @(posedge clk or negedge cptra_pwrgood) begin
     if(~cptra_pwrgood) begin
        pwrgood_toggle_hint <= 1;
     end
     // Reset the bit after warm reset deassertion has been observed
     else if(Warm_Reset_Capture_Flag) begin
        pwrgood_toggle_hint <= 0;
     end
end

always_ff @(posedge clk or negedge cptra_rst_b) begin
    if (~cptra_rst_b) begin
        Warm_Reset_Capture_Flag <= 0;
    end
    else if(!Warm_Reset_Capture_Flag) begin
        Warm_Reset_Capture_Flag <= 1;
    end
end

// PwrGood is used to decide if the warm reset toggle happened due to pwrgood or
// only due to warm reset. We also need to clear this bit when its
// FW_UPD_RESET only path
always_comb begin
    if (!Warm_Reset_Capture_Flag) begin
         soc_ifc_reg_hwif_in.CPTRA_RESET_REASON.WARM_RESET.next = ~pwrgood_toggle_hint;
    end
    else if (soc_ifc_reg_hwif_out.CPTRA_RESET_REASON.FW_UPD_RESET.value) begin
         soc_ifc_reg_hwif_in.CPTRA_RESET_REASON.WARM_RESET.next = 1'b0;
    end 
    else begin
         soc_ifc_reg_hwif_in.CPTRA_RESET_REASON.WARM_RESET.next = soc_ifc_reg_hwif_out.CPTRA_RESET_REASON.WARM_RESET.value;
    end
end


// Generate a pulse to set the interrupt bit
always_ff @(posedge soc_ifc_clk_cg or negedge cptra_noncore_rst_b) begin
    if (~cptra_noncore_rst_b) begin
        security_state_debug_locked_d <= '0;
    end
    else begin
        security_state_debug_locked_d <= security_state.debug_locked;
    end
end

always_comb security_state_debug_locked_p = security_state.debug_locked ^ security_state_debug_locked_d;

//Filtering by PAUSER
always_comb begin
    for (int i=0; i<5; i++) begin
        //once locked, can't be cleared until reset
        soc_ifc_reg_hwif_in.CPTRA_PAUSER_LOCK[i].LOCK.swwel = soc_ifc_reg_hwif_out.CPTRA_PAUSER_LOCK[i].LOCK.value;
        //lock the writes to valid user field once lock is set
        soc_ifc_reg_hwif_in.CPTRA_VALID_PAUSER[i].PAUSER.swwel = soc_ifc_reg_hwif_out.CPTRA_PAUSER_LOCK[i].LOCK.value;
        //If integrator set PAUSER values at integration time, pick it up from the define
        valid_mbox_users[i] = CLP_SET_PAUSER_INTEG[i] ? CLP_VALID_PAUSER[i][APB_USER_WIDTH-1:0] : soc_ifc_reg_hwif_out.CPTRA_VALID_PAUSER[i].PAUSER.value[APB_USER_WIDTH-1:0];
    end
end
//can't write to trng valid user after it is locked
always_comb soc_ifc_reg_hwif_in.CPTRA_TRNG_VALID_PAUSER.PAUSER.swwel = soc_ifc_reg_hwif_out.CPTRA_TRNG_PAUSER_LOCK.LOCK.value;
always_comb soc_ifc_reg_hwif_in.CPTRA_TRNG_PAUSER_LOCK.LOCK.swwel = soc_ifc_reg_hwif_out.CPTRA_TRNG_PAUSER_LOCK.LOCK.value;

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Can't write to RW-able fuses once fuse_done is set (implies the register is being locked using the fuse_wr_done)
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

always_ff @(posedge clk or negedge cptra_rst_b) begin
    if(~cptra_rst_b) begin
        fuse_wr_done_reg_write_observed <= 0;
    end
    else begin
        if(!fuse_wr_done_reg_write_observed) begin
            fuse_wr_done_reg_write_observed <= soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.swmod;
        end
    end
end

// Make the relevant fuses sticky on fuse_wr_done
always_comb begin
    for (int i=0; i<12; i++) begin
        soc_ifc_reg_hwif_in.fuse_key_manifest_pk_hash[i].hash.swwel = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
        soc_ifc_reg_hwif_in.fuse_owner_pk_hash[i].hash.swwel = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
        soc_ifc_reg_hwif_in.fuse_uds_seed[i].seed.swwel = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
    end

    for (int i=0; i<8; i++) begin
        soc_ifc_reg_hwif_in.fuse_field_entropy[i].seed.swwel = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
    end

    for (int i=0; i<24; i++) begin
      soc_ifc_reg_hwif_in.fuse_idevid_cert_attr[i].cert.swwel = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
    end

    for (int i=0; i<4; i++) begin
      soc_ifc_reg_hwif_in.fuse_idevid_manuf_hsm_id[i].hsm_id.swwel = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
    end

    // Run-time SVN can be unlocked whenever fuse_wr_done is 'reset' which happens on a warm reset
    for (int i=0; i<4; i++) begin
        soc_ifc_reg_hwif_in.fuse_runtime_svn[i].svn.swwel = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
    end
     
end

always_comb soc_ifc_reg_hwif_in.fuse_key_manifest_pk_hash_mask.mask.swwel  = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
always_comb soc_ifc_reg_hwif_in.fuse_fmc_key_manifest_svn.svn.swwel        = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
always_comb soc_ifc_reg_hwif_in.fuse_anti_rollback_disable.dis.swwel       = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
always_comb soc_ifc_reg_hwif_in.fuse_life_cycle.life_cycle.swwel           = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;

// Fuse write done can be written by SOC if it is already NOT '1. uController can only read this bit. The bit gets reset on cold reset
always_comb soc_ifc_reg_hwif_in.CPTRA_FUSE_WR_DONE.done.swwe = soc_ifc_reg_req_data.soc_req & ~soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//only allow valid users to write to TRNG
always_comb soc_ifc_reg_hwif_in.CPTRA_TRNG_STATUS.DATA_WR_DONE.swwe = soc_ifc_reg_req_data.soc_req & 
                                                            (soc_ifc_reg_req_data.user == soc_ifc_reg_hwif_out.CPTRA_TRNG_VALID_PAUSER.PAUSER.value[APB_USER_WIDTH-1:0]);
always_comb begin 
    for (int i = 0; i < 12; i++) begin
        soc_ifc_reg_hwif_in.CPTRA_TRNG_DATA[i].DATA.swwe = soc_ifc_reg_req_data.soc_req & 
                                                      (soc_ifc_reg_req_data.user == soc_ifc_reg_hwif_out.CPTRA_TRNG_VALID_PAUSER.PAUSER.value[APB_USER_WIDTH-1:0]);
    end
end

// Generate a pulse to set the interrupt bit
always_ff @(posedge soc_ifc_clk_cg or negedge cptra_noncore_rst_b) begin
    if (~cptra_noncore_rst_b) begin
        uc_mbox_data_avail_d <= '0;
    end
    else begin
        uc_mbox_data_avail_d <= uc_mbox_data_avail;
    end
end

always_comb uc_cmd_avail_p = uc_mbox_data_avail & !uc_mbox_data_avail_d;
// Pulse input to soc_ifc_reg to set the interrupt status bit and generate interrupt output (if enabled)
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset     = 1'b0; // TODO
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_inv_dev_sts.hwset      = 1'b0; // TODO should decode from APB PAUSER
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_cmd_fail_sts.hwset     = 1'b0; // TODO should this be set by write of "FAIL" to mbox_csr.status if soc_req is set? (i.e. SoC cmd execution failed)
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_bad_fuse_sts.hwset     = 1'b0; // TODO
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_iccm_blocked_sts.hwset = iccm_axs_blocked;
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_mbox_ecc_unc_sts.hwset = sram_double_ecc_error;
always_comb soc_ifc_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_avail_sts.hwset    = uc_cmd_avail_p; // TODO confirm signal correctness
always_comb soc_ifc_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_mbox_ecc_cor_sts.hwset = sram_single_ecc_error;
always_comb soc_ifc_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_debug_locked_sts.hwset = security_state_debug_locked_p; // Any transition results in interrupt
always_comb soc_ifc_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_soc_req_lock_sts.hwset = soc_req_mbox_lock;
always_comb soc_ifc_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_wdt_timer1_timeout_sts.hwset = t1_timeout_p;
always_comb soc_ifc_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_wdt_timer2_timeout_sts.hwset = t2_timeout_p && timer2_en;

always_comb soc_ifc_reg_hwif_in.internal_iccm_lock.lock.hwclr    = iccm_unlock;



logic s_cpuif_req_stall_wr_nc;
logic s_cpuif_req_stall_rd_nc;
logic s_cpuif_rd_ack_nc;
logic s_cpuif_wr_ack_nc;

soc_ifc_reg i_soc_ifc_reg (
    .clk(soc_ifc_clk_cg),
    .rst('0),
    //qualify request so no addresses alias
    .s_cpuif_req(soc_ifc_reg_req_dv & (soc_ifc_reg_req_data.addr[SOC_IFC_ADDR_W-1:SOC_IFC_REG_ADDR_WIDTH] == SOC_IFC_REG_START_ADDR[SOC_IFC_ADDR_W-1:SOC_IFC_REG_ADDR_WIDTH])),
    .s_cpuif_req_is_wr(soc_ifc_reg_req_data.write),
    .s_cpuif_addr(soc_ifc_reg_req_data.addr[SOC_IFC_REG_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data(soc_ifc_reg_req_data.wdata),
    .s_cpuif_req_stall_wr(s_cpuif_req_stall_wr_nc),
    .s_cpuif_req_stall_rd(s_cpuif_req_stall_rd_nc),
    .s_cpuif_rd_ack(s_cpuif_rd_ack_nc),
    .s_cpuif_rd_err(soc_ifc_reg_read_error),
    .s_cpuif_rd_data(soc_ifc_reg_rdata),
    .s_cpuif_wr_ack(s_cpuif_wr_ack_nc),
    .s_cpuif_wr_err(soc_ifc_reg_write_error),

    .hwif_in(soc_ifc_reg_hwif_in),
    .hwif_out(soc_ifc_reg_hwif_out)
);

assign soc_ifc_error_intr = soc_ifc_reg_hwif_out.intr_block_rf.error_global_intr_r.intr;
assign soc_ifc_notif_intr = soc_ifc_reg_hwif_out.intr_block_rf.notif_global_intr_r.intr;
assign nmi_vector = soc_ifc_reg_hwif_out.internal_nmi_vector.vec.value;
assign iccm_lock  = soc_ifc_reg_hwif_out.internal_iccm_lock.lock.value;
assign clk_gating_en = soc_ifc_reg_hwif_out.CPTRA_CLK_GATING_EN.clk_gating_en.value;
assign nmi_intr = t2_timeout && !timer2_en;             //Only issue nmi if WDT timers are cascaded and t2 times out
assign cptra_error_fatal = t2_timeout && !timer2_en;    //Only issue fatal error if WDT timers are cascaded and t2 times out

// TODO
assign cptra_error_non_fatal = 1'b0; // FIXME
assign trng_req = soc_ifc_reg_hwif_out.CPTRA_TRNG_STATUS.DATA_REQ.value;

//SHA Accelerator
sha512_acc_top #(
    .DATA_WIDTH(APB_DATA_WIDTH)
)
i_sha512_acc_top (
    .clk(soc_ifc_clk_cg),
    .rst_b(cptra_noncore_rst_b),
    .cptra_pwrgood(cptra_pwrgood),
    
    .req_dv(sha_req_dv),
    .req_hold(sha_req_hold),
    .req_data(sha_req_data),

    .rdata(sha_rdata),
    .err(sha_error),

    .sha_sram_req_dv(sha_sram_req_dv),
    .sha_sram_req_addr(sha_sram_req_addr),
    .sha_sram_resp(sha_sram_resp),
    .sha_sram_hold(sha_sram_hold),

    .error_intr(sha_error_intr),
    .notif_intr(sha_notif_intr)
);


//Mailbox
//This module contains the Caliptra Mailbox and associated control logic
//The SoC and uC can read and write to the mailbox by following the Caliptra Mailbox Protocol
mbox #(
    .DATA_W(SOC_IFC_DATA_W),
    .SIZE_KB(MBOX_SIZE_KB)
    )
i_mbox (
    .clk(soc_ifc_clk_cg),
    .rst_b(cptra_noncore_rst_b),
    .req_dv(mbox_req_dv), 
    .req_hold(mbox_req_hold),
    .dir_req_dv(mbox_dir_req_dv),
    .req_data(mbox_req_data),
    .mbox_error(mbox_error),
    .rdata(mbox_rdata),
    .sha_sram_req_dv(sha_sram_req_dv),
    .sha_sram_req_addr(sha_sram_req_addr),
    .sha_sram_resp(sha_sram_resp),
    .sha_sram_hold(sha_sram_hold),
    .mbox_sram_req(mbox_sram_req),
    .mbox_sram_resp(mbox_sram_resp),
    .sram_single_ecc_error(sram_single_ecc_error),
    .sram_double_ecc_error(sram_double_ecc_error),
    .soc_mbox_data_avail(mailbox_data_avail),
    .uc_mbox_data_avail(uc_mbox_data_avail),
    .soc_req_mbox_lock(soc_req_mbox_lock),
    .dmi_inc_rdptr(dmi_inc_rdptr),
    .dmi_reg(mbox_dmi_reg)
);

//-------------------------
//Watchdog timer
//-------------------------
assign timer1_en = soc_ifc_reg_hwif_out.CPTRA_WDT_TIMER1_EN.timer1_en;
assign timer2_en = soc_ifc_reg_hwif_out.CPTRA_WDT_TIMER2_EN.timer2_en;
assign timer1_restart = soc_ifc_reg_hwif_out.CPTRA_WDT_TIMER1_CTRL.timer1_restart;
assign timer2_restart = soc_ifc_reg_hwif_out.CPTRA_WDT_TIMER2_CTRL.timer2_restart;

always_comb begin
    for (int i = 0; i < WDT_TIMEOUT_PERIOD_NUM_DWORDS; i++) begin
        timer1_timeout_period[i] = soc_ifc_reg_hwif_out.CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[i].timer1_timeout_period.value;
        timer2_timeout_period[i] = soc_ifc_reg_hwif_out.CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[i].timer2_timeout_period.value;
    end
end

//Set WDT status reg
always_comb begin
    soc_ifc_reg_hwif_in.CPTRA_WDT_STATUS.t1_timeout.next = t1_timeout;
    soc_ifc_reg_hwif_in.CPTRA_WDT_STATUS.t2_timeout.next = t2_timeout;
end

//Generate t1 and t2 timeout interrupt pulse
always_ff @(posedge clk or negedge cptra_rst_b) begin
    if(!cptra_rst_b) begin
        t1_timeout_f <= 'b0;
        t2_timeout_f <= 'b0;
    end
    else begin
        t1_timeout_f <= t1_timeout;
        t2_timeout_f <= t2_timeout;
    end
end

always_comb t1_timeout_p = t1_timeout & ~t1_timeout_f;
always_comb t2_timeout_p = t2_timeout & ~t2_timeout_f;

//Detect falling edge on soc_ifc_error_intr to indicate that the interrupt has been serviced
always_ff @(posedge clk or negedge cptra_rst_b) begin
    if(!cptra_rst_b) begin
        soc_ifc_notif_intr_f <= 'b0;
    end
    else begin
        soc_ifc_notif_intr_f <= soc_ifc_notif_intr;
    end
end
assign wdt_notif_t1_intr_serviced = !soc_ifc_notif_intr && soc_ifc_notif_intr_f && t1_timeout;
assign wdt_notif_t2_intr_serviced = !soc_ifc_notif_intr && soc_ifc_notif_intr_f && t2_timeout && timer2_en;

//Set HW FATAL ERROR reg when timer2 times out in cascaded mode
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.error_code.we = cptra_error_fatal;
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.error_code.next = {31'b0, cptra_error_fatal}; //bit 0 will indicate if timer2 has timed out

//TIE-OFFS
always_comb begin
    soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.error_code.we = 'b0;
    soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.error_code.next = 'h0;
    soc_ifc_reg_hwif_in.CPTRA_FW_ERROR_FATAL.error_code.we = 'b0;
    soc_ifc_reg_hwif_in.CPTRA_FW_ERROR_FATAL.error_code.next = 'h0;
    soc_ifc_reg_hwif_in.CPTRA_FW_ERROR_NON_FATAL.error_code.we = 'b0;
    soc_ifc_reg_hwif_in.CPTRA_FW_ERROR_NON_FATAL.error_code.next = 'h0;
end

wdt i_wdt (
    .clk(clk),
    .cptra_rst_b(cptra_noncore_rst_b),
    .timer1_en(timer1_en),
    .timer2_en(timer2_en),
    .timer1_restart(timer1_restart),
    .timer2_restart(timer2_restart),
    .timer1_timeout_period(timer1_timeout_period),
    .timer2_timeout_period(timer2_timeout_period),
    .wdt_timer1_timeout_serviced(wdt_notif_t1_intr_serviced),
    .wdt_timer2_timeout_serviced(wdt_notif_t2_intr_serviced),
    .t1_timeout(t1_timeout),
    .t2_timeout(t2_timeout)
);
//DMI register writes
always_comb soc_ifc_reg_hwif_in.CPTRA_BOOTFSM_GO.GO.we = cptra_uncore_dmi_reg_wr_en & cptra_uncore_dmi_reg_en & 
                                                         (cptra_uncore_dmi_reg_addr == DMI_REG_BOOTFSM_GO);
always_comb soc_ifc_reg_hwif_in.CPTRA_BOOTFSM_GO.GO.next = cptra_uncore_dmi_reg_wdata[0];
always_comb soc_ifc_reg_hwif_in.CPTRA_DBG_MANUF_SERVICE_REG.DATA.we = cptra_uncore_dmi_reg_wr_en & cptra_uncore_dmi_reg_en & 
                                                                      (cptra_uncore_dmi_reg_addr == DMI_REG_CPTRA_DBG_MANUF_SERVICE_REG);
always_comb soc_ifc_reg_hwif_in.CPTRA_DBG_MANUF_SERVICE_REG.DATA.next = cptra_uncore_dmi_reg_wdata;

//DMI register read mux
always_comb cptra_uncore_dmi_reg_rdata_in = ({32{(cptra_uncore_dmi_reg_addr == DMI_REG_MBOX_DLEN)}} & mbox_dmi_reg.MBOX_DLEN) | 
                                            ({32{(cptra_uncore_dmi_reg_addr == DMI_REG_MBOX_DOUT)}} & mbox_dmi_reg.MBOX_DOUT) | 
                                            ({32{(cptra_uncore_dmi_reg_addr == DMI_REG_MBOX_STATUS)}} & mbox_dmi_reg.MBOX_STATUS) | 
                                            ({32{(cptra_uncore_dmi_reg_addr == DMI_REG_BOOT_STATUS)}} & soc_ifc_reg_hwif_out.CPTRA_BOOT_STATUS.status.value) | 
                                            ({32{(cptra_uncore_dmi_reg_addr == DMI_REG_CPTRA_HW_ERRROR_ENC)}} & soc_ifc_reg_hwif_out.CPTRA_HW_ERROR_ENC.error_code.value) | 
                                            ({32{(cptra_uncore_dmi_reg_addr == DMI_REG_CPTRA_FW_ERROR_ENC)}} & soc_ifc_reg_hwif_out.CPTRA_FW_ERROR_ENC.error_code.value) |
                                            ({32{(cptra_uncore_dmi_reg_addr == DMI_REG_BOOTFSM_GO)}} & soc_ifc_reg_hwif_out.CPTRA_BOOTFSM_GO.GO.value) |
                                            ({32{(cptra_uncore_dmi_reg_addr == DMI_REG_CPTRA_DBG_MANUF_SERVICE_REG)}} & soc_ifc_reg_hwif_out.CPTRA_DBG_MANUF_SERVICE_REG.DATA.value) ;

//Increment the read pointer when we had a dmi read to data out and no access this clock
//This assumes that reg_en goes low between read accesses
always_comb dmi_inc_rdptr = cptra_uncore_dmi_reg_dout_access_f & ~cptra_uncore_dmi_reg_en;

always_ff @(posedge clk or negedge cptra_pwrgood) begin
    if (~cptra_pwrgood) begin
        cptra_uncore_dmi_reg_rdata <= '0;
        cptra_uncore_dmi_reg_dout_access_f <= '0;
    end
    else begin
        cptra_uncore_dmi_reg_rdata <= cptra_uncore_dmi_reg_en ? cptra_uncore_dmi_reg_rdata_in : cptra_uncore_dmi_reg_rdata;
        cptra_uncore_dmi_reg_dout_access_f <= cptra_uncore_dmi_reg_en & ~cptra_uncore_dmi_reg_wr_en & (cptra_uncore_dmi_reg_addr == DMI_REG_MBOX_DOUT);
    end
end

`CALIPTRA_ASSERT_KNOWN(ERR_AHB_INF_X, {hreadyout_o,hresp_o}, soc_ifc_clk_cg, cptra_rst_b)
//this generates an NMI in the core, but we don't have a handler so it just hangs
`CALIPTRA_ASSERT_NEVER(ERR_SOC_IFC_AHB_ERR, hresp_o, soc_ifc_clk_cg, cptra_rst_b)
endmodule
