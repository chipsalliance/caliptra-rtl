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
`include "caliptra_reg_defines.svh"

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
    input logic rdc_clk_cg,

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
    output wire              timer_intr,

    //SRAM interface
    output mbox_sram_req_t  mbox_sram_req,
    input  mbox_sram_resp_t mbox_sram_resp,

    // RV ECC Status Interface
    input rv_ecc_sts_t rv_ecc_sts,

    //Obfuscated UDS and FE
    input  logic clear_obf_secrets,
    input  logic scan_mode,
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
    output logic rdc_clk_dis,
    output logic fw_update_rst_window,

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
logic [SOC_IFC_DATA_W-1:0] mbox_dir_rdata;
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
logic [SOC_IFC_DATA_W-1:0] soc_ifc_reg_rdata_pre, soc_ifc_reg_rdata;
logic soc_ifc_reg_error, soc_ifc_reg_read_error, soc_ifc_reg_write_error;
logic soc_ifc_reg_rdata_mask;

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
logic scan_mode_f;
logic scan_mode_p;
logic sram_single_ecc_error;
logic sram_double_ecc_error;
logic soc_req_mbox_lock;
logic [1:0] generic_input_toggle;
mbox_protocol_error_t mbox_protocol_error;
logic mbox_inv_user_p;

logic iccm_unlock;
logic fw_upd_rst_executed;
logic fuse_wr_done_reg_write_observed;

logic unmasked_hw_error_fatal_write;
logic unmasked_hw_error_non_fatal_write;
logic unmasked_hw_error_non_fatal_is_set;

logic pwrgood_toggle_hint;
logic Warm_Reset_Capture_Flag;

logic BootFSM_BrkPoint_Latched;
logic BootFSM_BrkPoint_valid;
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
logic wdt_error_t1_intr_serviced;
logic wdt_error_t2_intr_serviced;

logic valid_trng_user;
logic valid_fuse_user;

boot_fsm_state_e boot_fsm_ps;

//Boot FSM
//This module contains the logic required to control the Caliptra Boot Flow
//Once the SoC has powered on Caliptra and de-asserted RESET, we can request fuses
//This FSM will de-assert reset and allow the Caliptra uC to boot after fuses are downloaded
soc_ifc_boot_fsm i_soc_ifc_boot_fsm (
    .clk(clk),
    .cptra_pwrgood(cptra_pwrgood),
    .cptra_rst_b (cptra_rst_b),
    .scan_mode(scan_mode),
    .fw_update_rst (soc_ifc_reg_hwif_out.internal_fw_update_reset.core_rst.value),
    .fw_update_rst_wait_cycles (soc_ifc_reg_hwif_out.internal_fw_update_reset_wait_cycles.wait_cycles.value),
    .ready_for_fuses(ready_for_fuses),
    .boot_fsm_ps(boot_fsm_ps),

    .fuse_done(soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value),
    .fuse_wr_done_observed(fuse_wr_done_reg_write_observed),

    .BootFSM_BrkPoint(BootFSM_BrkPoint_valid),
    .BootFSM_Continue(soc_ifc_reg_hwif_out.CPTRA_BOOTFSM_GO.GO.value),

    .cptra_noncore_rst_b(cptra_noncore_rst_b), //goes to all other blocks
    .cptra_uc_rst_b(cptra_uc_rst_b), //goes to veer core
    .iccm_unlock(iccm_unlock),
    .fw_upd_rst_executed(fw_upd_rst_executed),
    .rdc_clk_dis(rdc_clk_dis),
    .fw_update_rst_window(fw_update_rst_window)
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
    .PRESETn(cptra_noncore_rst_b),
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
    .rst_b(cptra_noncore_rst_b),
    .valid_mbox_users(valid_mbox_users),
    .valid_fuse_user(valid_fuse_user),
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
    .mbox_dir_rdata(mbox_dir_rdata),
    .mbox_error(mbox_error),
    //SHA inf
    .sha_req_dv(sha_req_dv),
    .sha_req_hold(sha_req_hold),
    .sha_req_data(sha_req_data),
    .sha_rdata(sha_rdata),
    .sha_error(sha_error),
    //FUNC reg inf
    .soc_ifc_reg_req_dv(soc_ifc_reg_req_dv), 
    .soc_ifc_reg_req_hold(soc_ifc_reg_req_hold),
    .soc_ifc_reg_req_data(soc_ifc_reg_req_data),
    .soc_ifc_reg_rdata(soc_ifc_reg_rdata),
    .soc_ifc_reg_error(soc_ifc_reg_error)

);

always_comb soc_ifc_reg_req_hold = 1'b0;


//Functional Registers and Fuses
//This module contains the functional registers maintained by the Caliptra Mailbox
//These registers are memory mapped per the Caliptra Specification
//Read and Write permissions are controlled within this block
always_comb soc_ifc_reg_error = soc_ifc_reg_read_error | soc_ifc_reg_write_error;

always_comb soc_ifc_reg_hwif_in.cptra_rst_b = cptra_noncore_rst_b;
always_comb soc_ifc_reg_hwif_in.cptra_pwrgood = cptra_pwrgood;
always_comb soc_ifc_reg_hwif_in.soc_req = soc_ifc_reg_req_data.soc_req;

`ifdef CALIPTRA_INTERNAL_TRNG
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.iTRNG_en.next = 1'b1;
`else
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.iTRNG_en.next = 1'b0;
`endif
`ifdef CALIPTRA_INTERNAL_QSPI
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.QSPI_en.next = 1'b1;
`else
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.QSPI_en.next = 1'b0;
`endif
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.I3C_en.next = 1'b0;
`ifdef CALIPTRA_INTERNAL_UART
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.UART_en.next = 1'b1;
`else
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_CONFIG.UART_en.next = 1'b0;
`endif

//SOC Stepping ID update
always_comb begin
    soc_ifc_reg_hwif_in.CPTRA_HW_REV_ID.SOC_STEPPING_ID.next = soc_ifc_reg_hwif_out.fuse_soc_stepping_id.soc_stepping_id.value[15:0];
end

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
    soc_ifc_reg_hwif_in.CPTRA_FLOW_STATUS.boot_fsm_ps.next = boot_fsm_ps;
    soc_ifc_reg_hwif_in.CPTRA_SECURITY_STATE.device_lifecycle.next = security_state.device_lifecycle;
    soc_ifc_reg_hwif_in.CPTRA_SECURITY_STATE.debug_locked.next     = security_state.debug_locked;
    soc_ifc_reg_hwif_in.CPTRA_SECURITY_STATE.scan_mode.next        = scan_mode;
    //generic wires
    for (int i = 0; i < 2; i++) begin
        generic_output_wires[i] = soc_ifc_reg_hwif_out.CPTRA_GENERIC_OUTPUT_WIRES[i].generic_wires.value;
        soc_ifc_reg_hwif_in.CPTRA_GENERIC_INPUT_WIRES[i].generic_wires.next = generic_input_wires[i];
        if (|(soc_ifc_reg_hwif_out.CPTRA_GENERIC_INPUT_WIRES[i].generic_wires.value ^ generic_input_wires[i])) begin
            generic_input_toggle[i] = 1;
        end
        else begin
            generic_input_toggle[i] = 0;
        end
    end

end

logic cptra_in_dbg_or_manuf_mode;

// Breakpoint value captured on a Caliptra reset deassertion (0->1 signal transition)
// BootFSM_Continue will allow the boot fsm to continue
// Security State in Debug or Manuf Mode
assign cptra_in_dbg_or_manuf_mode = ~(security_state.debug_locked) | 
                                     ((security_state.debug_locked) & (security_state.device_lifecycle == DEVICE_MANUFACTURING));

always_ff @(posedge rdc_clk_cg or negedge cptra_noncore_rst_b) begin
    if (~cptra_noncore_rst_b) begin
        BootFSM_BrkPoint_Latched <= 0;
        BootFSM_BrkPoint_Flag <= 0;
    end
    // Breakpoint value captured on a Caliptra reset deassertion (0->1 signal transition) and is reset on BootFSM_Continue is set
    // BootFSM_Continue's reset value is zero
    else if(!BootFSM_BrkPoint_Flag) begin
        BootFSM_BrkPoint_Latched <= BootFSM_BrkPoint;
        BootFSM_BrkPoint_Flag <= 1;
    end
end

assign BootFSM_BrkPoint_valid = BootFSM_BrkPoint_Latched & cptra_in_dbg_or_manuf_mode;

// pwrgood_hint informs if the powergood toggled
always_ff @(posedge rdc_clk_cg or negedge cptra_pwrgood) begin
     if(~cptra_pwrgood) begin
        pwrgood_toggle_hint <= 1;
     end
     // Reset the bit after warm reset deassertion has been observed
     else if(Warm_Reset_Capture_Flag) begin
        pwrgood_toggle_hint <= 0;
     end
end

always_ff @(posedge rdc_clk_cg or negedge cptra_noncore_rst_b) begin
    if (~cptra_noncore_rst_b) begin
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
always_ff @(posedge rdc_clk_cg or negedge cptra_noncore_rst_b) begin
    if (~cptra_noncore_rst_b) begin
        security_state_debug_locked_d <= '0;
    end
    else begin
        security_state_debug_locked_d <= security_state.debug_locked;
    end
end

always_comb security_state_debug_locked_p = security_state.debug_locked ^ security_state_debug_locked_d;

// Generate a pulse to set the interrupt bit
always_ff @(posedge clk or negedge cptra_noncore_rst_b) begin
    if (~cptra_noncore_rst_b) begin
        scan_mode_f <= '0;
    end
    else begin
        scan_mode_f <= scan_mode;
    end
end

always_comb scan_mode_p = scan_mode & ~scan_mode_f;

//Filtering by PAUSER
always_comb begin
    for (int i=0; i<5; i++) begin
        //once locked, can't be cleared until reset
        soc_ifc_reg_hwif_in.CPTRA_MBOX_PAUSER_LOCK[i].LOCK.swwel = soc_ifc_reg_hwif_out.CPTRA_MBOX_PAUSER_LOCK[i].LOCK.value;
        //lock the writes to valid user field once lock is set
        soc_ifc_reg_hwif_in.CPTRA_MBOX_VALID_PAUSER[i].PAUSER.swwel = soc_ifc_reg_hwif_out.CPTRA_MBOX_PAUSER_LOCK[i].LOCK.value;
        //If integrator set PAUSER values at integration time, pick it up from the define
        valid_mbox_users[i] = CPTRA_SET_MBOX_PAUSER_INTEG[i] ? CPTRA_MBOX_VALID_PAUSER[i][APB_USER_WIDTH-1:0] : 
                              soc_ifc_reg_hwif_out.CPTRA_MBOX_PAUSER_LOCK[i].LOCK.value ? 
                              soc_ifc_reg_hwif_out.CPTRA_MBOX_VALID_PAUSER[i].PAUSER.value[APB_USER_WIDTH-1:0] : CPTRA_DEF_MBOX_VALID_PAUSER;
    end
end

//can't write to trng valid user after it is locked
always_comb soc_ifc_reg_hwif_in.CPTRA_TRNG_VALID_PAUSER.PAUSER.swwel = soc_ifc_reg_hwif_out.CPTRA_TRNG_PAUSER_LOCK.LOCK.value;
always_comb soc_ifc_reg_hwif_in.CPTRA_TRNG_PAUSER_LOCK.LOCK.swwel = soc_ifc_reg_hwif_out.CPTRA_TRNG_PAUSER_LOCK.LOCK.value;

//fuse register pauser fields
always_comb soc_ifc_reg_hwif_in.CPTRA_FUSE_VALID_PAUSER.PAUSER.swwel = soc_ifc_reg_hwif_out.CPTRA_FUSE_PAUSER_LOCK.LOCK.value;
always_comb soc_ifc_reg_hwif_in.CPTRA_FUSE_PAUSER_LOCK.LOCK.swwel = soc_ifc_reg_hwif_out.CPTRA_FUSE_PAUSER_LOCK.LOCK.value;

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Can't write to RW-able fuses once fuse_done is set (implies the register is being locked using the fuse_wr_done)
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

always_ff @(posedge soc_ifc_clk_cg or negedge cptra_noncore_rst_b) begin
    if(~cptra_noncore_rst_b) begin
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
always_comb soc_ifc_reg_hwif_in.fuse_lms_verify.lms_verify.swwel           = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
always_comb soc_ifc_reg_hwif_in.fuse_lms_revocation.lms_revocation.swwel   = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
always_comb soc_ifc_reg_hwif_in.fuse_soc_stepping_id.soc_stepping_id.swwel = soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;

// Fuse write done can be written by SOC if it is already NOT '1. uController can only read this bit. The bit gets reset on cold reset
always_comb soc_ifc_reg_hwif_in.CPTRA_FUSE_WR_DONE.done.swwe = soc_ifc_reg_req_data.soc_req & ~soc_ifc_reg_hwif_out.CPTRA_FUSE_WR_DONE.done.value;
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//When TRNG_PAUSER_LOCK is one only allow valid users to write to TRNG
//If TRNG_PAUSER_LOCK is zero allow any user to write to TRNG
always_comb valid_trng_user = soc_ifc_reg_req_data.soc_req & (~soc_ifc_reg_hwif_out.CPTRA_TRNG_PAUSER_LOCK.LOCK.value | 
                             (soc_ifc_reg_req_data.user == soc_ifc_reg_hwif_out.CPTRA_TRNG_VALID_PAUSER.PAUSER.value[APB_USER_WIDTH-1:0]));

always_comb soc_ifc_reg_hwif_in.CPTRA_TRNG_STATUS.DATA_WR_DONE.swwe = valid_trng_user;

always_comb begin 
    for (int i = 0; i < 12; i++) begin
        soc_ifc_reg_hwif_in.CPTRA_TRNG_DATA[i].DATA.swwe = valid_trng_user;
        soc_ifc_reg_hwif_in.CPTRA_TRNG_DATA[i].DATA.hwclr = soc_ifc_reg_hwif_out.CPTRA_TRNG_CTRL.clear.value;
    end
end

//Clear the DATA_WR_DONE when FW clears the req bit
always_comb soc_ifc_reg_hwif_in.CPTRA_TRNG_STATUS.DATA_WR_DONE.hwclr = ~soc_ifc_reg_hwif_out.CPTRA_TRNG_STATUS.DATA_REQ.value;

generate
    if (CPTRA_SET_FUSE_PAUSER_INTEG) begin
        always_comb valid_fuse_user = soc_req_dv & (soc_req.user == CPTRA_FUSE_VALID_PAUSER);
    end else begin
        always_comb valid_fuse_user = soc_req_dv & (~soc_ifc_reg_hwif_out.CPTRA_FUSE_PAUSER_LOCK.LOCK.value | 
                                     (soc_req.user == soc_ifc_reg_hwif_out.CPTRA_FUSE_VALID_PAUSER.PAUSER.value[APB_USER_WIDTH-1:0]));
    end
endgenerate
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
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset           = 1'b0; // TODO
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_inv_dev_sts.hwset            = mbox_inv_user_p; // All invalid users, or only 'valid user but != mbox_user.user'?
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_cmd_fail_sts.hwset           = |mbox_protocol_error; // Set by any protocol error violation (mirrors the bits in CPTRA_HW_ERROR_NON_FATAL)
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_bad_fuse_sts.hwset           = 1'b0; // TODO
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_iccm_blocked_sts.hwset       = iccm_axs_blocked;
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_mbox_ecc_unc_sts.hwset       = sram_double_ecc_error;
always_comb soc_ifc_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_avail_sts.hwset          = uc_cmd_avail_p;
always_comb soc_ifc_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_mbox_ecc_cor_sts.hwset       = sram_single_ecc_error;
always_comb soc_ifc_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_debug_locked_sts.hwset       = security_state_debug_locked_p; // Any transition results in interrupt
always_comb soc_ifc_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_scan_mode_sts.hwset          = scan_mode_p; // Any transition results in interrupt
always_comb soc_ifc_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_soc_req_lock_sts.hwset       = soc_req_mbox_lock;
always_comb soc_ifc_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_gen_in_toggle_sts.hwset      = |generic_input_toggle;
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_wdt_timer1_timeout_sts.hwset = t1_timeout_p;
always_comb soc_ifc_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_wdt_timer2_timeout_sts.hwset = t2_timeout_p && timer2_en;

always_comb soc_ifc_reg_hwif_in.internal_iccm_lock.lock.hwclr    = iccm_unlock;




logic s_cpuif_req_stall_wr_nc;
logic s_cpuif_req_stall_rd_nc;
logic s_cpuif_rd_ack_nc;
logic s_cpuif_wr_ack_nc;

soc_ifc_reg i_soc_ifc_reg (
    .clk(rdc_clk_cg),
    .rst('0),
    //qualify request so no addresses alias
    .s_cpuif_req(soc_ifc_reg_req_dv & (soc_ifc_reg_req_data.addr[SOC_IFC_ADDR_W-1:SOC_IFC_REG_ADDR_WIDTH] == SOC_IFC_REG_START_ADDR[SOC_IFC_ADDR_W-1:SOC_IFC_REG_ADDR_WIDTH])),
    .s_cpuif_req_is_wr(soc_ifc_reg_req_data.write),
    .s_cpuif_addr(soc_ifc_reg_req_data.addr[SOC_IFC_REG_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data(soc_ifc_reg_req_data.wdata),
    .s_cpuif_wr_biten('1),
    .s_cpuif_req_stall_wr(s_cpuif_req_stall_wr_nc),
    .s_cpuif_req_stall_rd(s_cpuif_req_stall_rd_nc),
    .s_cpuif_rd_ack(s_cpuif_rd_ack_nc),
    .s_cpuif_rd_err(soc_ifc_reg_read_error),
    .s_cpuif_rd_data(soc_ifc_reg_rdata_pre),
    .s_cpuif_wr_ack(s_cpuif_wr_ack_nc),
    .s_cpuif_wr_err(soc_ifc_reg_write_error),

    .hwif_in(soc_ifc_reg_hwif_in),
    .hwif_out(soc_ifc_reg_hwif_out)
);

//Mask read data to TRNG DATA when TRNG PAUSER is locked and the requester isn't the correct PAUSER
always_comb begin
    soc_ifc_reg_rdata_mask = 0;
    for (int i = 0; i < 12; i++) begin
        soc_ifc_reg_rdata_mask |= soc_ifc_reg_req_data.soc_req & soc_ifc_reg_hwif_out.CPTRA_TRNG_DATA[i].DATA.swacc & 
                                  soc_ifc_reg_hwif_out.CPTRA_TRNG_PAUSER_LOCK.LOCK.value &
                                  (soc_ifc_reg_req_data.user != soc_ifc_reg_hwif_out.CPTRA_TRNG_VALID_PAUSER.PAUSER.value[APB_USER_WIDTH-1:0]);
    end
end

always_comb soc_ifc_reg_rdata = soc_ifc_reg_rdata_pre & {SOC_IFC_DATA_W{~soc_ifc_reg_rdata_mask}};

assign soc_ifc_error_intr = soc_ifc_reg_hwif_out.intr_block_rf.error_global_intr_r.intr;
assign soc_ifc_notif_intr = soc_ifc_reg_hwif_out.intr_block_rf.notif_global_intr_r.intr;
assign nmi_vector = soc_ifc_reg_hwif_out.internal_nmi_vector.vec.value;
assign iccm_lock  = soc_ifc_reg_hwif_out.internal_iccm_lock.lock.value;
assign clk_gating_en = soc_ifc_reg_hwif_out.CPTRA_CLK_GATING_EN.clk_gating_en.value;
assign nmi_intr = t2_timeout && !timer2_en;             //Only issue nmi if WDT timers are cascaded and t2 times out

// Interrupt output is set, for any enabled conditions, when a new write
// sets CPTRA_FW_ERROR_FATAL or when a HW condition occurs that sets a bit
// in CPTRA_HW_ERROR_FATAL
// Interrupt only deasserts on reset
always_ff@(posedge rdc_clk_cg or negedge cptra_noncore_rst_b) begin
    if(~cptra_noncore_rst_b) begin
        cptra_error_fatal <= 1'b0;
    end
    // FW write that SETS a new (non-masked) bit results in interrupt assertion
    else if (soc_ifc_reg_req_dv &&
             soc_ifc_reg_hwif_out.CPTRA_FW_ERROR_FATAL.error_code.swmod &&
             |(soc_ifc_reg_req_data.wdata & ~soc_ifc_reg_hwif_out.internal_fw_error_fatal_mask.mask.value & ~soc_ifc_reg_hwif_out.CPTRA_FW_ERROR_FATAL.error_code.value)) begin
        cptra_error_fatal <= 1'b1;
    end
    // HW event that SETS a new (non-masked) bit results in interrupt assertion
    else if (unmasked_hw_error_fatal_write) begin
        cptra_error_fatal <= 1'b1;
    end
    // NOTE: There is no mechanism to clear interrupt assertion by design.
    //       Platform MUST perform cptra_rst_b in order to clear cptra_error_fatal
    //       output signal, per the integration spec.
    else begin
        cptra_error_fatal <= cptra_error_fatal;
    end
end
always_ff@(posedge rdc_clk_cg or negedge cptra_noncore_rst_b) begin
    if(~cptra_noncore_rst_b) begin
        cptra_error_non_fatal <= 1'b0;
    end
    // FW write that SETS a new (non-masked) bit results in interrupt assertion
    else if (soc_ifc_reg_req_dv &&
             soc_ifc_reg_hwif_out.CPTRA_FW_ERROR_NON_FATAL.error_code.swmod &&
             |(soc_ifc_reg_req_data.wdata & ~soc_ifc_reg_hwif_out.internal_fw_error_non_fatal_mask.mask.value  & ~soc_ifc_reg_hwif_out.CPTRA_FW_ERROR_NON_FATAL.error_code.value)) begin
        cptra_error_non_fatal <= 1'b1;
    end
    // HW event that SETS a new (non-masked) bit results in interrupt assertion
    else if (unmasked_hw_error_non_fatal_write) begin
        cptra_error_non_fatal <= 1'b1;
    end
    // If FW performs a write that clears all outstanding (unmasked) ERROR_NON_FATAL events, deassert interrupt
    else if (~unmasked_hw_error_non_fatal_is_set &&
             ~|(~soc_ifc_reg_hwif_out.internal_fw_error_non_fatal_mask.mask.value & soc_ifc_reg_hwif_out.CPTRA_FW_ERROR_NON_FATAL.error_code.value)) begin
        cptra_error_non_fatal <= 1'b0;
    end
    else begin
        cptra_error_non_fatal <= cptra_error_non_fatal;
    end
end

assign trng_req = soc_ifc_reg_hwif_out.CPTRA_TRNG_STATUS.DATA_REQ.value;

// mtime always increments, but if it's being written by software the write
// value will update the register. Deasserting incr in this case prevents the
// SW write from being dropped (due to RDL compiler failing to give SW precedence properly).
assign soc_ifc_reg_hwif_in.internal_rv_mtime_l.count_l.incr = !(soc_ifc_reg_req_dv && soc_ifc_reg_hwif_out.internal_rv_mtime_l.count_l.swmod);
assign soc_ifc_reg_hwif_in.internal_rv_mtime_h.count_h.incr = !(soc_ifc_reg_req_dv && soc_ifc_reg_hwif_out.internal_rv_mtime_h.count_h.swmod) && soc_ifc_reg_hwif_out.internal_rv_mtime_l.count_l.overflow;
assign timer_intr =  {soc_ifc_reg_hwif_out.internal_rv_mtime_h.count_h.value     ,soc_ifc_reg_hwif_out.internal_rv_mtime_l.count_l.value}
                     >=
                     {soc_ifc_reg_hwif_out.internal_rv_mtimecmp_h.compare_h.value,soc_ifc_reg_hwif_out.internal_rv_mtimecmp_l.compare_l.value};

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
    .dir_rdata(mbox_dir_rdata),
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
    .mbox_protocol_error(mbox_protocol_error),
    .mbox_inv_pauser_axs(mbox_inv_user_p),
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

for (genvar i = 0; i < WDT_TIMEOUT_PERIOD_NUM_DWORDS; i++) begin
  assign timer1_timeout_period[i] = soc_ifc_reg_hwif_out.CPTRA_WDT_TIMER1_TIMEOUT_PERIOD[i].timer1_timeout_period.value;
  assign timer2_timeout_period[i] = soc_ifc_reg_hwif_out.CPTRA_WDT_TIMER2_TIMEOUT_PERIOD[i].timer2_timeout_period.value;
end

//Set WDT status reg
always_comb begin
    soc_ifc_reg_hwif_in.CPTRA_WDT_STATUS.t1_timeout.next = t1_timeout;
    soc_ifc_reg_hwif_in.CPTRA_WDT_STATUS.t2_timeout.next = t2_timeout;
end

//Generate t1 and t2 timeout interrupt pulse
always_ff @(posedge rdc_clk_cg or negedge cptra_noncore_rst_b) begin
    if(!cptra_noncore_rst_b) begin
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

// NOTE: Since error_internal_intr_r is Write-1-to-clear, capture writes to the
//       WDT interrupt bits to detect the interrupt being serviced.
//       It would be preferable to decode this from interrupt signals somehow,
//       but that would require modifying interrupt register RDL which has been
//       standardized.
always_ff @(posedge soc_ifc_clk_cg or negedge cptra_noncore_rst_b) begin
    if(!cptra_noncore_rst_b) begin
        wdt_error_t1_intr_serviced <= 1'b0;
        wdt_error_t2_intr_serviced <= 1'b0;
    end
    else if (soc_ifc_reg_req_dv && soc_ifc_reg_req_data.write && (soc_ifc_reg_req_data.addr[SOC_IFC_REG_ADDR_WIDTH-1:0] == `SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R)) begin
        wdt_error_t1_intr_serviced <= soc_ifc_reg_req_data.wdata[`SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_LOW] && t1_timeout;
        wdt_error_t2_intr_serviced <= soc_ifc_reg_req_data.wdata[`SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_LOW] && t2_timeout && timer2_en;
    end
    else begin
        wdt_error_t1_intr_serviced <= 1'b0;
        wdt_error_t2_intr_serviced <= 1'b0;
    end
end

wdt i_wdt (
    .clk(rdc_clk_cg),
    .cptra_rst_b(cptra_noncore_rst_b),
    .timer1_en(timer1_en),
    .timer2_en(timer2_en),
    .timer1_restart(timer1_restart),
    .timer2_restart(timer2_restart),
    .timer1_timeout_period(timer1_timeout_period),
    .timer2_timeout_period(timer2_timeout_period),
    .wdt_timer1_timeout_serviced(wdt_error_t1_intr_serviced),
    .wdt_timer2_timeout_serviced(wdt_error_t2_intr_serviced),
    .t1_timeout(t1_timeout),
    .t2_timeout(t2_timeout)
);

////////////////////////////////////////////////////////
// Write-enables for CPTRA_HW_ERROR_FATAL and CPTRA_HW_ERROR_NON_FATAL
// Also calculate whether or not an unmasked event is being set, so we can
// trigger the SOC interrupt signal
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.iccm_ecc_unc.we = rv_ecc_sts.cptra_iccm_ecc_double_error & ~fw_update_rst_window;
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.dccm_ecc_unc.we = rv_ecc_sts.cptra_dccm_ecc_double_error & ~fw_update_rst_window;
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.nmi_pin     .we = nmi_intr;
// Using we+next instead of hwset allows us to encode the reserved fields in some fashion
// other than bit-hot in the future, if needed (e.g. we need to encode > 32 FATAL events)
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.iccm_ecc_unc.next = 1'b1;
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.dccm_ecc_unc.next = 1'b1;
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.nmi_pin     .next = 1'b1;
// Flag the write even if the field being written to is already set to 1 - this is a new occurrence of the error and should trigger a new interrupt
always_comb unmasked_hw_error_fatal_write = (soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.iccm_ecc_unc.we && ~soc_ifc_reg_hwif_out.internal_hw_error_fatal_mask.mask_iccm_ecc_unc.value && |soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.iccm_ecc_unc.next) ||
                                            (soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.dccm_ecc_unc.we && ~soc_ifc_reg_hwif_out.internal_hw_error_fatal_mask.mask_dccm_ecc_unc.value && |soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.dccm_ecc_unc.next) ||
                                            (soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.nmi_pin     .we && ~soc_ifc_reg_hwif_out.internal_hw_error_fatal_mask.mask_nmi_pin     .value && |soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_FATAL.nmi_pin     .next);

always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.mbox_prot_no_lock.we = mbox_protocol_error.axs_without_lock;
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.mbox_prot_ooo    .we = mbox_protocol_error.axs_incorrect_order;
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.mbox_ecc_unc     .we = sram_double_ecc_error;
// Using we+next instead of hwset allows us to encode the reserved fields in some fashion
// other than bit-hot in the future, if needed (e.g. we need to encode > 32 NON-FATAL events)
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.mbox_prot_no_lock.next = 1'b1;
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.mbox_prot_ooo    .next = 1'b1;
always_comb soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.mbox_ecc_unc     .next = 1'b1;
// Flag the write even if the field being written to is already set to 1 - this is a new occurrence of the error and should trigger a new interrupt
always_comb unmasked_hw_error_non_fatal_write = (soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.mbox_prot_no_lock.we && ~soc_ifc_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox_prot_no_lock.value && |soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.mbox_prot_no_lock.next) ||
                                                (soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.mbox_prot_ooo    .we && ~soc_ifc_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox_prot_ooo    .value && |soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.mbox_prot_ooo    .next) ||
                                                (soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.mbox_ecc_unc     .we && ~soc_ifc_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox_ecc_unc     .value && |soc_ifc_reg_hwif_in.CPTRA_HW_ERROR_NON_FATAL.mbox_ecc_unc     .next);
always_comb unmasked_hw_error_non_fatal_is_set = (soc_ifc_reg_hwif_out.CPTRA_HW_ERROR_NON_FATAL.mbox_prot_no_lock.value && ~soc_ifc_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox_prot_no_lock.value) ||
                                                 (soc_ifc_reg_hwif_out.CPTRA_HW_ERROR_NON_FATAL.mbox_prot_ooo    .value && ~soc_ifc_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox_prot_ooo    .value) ||
                                                 (soc_ifc_reg_hwif_out.CPTRA_HW_ERROR_NON_FATAL.mbox_ecc_unc     .value && ~soc_ifc_reg_hwif_out.internal_hw_error_non_fatal_mask.mask_mbox_ecc_unc     .value);

//TIE-OFFS
always_comb begin
    soc_ifc_reg_hwif_in.CPTRA_FW_ERROR_FATAL.error_code.we = 'b0;
    soc_ifc_reg_hwif_in.CPTRA_FW_ERROR_FATAL.error_code.next = 'h0;
    soc_ifc_reg_hwif_in.CPTRA_FW_ERROR_NON_FATAL.error_code.we = 'b0;
    soc_ifc_reg_hwif_in.CPTRA_FW_ERROR_NON_FATAL.error_code.next = 'h0;
end

//DMI register writes
always_comb soc_ifc_reg_hwif_in.CPTRA_BOOTFSM_GO.GO.we = cptra_uncore_dmi_reg_wr_en & cptra_uncore_dmi_reg_en & 
                                                         (cptra_uncore_dmi_reg_addr == DMI_REG_BOOTFSM_GO);
always_comb soc_ifc_reg_hwif_in.CPTRA_BOOTFSM_GO.GO.next = cptra_uncore_dmi_reg_wdata[0];
always_comb soc_ifc_reg_hwif_in.CPTRA_DBG_MANUF_SERVICE_REG.DATA.we = cptra_uncore_dmi_reg_wr_en & cptra_uncore_dmi_reg_en & 
                                                                      (cptra_uncore_dmi_reg_addr == DMI_REG_CPTRA_DBG_MANUF_SERVICE_REG);
always_comb soc_ifc_reg_hwif_in.CPTRA_DBG_MANUF_SERVICE_REG.DATA.next = cptra_uncore_dmi_reg_wdata;

//DMI register read mux
always_comb cptra_uncore_dmi_reg_rdata_in = ({32{(cptra_uncore_dmi_reg_addr == DMI_REG_MBOX_DLEN)}} & {31'b0, mbox_dmi_reg.MBOX_DLEN}) | 
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

always_ff @(posedge rdc_clk_cg or negedge cptra_pwrgood) begin
    if (~cptra_pwrgood) begin
        cptra_uncore_dmi_reg_rdata <= '0;
        cptra_uncore_dmi_reg_dout_access_f <= '0;
    end
    else begin
        cptra_uncore_dmi_reg_rdata <= cptra_uncore_dmi_reg_en ? cptra_uncore_dmi_reg_rdata_in : cptra_uncore_dmi_reg_rdata;
        cptra_uncore_dmi_reg_dout_access_f <= cptra_uncore_dmi_reg_en & ~cptra_uncore_dmi_reg_wr_en & (cptra_uncore_dmi_reg_addr == DMI_REG_MBOX_DOUT);
    end
end

`CALIPTRA_ASSERT_KNOWN(ERR_AHB_INF_X, {hreadyout_o,hresp_o}, clk, !cptra_noncore_rst_b)
//this generates an NMI in the core, but we don't have a handler so it just hangs
`CALIPTRA_ASSERT_NEVER(ERR_SOC_IFC_AHB_ERR, hresp_o, clk, !cptra_noncore_rst_b)
endmodule
