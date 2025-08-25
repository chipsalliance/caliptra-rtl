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

module soc_ifc_boot_fsm 
    import soc_ifc_pkg::*;
    import soc_ifc_reg_pkg::*;
    (
    input logic clk,
    input logic cptra_pwrgood,
    input logic cptra_rst_b,
    input logic scan_mode,
    input logic fw_update_rst,
    input logic [7:0] fw_update_rst_wait_cycles,

    // Debug wires to Stop the BootFSM from bringing uC out of reset and continue on a write
    input logic BootFSM_BrkPoint,
    input logic BootFSM_Continue,

    output logic ready_for_fuses,
    output boot_fsm_state_e boot_fsm_ps,

    input logic fuse_done,
    input logic fuse_wr_done_observed,

    output logic cptra_noncore_rst_b, //Global rst that goes to all other blocks
    output logic cptra_uc_rst_b, //Global + fw update rst that goes to VeeR core only,
    output logic iccm_unlock,
    output logic fw_upd_rst_executed,
    output logic rdc_clk_dis,
    output logic fw_update_rst_window
);

`include "caliptra_sva.svh"

logic cptra_uc_rst_b_nq;
logic cptra_noncore_rst_b_nq;

//present and next state
boot_fsm_state_e boot_fsm_ns;
//arcs between states - global rst
logic arc_BOOT_IDLE_BOOT_FUSE;
logic arc_BOOT_FUSE_BOOT_DONE;
logic arc_BOOT_FUSE_BOOT_WAIT;
logic arc_BOOT_DONE_BOOT_IDLE;
//arcs for fw update rst
logic arc_BOOT_DONE_BOOT_FWRST;
logic arc_BOOT_FWRST_BOOT_WAIT;
logic arc_BOOT_WAIT_BOOT_DONE;
logic arc_IDLE;
//reset generation
logic fsm_synch_noncore_rst_b;
logic synch_noncore_rst_b;
logic fsm_synch_uc_rst_b;
logic synch_uc_rst_b;

logic fsm_iccm_unlock;
logic [7:0] wait_count;
logic wait_count_rst;
logic wait_count_decr;

logic cptra_rst_window;
logic cptra_rst_window_sync, cptra_rst_window_sync_f, cptra_rst_window_sync_2f;

//move to fuse state when SoC de-asserts reset
always_comb arc_BOOT_IDLE_BOOT_FUSE = (boot_fsm_ps == BOOT_IDLE) & ~cptra_rst_window_sync & ~cptra_rst_window_sync_f & ~cptra_rst_window_sync_2f;
//move from fuse state to done when fuse done register is set OR
//if it was already set (since its locked across warm reset), that the write was observed from SOC
always_comb arc_BOOT_FUSE_BOOT_DONE = fuse_done & fuse_wr_done_observed;

// Hold the bootFSM from bringing uC out of reset if the breakpoint is set after fuse writes are done
always_comb arc_BOOT_FUSE_BOOT_WAIT = BootFSM_BrkPoint;

//dummy arc for terminal state lint check
always_comb arc_BOOT_DONE_BOOT_IDLE = '0;

always_comb arc_IDLE = cptra_rst_window_sync;

//Masks combo paths from uc reset flops into other reset domains
always_comb fw_update_rst_window = (boot_fsm_ps == BOOT_FW_RST) |
                                   ((boot_fsm_ps == BOOT_WAIT) & (wait_count != 0));
//clock gate all flops on warm reset to prevent RDC metastability issues
//cover 2 clocks after synchronized reset assertion (cptra_rst_window_sync) to handle bootfsm transitions
always_comb rdc_clk_dis = cptra_rst_window_sync | cptra_rst_window_sync_f | cptra_rst_window_sync_2f;

//move to rst state when reg bit is set to 1. This state will assert fw_rst to uc
always_comb arc_BOOT_DONE_BOOT_FWRST = (boot_fsm_ps == BOOT_DONE) & fw_update_rst;
//advance to boot wait when reset starts to propagate
always_comb arc_BOOT_FWRST_BOOT_WAIT = ~synch_uc_rst_b;

// Move to BOOT_DONE state when
// a fixed time is met AND
// if the BootFSM breakpoint is asserted and the BootFSM continue is not set, stay put in WAIT state
always_comb arc_BOOT_WAIT_BOOT_DONE = (wait_count == '0) & ~(BootFSM_BrkPoint & ~BootFSM_Continue);


always_comb begin
    boot_fsm_ns = boot_fsm_ps;
    fw_upd_rst_executed = '0;
    fsm_synch_noncore_rst_b = '0;
    fsm_iccm_unlock = '0;
    fsm_synch_uc_rst_b = '0;
    wait_count_decr = 0;
    wait_count_rst = 0;

    unique case (boot_fsm_ps) inside
        BOOT_IDLE: begin
            if (arc_BOOT_IDLE_BOOT_FUSE) begin
                boot_fsm_ns = BOOT_FUSE;
            end
            //reset flags in IDLE
            // NOTE: FSM is only in BOOT_IDLE when system reset is asserted, so
            //       also assert the internal core/noncore resets
            fsm_synch_uc_rst_b = '0;
            fsm_synch_noncore_rst_b = '0;
            fsm_iccm_unlock = '0;
            wait_count_decr = 0;
            wait_count_rst = 0;
        end
        BOOT_FUSE: begin
            if (arc_BOOT_FUSE_BOOT_DONE) begin
                if (arc_BOOT_FUSE_BOOT_WAIT) begin
                    boot_fsm_ns = BOOT_WAIT;
                end
                else begin
                    boot_fsm_ns = BOOT_DONE;
                end
            end

            //reset flags
            fsm_synch_uc_rst_b = '0;
            fsm_synch_noncore_rst_b = '1;
            fsm_iccm_unlock = '0;
            wait_count_decr = 0;
            wait_count_rst = 0;
        end
        BOOT_FW_RST: begin
            if (arc_BOOT_FWRST_BOOT_WAIT) boot_fsm_ns = BOOT_WAIT;

            //Assert core reset
            fsm_synch_uc_rst_b = '0;
            fsm_synch_noncore_rst_b = '1;
            //Keep ICCM locked until end of fw rst
            fsm_iccm_unlock = '0;
            //Start timer
            wait_count_decr = 0;
            wait_count_rst = 1;
        end
        BOOT_WAIT: begin
            if (arc_BOOT_WAIT_BOOT_DONE) begin
                boot_fsm_ns = BOOT_DONE;
                fsm_iccm_unlock = 1'b1;
            end
            // Unlock ICCM at the end of reset flow to avoid a potential
            // race-condition attack against ICCM
            else begin
                fsm_iccm_unlock = '0;
            end
            fsm_synch_uc_rst_b = '0;
            fsm_synch_noncore_rst_b = '1;
            wait_count_decr = 1;
            wait_count_rst = 0;
        end
        BOOT_DONE: begin
            if (arc_BOOT_DONE_BOOT_IDLE) begin
                boot_fsm_ns = BOOT_IDLE;
            end
            else if (arc_BOOT_DONE_BOOT_FWRST) begin
                boot_fsm_ns = BOOT_FW_RST;
                // Even a single FW_UPD_RESET flow will assert this bit and it will never be deasserted.
                // This is fine because if there is WARM or COLD RESET, this register bit gets reset.
                // Implying the only time this bit can be observed as '1 is because the reset is happening due to a FW UPD RESET
                // If that assumption changes, by adding a new reset state, then this bit needs to change
                fw_upd_rst_executed = 1;
            end

            //Deassert reset
            fsm_synch_uc_rst_b = '1;
            fsm_synch_noncore_rst_b = '1;
            fsm_iccm_unlock = '0;
            //Timer re-init
            wait_count_rst = 0;
            wait_count_decr = 0;
        end
        default: begin
            boot_fsm_ns = boot_fsm_ps;
            fw_upd_rst_executed = '0;
            fsm_synch_noncore_rst_b = '0;
            fsm_iccm_unlock = '0;
            fsm_synch_uc_rst_b = '0;
            wait_count_decr = 0;
            wait_count_rst = 0;
        end
    endcase
end

//next state -> present state
//reset boot fsm to idle on cptra_pwrgood
always_ff @(posedge clk or negedge cptra_pwrgood) begin
    if (~cptra_pwrgood) begin
        boot_fsm_ps <= BOOT_IDLE;
        synch_noncore_rst_b <= '0;
        synch_uc_rst_b <= 0;
        cptra_noncore_rst_b_nq <= '0;
        cptra_uc_rst_b_nq <= '0;

        cptra_rst_window_sync_f <= '1;
        cptra_rst_window_sync_2f <= '1;
    end
    else begin
        boot_fsm_ps <= arc_IDLE ? BOOT_IDLE : boot_fsm_ns;
        synch_noncore_rst_b <= fsm_synch_noncore_rst_b;
        synch_uc_rst_b <= fsm_synch_uc_rst_b;
        cptra_noncore_rst_b_nq <= synch_noncore_rst_b;
        cptra_uc_rst_b_nq <= synch_noncore_rst_b && synch_uc_rst_b; //uc comes out of rst only when both global and fw rsts are deasserted (through 2FF sync)

        cptra_rst_window_sync_f <= cptra_rst_window_sync;
        cptra_rst_window_sync_2f <= cptra_rst_window_sync_f;
    end
end

//protect resets during scan mode
//utilize warm reset pin to drive reset during scan mode
assign cptra_noncore_rst_b = scan_mode ? cptra_rst_b : cptra_noncore_rst_b_nq;
assign cptra_uc_rst_b = scan_mode ? cptra_rst_b : cptra_uc_rst_b_nq;

//uC reset generation
always_ff @(posedge clk or negedge cptra_rst_b) begin
    if (~cptra_rst_b) begin
        cptra_rst_window <= '1;
    end
    else begin
        cptra_rst_window <= 0;
    end
end

// Ready for fuses output signal
always_ff @(posedge clk or negedge cptra_noncore_rst_b) begin
    if (~cptra_noncore_rst_b) begin
        ready_for_fuses <= 1'b0;
        wait_count <= '0;
        iccm_unlock <= 0;
    end
    else begin
        ready_for_fuses <= (boot_fsm_ps == BOOT_FUSE) && !fuse_wr_done_observed;
        wait_count <= (wait_count_decr && (wait_count != '0)) ? wait_count - 1 :
                                               wait_count_rst ? fw_update_rst_wait_cycles :
                                                                wait_count ;
        iccm_unlock <= fsm_iccm_unlock;
    end
end

caliptra_2ff_sync #(.WIDTH(1), .RST_VAL('d1)) i_rst_window_sync (.clk(clk), .rst_b(cptra_pwrgood), .din(cptra_rst_window), .dout(cptra_rst_window_sync));

//Check for x prop
`CALIPTRA_ASSERT_KNOWN(ERR_FSM_ARC_X, {arc_BOOT_FUSE_BOOT_DONE, arc_BOOT_DONE_BOOT_FWRST, arc_BOOT_WAIT_BOOT_DONE}, clk, !cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(ERR_FSM_STATE_X, boot_fsm_ps, clk, !cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(ERR_UC_RST_X, cptra_noncore_rst_b, clk, !cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(ERR_UC_FWRST_X, cptra_uc_rst_b, clk, !cptra_rst_b)

//Reset got asserted, but cptra rst window wasn't asserted to protect RDC
`CALIPTRA_ASSERT_NEVER(ERR_RST_ASSERT_NO_WINDOW, $fell(cptra_noncore_rst_b) && ~rdc_clk_dis, clk, !(cptra_pwrgood && ~scan_mode))
`CALIPTRA_ASSERT_NEVER(ERR_UC_RST_ASSERT_NO_WINDOW, $fell(cptra_uc_rst_b) && ~(fw_update_rst_window || rdc_clk_dis), clk, !(cptra_pwrgood && ~scan_mode))

endmodule
