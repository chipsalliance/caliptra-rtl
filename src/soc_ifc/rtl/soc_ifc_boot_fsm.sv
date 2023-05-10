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
    input logic fw_update_rst,
    input logic [7:0] fw_update_rst_wait_cycles,

    // Debug wires to Stop the BootFSM from bringing uC out of reset and continue on a write
    input logic BootFSM_BrkPoint,
    input logic BootFSM_Continue,

    output logic ready_for_fuses,

    input logic fuse_done,
    input logic fuse_wr_done_observed,

    output logic cptra_noncore_rst_b, //Global rst that goes to all other blocks
    output logic cptra_uc_rst_b, //Global + fw update rst that goes to VeeR core only,
    output logic iccm_unlock,
    output logic fw_upd_rst_executed
);

`include "caliptra_sva.svh"

//present and next state
boot_fsm_state_e boot_fsm_ns;
boot_fsm_state_e boot_fsm_ps;
//arcs between states - global rst
logic arc_BOOT_FUSE_BOOT_DONE;
logic arc_BOOT_FUSE_BOOT_WAIT;
logic arc_BOOT_DONE_BOOT_IDLE;
//arcs for fw update rst
logic arc_BOOT_DONE_BOOT_FWRST;
logic arc_BOOT_WAIT_BOOT_DONE;
//reset generation
logic propagate_reset_en;
logic propagate_uc_reset_en;
logic fsm_synch_noncore_rst_b;
logic fsm_synch_uc_rst_b;
logic synch_uc_rst_b;

logic fsm_iccm_unlock;
logic [7:0] wait_count;
logic wait_count_rst;
logic wait_count_decr;

//move to fuse state when SoC de-asserts reset

//move from fuse state to done when fuse done register is set OR
//if it was already set (since its locked across warm reset), that the write was observed from SOC
always_comb arc_BOOT_FUSE_BOOT_DONE = fuse_done & fuse_wr_done_observed;

// Hold the bootFSM from bringing uC out of reset if the breakpoint is set after fuse writes are done
always_comb arc_BOOT_FUSE_BOOT_WAIT = BootFSM_BrkPoint;

//dummy arc for terminal state lint check
always_comb arc_BOOT_DONE_BOOT_IDLE = '0;


always_comb begin
    //move to rst state when reg bit is set to 1. This state will assert fw_rst to uc
    arc_BOOT_DONE_BOOT_FWRST = fw_update_rst;

    // TODO: Capture BootFSM_BrkPoint only at the point of cold or warm reset exit
    // Move to BOOT_DONE state when
          // a fixed time is met AND
          // if the BootFSM breakpoint is asserted and the BootFSM continue is not set, stay put in WAIT state
    arc_BOOT_WAIT_BOOT_DONE = (wait_count == '0) & ~(BootFSM_BrkPoint & ~BootFSM_Continue);
end

always_comb begin
    boot_fsm_ns = boot_fsm_ps;
    ready_for_fuses = '0;
    propagate_reset_en = '0;
    propagate_uc_reset_en = '0;
    fw_upd_rst_executed = 0;

    unique casez (boot_fsm_ps)
        BOOT_IDLE: begin
            boot_fsm_ns = BOOT_FUSE;

            //reset flags in IDLE
            // NOTE: FSM is only in BOOT_IDLE when system reset is asserted, so
            //       also assert the internal core/noncore resets
            fsm_synch_uc_rst_b = '0;
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
            ready_for_fuses = 1'b1;

            //reset flags
            fsm_synch_uc_rst_b = '0;
            fsm_iccm_unlock = '0;
            wait_count_decr = 0;
            wait_count_rst = 0;
        end
        BOOT_FW_RST: begin
            boot_fsm_ns = BOOT_WAIT;

            //Assert core reset
            fsm_synch_uc_rst_b = '0;
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

            //propagate reset de-assertion from synchronizer when boot fsm is in BOOT_DONE state
            propagate_reset_en = 1'b1;
            propagate_uc_reset_en = 1'b1;
            //Deassert core reset
            fsm_synch_uc_rst_b = '1;
            fsm_iccm_unlock = '0;
            //Timer re-init
            wait_count_rst = 0;
            wait_count_decr = 0;
        end
        default: begin
            boot_fsm_ns = boot_fsm_ps;
            fsm_synch_uc_rst_b = '1;
            fsm_iccm_unlock = '0;
            wait_count_decr = 0;
            wait_count_rst = 0;
        end
    endcase
end

//uC reset generation

//next state -> present state
//reset boot fsm to idle on cptra_rst_b
always_ff @(posedge clk or negedge cptra_rst_b) begin
    if (~cptra_rst_b) begin
        boot_fsm_ps <= BOOT_IDLE;
        fsm_synch_noncore_rst_b <= '0;
        cptra_noncore_rst_b <= '0;
        cptra_uc_rst_b <= '0;
        wait_count <= '0;
        synch_uc_rst_b <= 0;
        iccm_unlock <= 0;
    end
    else begin
        boot_fsm_ps <= boot_fsm_ns;
        fsm_synch_noncore_rst_b <= propagate_reset_en ? '1 : fsm_synch_noncore_rst_b;
        synch_uc_rst_b <= propagate_uc_reset_en ? '1 : fsm_synch_uc_rst_b;
        cptra_noncore_rst_b <= fsm_synch_noncore_rst_b;
        cptra_uc_rst_b <= fsm_synch_noncore_rst_b && fsm_synch_uc_rst_b && synch_uc_rst_b; //uc comes out of rst only when both global and fw rsts are deasserted (through 2FF sync)

        wait_count <= (wait_count_decr && (wait_count != '0)) ? wait_count - 1
                                      : wait_count_rst ? fw_update_rst_wait_cycles
                                                        : wait_count ;
        iccm_unlock <= fsm_iccm_unlock;
    end
end

`CALIPTRA_ASSERT_KNOWN(ERR_FSM_ARC_X, {arc_BOOT_FUSE_BOOT_DONE, arc_BOOT_DONE_BOOT_FWRST, arc_BOOT_WAIT_BOOT_DONE}, clk, cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(ERR_FSM_STATE_X, boot_fsm_ps, clk, cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(ERR_UC_RST_X, cptra_noncore_rst_b, clk, cptra_rst_b)
`CALIPTRA_ASSERT_KNOWN(ERR_UC_FWRST_X, cptra_uc_rst_b, clk, cptra_rst_b)
`CALIPTRA_ASSERT_NEVER(ERR_UC_RST_ASSERT_AND_BOOT_NOT_DONE, cptra_noncore_rst_b && ((boot_fsm_ps == BOOT_IDLE) || (boot_fsm_ps == BOOT_FUSE)), clk, cptra_rst_b)
`CALIPTRA_ASSERT(ERR_UC_RST_ASSERT_AND_BOOT_NOT_DONE2, ~cptra_noncore_rst_b || (boot_fsm_ps == BOOT_DONE) || (boot_fsm_ps == BOOT_FW_RST) || (boot_fsm_ps == BOOT_WAIT), clk, cptra_rst_b)
`CALIPTRA_ASSERT_NEVER(ERR_UC_FWRST_ASSERT_AND_BOOT_NOT_DONE, cptra_uc_rst_b && (boot_fsm_ps == BOOT_WAIT), clk, cptra_rst_b)

endmodule
