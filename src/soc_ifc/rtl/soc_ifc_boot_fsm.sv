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
    (
    input logic clk,
    input logic cptra_pwrgood,
    input logic cptra_rst_b,
    input logic fw_update_rst,

    output logic ready_for_fuses,

    input logic fuse_done,

    output logic cptra_uc_rst_b, //Global rst that goes to all other blocks
    output logic cptra_uc_fw_rst_b, //Global + fw update rst that goes to SWeRV core only,
    output logic iccm_unlock
);

//present and next state
boot_fsm_state_e boot_fsm_ns;
boot_fsm_state_e boot_fsm_ps;
//arcs between states - global rst
logic arc_BOOT_IDLE_BOOT_FUSE;
logic arc_BOOT_FUSE_BOOT_DONE;
logic arc_BOOT_DONE_BOOT_IDLE;
//arcs for fw update rst
logic arc_BOOT_IDLE_BOOT_FWRST;
logic arc_BOOT_WAIT_BOOT_DONE;
//reset generation
logic propagate_reset_en;
logic propagate_fw_reset_en;
logic fsm_synch_rst_b;
logic fsm_synch_fw_rst_b;
logic synch_fw_rst_b;

logic fsm_iccm_unlock;
logic [$clog2(UC_FW_UPDT_RST_CYCLES)-1:0] wait_count;
logic wait_count_rst;
logic wait_count_decr;

//move to fuse state when SoC signals pwrgood and de-asserts reset
always_comb arc_BOOT_IDLE_BOOT_FUSE = cptra_pwrgood;

//move from fuse state to done when fuse done register is set
always_comb arc_BOOT_FUSE_BOOT_DONE = fuse_done;

//dummy arc for terminal state lint check
always_comb arc_BOOT_DONE_BOOT_IDLE = '0;

always_comb begin
    //move to rst state when reg bit is set to 0. This state will assert fw_rst to uc
    arc_BOOT_IDLE_BOOT_FWRST = fw_update_rst;

    //move to done state after a fixed time
    arc_BOOT_WAIT_BOOT_DONE = (wait_count == '0);
end

always_comb begin
    boot_fsm_ns = boot_fsm_ps;
    ready_for_fuses = '0;
    propagate_reset_en = '0;
    propagate_fw_reset_en = '0;
    unique casez (boot_fsm_ps)
        BOOT_IDLE: begin
            if (arc_BOOT_IDLE_BOOT_FUSE) begin
                boot_fsm_ns = BOOT_FUSE;
            end

            //reset flags in IDLE
            fsm_synch_fw_rst_b = '1;
            fsm_iccm_unlock = '0;
            wait_count_decr = 0;
            wait_count_rst = 1;
        end
        BOOT_FUSE: begin
            if (arc_BOOT_FUSE_BOOT_DONE) begin
                boot_fsm_ns = BOOT_DONE;
            end
            ready_for_fuses = 1'b1;
        end
        BOOT_FW_RST: begin
            boot_fsm_ns = BOOT_WAIT;

            //Assert core reset
            fsm_synch_fw_rst_b = '0;
            //Unlock ICCM
            fsm_iccm_unlock = '1;
            //Timer init done
            wait_count_rst = 0;
        end
        BOOT_WAIT: begin
            if (arc_BOOT_WAIT_BOOT_DONE) begin
                boot_fsm_ns = BOOT_DONE;
            end

            fsm_iccm_unlock = '0;
            //Start timer
            wait_count_decr = 1;
            wait_count_rst = 0;
        end
        BOOT_DONE: begin
            if (arc_BOOT_DONE_BOOT_IDLE) begin
                boot_fsm_ns = BOOT_IDLE;
            end
            else if (arc_BOOT_IDLE_BOOT_FWRST) begin
                boot_fsm_ns = BOOT_FW_RST;
            end

            //propagate reset de-assertion from synchronizer when boot fsm is in BOOT_DONE state
            propagate_reset_en = 1'b1;
            propagate_fw_reset_en = 1'b1;
            //Deassert core reset
            fsm_synch_fw_rst_b = '1;
            //Timer re-init
            wait_count_rst = 1;
            wait_count_decr = 0;
        end
        default: begin
            boot_fsm_ns = boot_fsm_ps;
        end
    endcase
end

//uC reset generation

//next state -> present state
//reset boot fsm to idle on cptra_rst_b
always_ff @(posedge clk or negedge cptra_rst_b) begin
    if (~cptra_rst_b) begin
        boot_fsm_ps <= BOOT_IDLE;
        fsm_synch_rst_b <= '0;
        cptra_uc_rst_b <= '0;
        cptra_uc_fw_rst_b <= '0;
        wait_count <= UC_FW_UPDT_RST_CYCLES;
        synch_fw_rst_b <= 0;
        iccm_unlock <= 0;
    end
    else begin
        boot_fsm_ps <= boot_fsm_ns;
        fsm_synch_rst_b <= propagate_reset_en ? '1 : fsm_synch_rst_b;
        synch_fw_rst_b <= propagate_fw_reset_en ? '1 : fsm_synch_fw_rst_b;
        cptra_uc_rst_b <= fsm_synch_rst_b;
        cptra_uc_fw_rst_b <= fsm_synch_rst_b && fsm_synch_fw_rst_b && synch_fw_rst_b; //uc comes out of rst only when both global and fw rsts are deasserted (through 2FF sync)

        wait_count <= wait_count_decr ? wait_count - 1
                                      : wait_count_rst ? UC_FW_UPDT_RST_CYCLES
                                                        : wait_count ;
        iccm_unlock <= fsm_iccm_unlock;
    end
end

`ASSERT_KNOWN(ERR_FSM_ARC_X, {arc_BOOT_IDLE_BOOT_FUSE,arc_BOOT_FUSE_BOOT_DONE, arc_BOOT_IDLE_BOOT_FWRST, arc_BOOT_WAIT_BOOT_DONE}, clk, cptra_rst_b)
`ASSERT_KNOWN(ERR_FSM_STATE_X, boot_fsm_ps, clk, cptra_rst_b)
`ASSERT_KNOWN(ERR_UC_RST_X, cptra_uc_rst_b, clk, cptra_rst_b)
`ASSERT_KNOWN(ERR_UC_FWRST_X, cptra_uc_fw_rst_b, clk, cptra_rst_b)
`ASSERT_NEVER(ERR_UC_RST_ASSERT_AND_BOOT_NOT_DONE, cptra_uc_rst_b && ((boot_fsm_ps == BOOT_IDLE) || (boot_fsm_ps == BOOT_FUSE)), clk, cptra_rst_b)
`ASSERT(ERR_UC_RST_ASSERT_AND_BOOT_NOT_DONE2, ~cptra_uc_rst_b || (boot_fsm_ps == BOOT_DONE) || (boot_fsm_ps == BOOT_FW_RST) || (boot_fsm_ps == BOOT_WAIT), clk, cptra_rst_b)
`ASSERT_NEVER(ERR_UC_FWRST_ASSERT_AND_BOOT_NOT_DONE, cptra_uc_fw_rst_b && (boot_fsm_ps == BOOT_WAIT), clk, cptra_rst_b)

endmodule