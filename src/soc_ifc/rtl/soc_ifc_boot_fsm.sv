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

    output logic ready_for_fuses,

    input logic fuse_done,

    output logic cptra_uc_rst_b
);

//present and next state
boot_fsm_state_e boot_fsm_ns;
boot_fsm_state_e boot_fsm_ps;
//arcs between states
logic arc_BOOT_IDLE_BOOT_FUSE;
logic arc_BOOT_FUSE_BOOT_DONE;
logic arc_BOOT_DONE_BOOT_IDLE;
//reset generation
logic propagate_reset_en;
logic fsm_synch_rst_b;

//move to fuse state when SoC signals pwrgood and de-asserts reset
always_comb arc_BOOT_IDLE_BOOT_FUSE = cptra_pwrgood;

//move from fuse state to done when fuse done register is set
always_comb arc_BOOT_FUSE_BOOT_DONE = fuse_done;

//dummy arc for terminal state lint check
always_comb arc_BOOT_DONE_BOOT_IDLE = '0;

always_comb begin
    boot_fsm_ns = boot_fsm_ps;
    ready_for_fuses = '0;
    propagate_reset_en = '0;
    unique casez (boot_fsm_ps)
        BOOT_IDLE: begin
            if (arc_BOOT_IDLE_BOOT_FUSE) begin
                boot_fsm_ns = BOOT_FUSE;
            end
        end
        BOOT_FUSE: begin
            if (arc_BOOT_FUSE_BOOT_DONE) begin
                boot_fsm_ns = BOOT_DONE;
            end
            ready_for_fuses = 1'b1;
        end
        BOOT_DONE: begin
            if (arc_BOOT_DONE_BOOT_IDLE) begin
                boot_fsm_ns = BOOT_IDLE;
            end
            //propagate reset de-assertion from synchronizer when boot fsm is in BOOT_DONE state
            propagate_reset_en = 1'b1;
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
    end
    else begin
        boot_fsm_ps <= boot_fsm_ns;
        fsm_synch_rst_b <= propagate_reset_en ? '1 : fsm_synch_rst_b;
        cptra_uc_rst_b <= fsm_synch_rst_b;
    end
end

`ASSERT_KNOWN(ERR_FSM_ARC_X, {arc_BOOT_IDLE_BOOT_FUSE,arc_BOOT_FUSE_BOOT_DONE}, clk, cptra_rst_b)
`ASSERT_KNOWN(ERR_FSM_STATE_X, boot_fsm_ps, clk, cptra_rst_b)
`ASSERT_KNOWN(ERR_UC_RST_X, cptra_uc_rst_b, clk, cptra_rst_b)
`ASSERT_NEVER(ERR_UC_RST_ASSERT_AND_BOOT_NOT_DONE, cptra_uc_rst_b && (boot_fsm_ps != BOOT_DONE), clk, cptra_rst_b)
`ASSERT(ERR_UC_RST_ASSERT_AND_BOOT_NOT_DONE2, ~cptra_uc_rst_b || (boot_fsm_ps == BOOT_DONE), clk, cptra_rst_b)

endmodule