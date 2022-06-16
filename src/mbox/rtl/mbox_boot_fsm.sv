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

module mbox_boot_fsm (
    input logic clk,
    input logic cptra_pwrgood,
    input logic cptra_rst_b,

    input logic fuse_done,

    output logic cptra_uc_rst_b
);

//present and next state
boot_fsm_state_e boot_fsm_ns;
boot_fsm_state_e boot_fsm_ps;
//arcs between states
logic arc_BOOT_IDLE_BOOT_FUSE;
logic arc_BOOT_FUSE_BOOT_DONE;
//reset generation
logic propagate_reset_en;
logic fsm_synch_rst_b;

//move to fuse state when SoC signals pwrgood and de-asserts reset
always_comb arc_BOOT_IDLE_BOOT_FUSE = cptra_pwrgood && cptra_rst_b;

//move from fuse state to done when fuse done register is set
always_comb arc_BOOT_FUSE_BOOT_DONE = fuse_done;

always_comb begin
    unique casez (boot_fsm_ps)
        BOOT_IDLE: begin
            if (arc_BOOT_IDLE_BOOT_FUSE) begin
                boot_fsm_ns = BOOT_FUSE;
            end
            else begin
                boot_fsm_ns = BOOT_IDLE;
            end
        end
        BOOT_FUSE: begin
            if (arc_BOOT_FUSE_BOOT_DONE) begin
                boot_fsm_ns = BOOT_DONE;
            end
            else begin
                boot_fsm_ns = BOOT_FUSE;
            end
        end
        BOOT_DONE: begin
            boot_fsm_ns = BOOT_DONE;
        end
        default: begin
            boot_fsm_ns = BOOT_X;
        end
    endcase
end

//next state -> present state
//reset boot fsm to idle on cptra_rst_b
`CLP_RSTD_FF(boot_fsm_ps, boot_fsm_ns, clk, cptra_rst_b, BOOT_IDLE)

//uC reset generation
//propagate reset de-assertion from synchronizer when boot fsm is in BOOT_DONE state
always_comb propagate_reset_en = boot_fsm_ps == BOOT_DONE;

`CLP_EN_RST_FF(fsm_synch_rst_b, '1, clk, propagate_reset_en, cptra_rst_b)
`CLP_RST_FF(cptra_uc_rst_b, fsm_synch_rst_b, clk, cptra_rst_b)

//TODO assertions

endmodule