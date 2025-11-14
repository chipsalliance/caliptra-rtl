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
// Clock Enable Logic Truth Table
//======================================================================
// This truth table describes the clock state based on control signals.
// The logic is evaluated in priority order from top to bottom.
//
// +---------+--------------+---------+-------------------+
// | rst_b_i | debug_mode_i | clk_off | Clock State       |
// +---------+--------------+---------+-------------------+
// |    0    |      X       |    X    | ENABLED           | Reset or Debug mode
// |    1    |      1       |    X    | ENABLED           |
// +---------+--------------+---------+-------------------+
// |    1    |      0       |    1    | DISABLED          | Clock forced off
// +---------+--------------+---------+-------------------+
// |    1    |      0       |    0    | ENABLED           | Normal operation
// +---------+--------------+---------+-------------------+
//
// Priority Logic:
//   1. (!rst_b_i || debug_mode_i)  → Clock ENABLED (always running for reset/debug)
//   2. clk_off_i                   → Clock DISABLED (forced off for power savings)
//   3. Default                     → Clock ENABLED (always running)
//======================================================================

module caliptra_static_cg (
    input logic clk_i,
    input logic clk_off_i,
    input logic rst_b_i,

    input logic debug_mode_i,

    output logic clk_cg_o
);


    logic en;

    assign en = !rst_b_i || debug_mode_i ?  1'b1 :
                               clk_off_i ? 1'b0 : 1'b1;




    `CALIPTRA_ICG caliptra_icg (
        .clk(clk_i),
        .en,
        .clk_cg(clk_cg_o)

    );


endmodule
