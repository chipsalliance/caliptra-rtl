
// -------------------------------------------------
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------
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

module fv_constraints_main
    import sha256_reg_pkg::*;
#(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    input wire           clk,
    input wire           reset_n,
    input wire           cptra_pwrgood,
    input wire           cs,
    input wire           we,
    input wire  [ADDR_WIDTH-1 : 0] address,
    input wire  [DATA_WIDTH-1 : 0] write_data,
    input  logic debugUnlock_or_scan_mode_switch,

    // Design internal signals
    input logic           core_init,
    input logic           core_next,
    input logic           core_ready,
    input logic           winternitz_mode
);

    default clocking default_clk @(posedge clk); endclocking

    // Compute if there is an ongoing init computation
    logic init_reg;
    always @ (posedge clk or negedge reset_n) begin
        if (!reset_n)
            init_reg <= 1'b0;
        else if (core_init && core_ready)
            init_reg <= 1'b1;
        else if (core_next && core_ready)
            init_reg <= 1'b0;
    end

    // There should not be a next command before an init command
    assume_init_before_next: assume property(
        !init_reg
    |->
        !core_next
    );

    // When a winternitz computation is ongoing, then no core_next is allowed
    assume_no_next_for_winternitz: assume property(
        winternitz_mode
    |->
        !core_next
    );

    // Since we cut the core digest signal we need to ensure that the output
    // of the core is stable
    assume_stable_digest_when_valid: assume property(
        ##1 sha256.core_digest_valid
    |->
        $stable(sha256.core_digest)
    );

endmodule

bind sha256 fv_constraints_main #(
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(DATA_WIDTH)
) fv_constraints_i (
  .clk(clk),
  .reset_n(reset_n),
  .cptra_pwrgood(cptra_pwrgood),
  .cs(cs),
  .we(we),
  .address(address),
  .write_data(write_data),
  .debugUnlock_or_scan_mode_switch(debugUnlock_or_scan_mode_switch),
  .core_init(sha256.core_init),
  .core_next(sha256.core_next),
  .core_ready(sha256.core_ready),
  .winternitz_mode(sha256.wntz_mode)
);
