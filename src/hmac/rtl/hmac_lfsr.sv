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
//======================================================================
//
// hmac_lfsr.sv
// ------
// 32-bit LFSR
// 
//======================================================================

module hmac_lfsr
#(
   parameter                    REG_SIZE  = 32
)
(
  // Clock and reset.
  input wire                        clk,
  input wire                        reset_n,
  input wire                        zeroize,

  //Control
  input wire                        en,

  //Data
  input wire   [REG_SIZE-1 : 0]     seed,
  output wire  [REG_SIZE-1 : 0]     rnd
);

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
   reg [REG_SIZE-1 : 0]    rnd_reg;
   reg [REG_SIZE-1 : 0]    rnd_next;

   logic                   feedback;
   logic                   lockup;
   logic [REG_SIZE-1 : 0]  counter_reg;
   logic [REG_SIZE-1 : 0]  counter_next;

  //----------------------------------------------------------------
  // reg_update
  // Update functionality for all registers in the core.
  //----------------------------------------------------------------
   
   // TAPs are: 32,22,2,1 based on Xilinx doc: https://docs.xilinx.com/v/u/en-US/xapp052
   always_comb feedback = rnd_reg[31] ^ rnd_reg[21] ^ rnd_reg[1] ^ rnd_reg[0];

   always_comb rnd_next = {rnd_reg[REG_SIZE-2 : 0], !feedback};

   always_ff @ (posedge clk or negedge reset_n) 
   begin
      if (!reset_n)
         rnd_reg <= '0;
      else if (zeroize)
         rnd_reg <= counter_reg;
      else if (en)
         rnd_reg <= seed;
      else if (lockup)
         rnd_reg <= counter_reg;
      else
         rnd_reg <= rnd_next;
   end

   always_comb counter_next = counter_reg + 1;

   always_ff @(posedge clk or negedge reset_n) 
    begin : counter_reg_update
        if (!reset_n)
            counter_reg       <= '0;
        else if (&counter_next)
            counter_reg       <= '0;
         else
            counter_reg       <= counter_next;
    end // counter_reg_update

   // lockup condition is all-one
   assign lockup = &rnd_reg;

   assign rnd = rnd_reg;

endmodule