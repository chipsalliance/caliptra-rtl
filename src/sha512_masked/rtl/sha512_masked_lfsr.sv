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
// sha512_masked_lfsr.sv
// ------
// 74-bit LFSR
// 
//======================================================================

module sha512_masked_lfsr
#(
   parameter                     REG_SIZE  = 74,
   parameter [REG_SIZE-1 : 0]    INIT_SEED = 74'h23A_A79D_0EC1_1E38_9277 // a random value
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

  //----------------------------------------------------------------
  // reg_update
  // Update functionality for all registers in the core.
  //----------------------------------------------------------------
   
   // TAPs are: 74,73,59,58 based on Xilinx doc: https://docs.xilinx.com/v/u/en-US/xapp052
   always_comb feedback = rnd_reg[73] ^ rnd_reg[72] ^ rnd_reg[58] ^ rnd_reg[57];

   always_comb rnd_next = {rnd_reg[REG_SIZE-2 : 0], feedback};

   always_ff @ (posedge clk or negedge reset_n) 
   begin
      if (!reset_n)
         rnd_reg <= INIT_SEED;
      else if (zeroize)
         rnd_reg <= INIT_SEED;
      else if (en)
         rnd_reg <= seed;
      else
         rnd_reg <= rnd_next;
   end

   assign rnd = rnd_reg;

endmodule