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
// physical_rng.sv
// --------
// Simple simulation model for a rng.  Generates 32b of random data
// and pushes out 4b at a time through the data/valid interface.
//
// An initial seed is provided to generate deterministic results for
// simulation.  After the first 384 bits, random data will be generated.
//
//======================================================================

module physical_rng #(
  // Set UseInitialSeed to 0 to disable
  parameter logic         UseInitialSeed = 1'b1,
  parameter logic [383:0] InitialSeed = 384'h33F63B65F57AD68765693560E743CC5010518E4BF4ECBEBA71DC56AAA08B394311731D9DF763FC5D27E4ED3E4B7DE947,
  // Parameter chosen to mimic a slow source (Expected 50kbps in hw)
  parameter int unsigned DutyCycle = 500
) (
  input  logic       clk,
  input  logic       enable,
  output logic [3:0] data,
  output logic       valid
);

  logic [31:0] count, pulse_count, random_data;

  wire pulse = (count == DutyCycle - 1);

  assign data = random_data[3:0];

  always @(posedge clk) begin
    if (enable) begin
      valid <= 1'b0;
      count <= count + 1'b1;

      // Generate random data
      if (pulse) begin
        if (UseInitialSeed &&
           (pulse_count < $bits(InitialSeed)/$bits(data))) begin
	  pulse_count  <= pulse_count + 1'b1;
          random_data[3:0] <= InitialSeed[pulse_count * $bits(data) +:$bits(data)];
        end else begin
          random_data <= $urandom();
        end

        valid <= 1'b1;
        count <= '0;
      end
    end else begin
      pulse_count  <= '0;
      valid <= 1'b0;
      count <= '0;
    end
  end

endmodule : physical_rng
