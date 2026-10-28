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
// physical_rng_deterministic.sv
// -----------------------------
// Deterministic simulation RNG for reproducible entropy_src tests.
//
// Unlike physical_rng (which replays InitialSeed for the first 384 bits and then
// returns $urandom), this model streams a fully deterministic nibble sequence for
// its ENTIRE runtime. That lets a reference model predict the conditioned
// entropy_src output exactly -- needed for FIPS/continuous-mode combine tests
// (per-ES SHA3-384 conditioner ON) and multi-seed tests, where the ES absorbs
// many samples per seed and $urandom would make the result uncheckable.
//
// Pattern: a 32-bit Galois right-shift LFSR with tap mask 0xEDB88320 (the
// reversed CRC-32 polynomial). Each 4-bit output sample is built from 4
// consecutive LFSR output bits (so samples do not overlap):
//
//   s = LfsrSeed
//   for each sample:
//     for b in 0..3: sample[b] = s[0]; s = s[0] ? (s>>1)^0xEDB88320 : (s>>1)
//
// Reproduce in Python:
//   def next_sample(s):
//       nib = 0
//       for b in range(4):
//           nib |= (s & 1) << b
//           s = ((s >> 1) ^ 0xEDB88320) if (s & 1) else (s >> 1)
//       return nib, s
//
// A distinct nonzero LfsrSeed per source makes ES0 and ES1 stream different
// entropy. The LFSR is reloaded with LfsrSeed whenever the source is disabled
// (like physical_rng restarts its InitialSeed), so every time entropy_src is
// (re-)enabled, the sample sequence starts from LfsrSeed again -- the reference
// model just takes the first N samples after each enable. The emitted values are
// independent of DutyCycle (which only sets the streaming rate); a small
// DutyCycle keeps sims fast.
//
//======================================================================

module physical_rng_deterministic #(
  // Distinct nonzero seed per source, loaded once at time 0.
  parameter logic [31:0] LfsrSeed  = 32'hDEADBEEF,
  // Cycles between emitted samples. Small => fast. Does not affect the values.
  parameter int unsigned DutyCycle = 4
) (
  input  logic       clk,
  input  logic       enable,
  output logic [3:0] data,
  output logic       valid
);

  localparam logic [31:0] LfsrTaps = 32'hEDB88320; // reversed CRC-32 polynomial

  logic [31:0] lfsr;
  logic [31:0] count;
  logic [3:0]  data_q;

  wire pulse = (count == DutyCycle - 1);
  assign data = data_q;

  // Unrolled 4-step LFSR advance (no block-local variables -> fully portable).
  // sample bit b = the b-th consecutive LFSR output bit (the LSB shifted out).
  wire        b0 = lfsr[0];
  wire [31:0] s1 = b0 ? ((lfsr >> 1) ^ LfsrTaps) : (lfsr >> 1);
  wire        b1 = s1[0];
  wire [31:0] s2 = b1 ? ((s1   >> 1) ^ LfsrTaps) : (s1   >> 1);
  wire        b2 = s2[0];
  wire [31:0] s3 = b2 ? ((s2   >> 1) ^ LfsrTaps) : (s2   >> 1);
  wire        b3 = s3[0];
  wire [31:0] s4 = b3 ? ((s3   >> 1) ^ LfsrTaps) : (s3   >> 1);
  wire [3:0]  sample_c    = {b3, b2, b1, b0};
  wire [31:0] lfsr_next_c = s4;

  initial begin
    lfsr   = LfsrSeed;
    count  = '0;
    data_q = '0;
    valid  = 1'b0;
  end

  always @(posedge clk) begin
    if (enable) begin
      valid <= 1'b0;
      count <= count + 1'b1;
      if (pulse) begin
        data_q <= sample_c;
        lfsr   <= lfsr_next_c;
        valid  <= 1'b1;
        count  <= '0;
      end
    end else begin
      // Reload the LFSR while disabled so that every enable starts the sample
      // sequence from LfsrSeed. This makes tests that disable, reconfigure and
      // re-enable entropy_src predictable by the reference model.
      lfsr  <= LfsrSeed;
      valid <= 1'b0;
      count <= '0;
    end
  end

endmodule : physical_rng_deterministic
