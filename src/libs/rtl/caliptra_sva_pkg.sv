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


package caliptra_sva_pkg;

// Converts an arbitrary block of code into a Verilog string
`define STRINGIFY(__x) `"__x`"

// ASSERT_RPT is available to change the reporting mechanism when an assert fails
`define ASSERT_RPT(name)                                                  \
`ifdef UVM                                                                \
  assert_rpt_pkg::assert_rpt($sformatf("[%m] %s (%s:%0d)",                \
                             name, `__FILE__, `__LINE__));                \
`else                                                                     \
  $fatal(1, "[ASSERT FAILED] [%m] %s (%s:%0d)",name, `__FILE__, `__LINE__);  \
`endif

// Assert a concurrent property directly.
`define ASSERT(assert_name, prop, clk, rst_b)                                  \
  assert_name: assert property (@(posedge clk) disable iff (~rst_b) (prop))    \
    else begin                                                                 \
        `ASSERT_RPT(`STRINGIFY(assert_name))                                          \
    end

// Assert a concurrent property NEVER happens
`define ASSERT_NEVER(assert_name, prop, clk, rst_b)                             \
  assert_name: assert property (@(posedge clk) disable iff (~rst_b) not (prop)) \
    else begin                                                                  \
        `ASSERT_RPT(`STRINGIFY(assert_name))                                           \
    end

// Assert that signal is not x
`define ASSERT_KNOWN(assert_name, sig, clk, rst_b)     \
  `ASSERT(assert_name, !$isunknown(sig), clk, rst_b)

// Assert that a vector of signals is mutually exclusive
`define ASSERT_MUTEX(assert_name, sig, clk, rst_b)     \
    `ASSERT(assert_name, $onehot0(sig), clk, rst_b)

endpackage