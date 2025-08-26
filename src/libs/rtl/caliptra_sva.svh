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

`ifndef CALIPTRA_SVA
`define CALIPTRA_SVA

// Default clk and reset signals used by assertion macros below.
`define CALIPTRA_ASSERT_DEFAULT_CLK clk_i
`define CALIPTRA_ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define STRINGIFY(__x) `"__x`"

// CALIPTRA_ASSERT_RPT is available to change the reporting mechanism when an assert fails
`define CALIPTRA_ASSERT_RPT(name)                                                  \
`ifdef UVM                                                                            \
  uvm_pkg::uvm_report_error("CALIPTRA ASSERT FAILED", name, uvm_pkg::UVM_NONE,        \
                            `__FILE__, `__LINE__);                                    \
`else                                                                                 \
  $fatal(1, "[CALIPTRA_ASSERT FAILED] [%m] %s (%s:%0d)",name, `__FILE__, `__LINE__);  \
`endif

// Assert a concurrent property directly.
`define CALIPTRA_ASSERT(assert_name, prop, clk = `CALIPTRA_ASSERT_DEFAULT_CLK, rst = `CALIPTRA_ASSERT_DEFAULT_RST)  \
`ifdef CLP_ASSERT_ON                                                           \
  assert_name: assert property (@(posedge clk) disable iff (rst !== 0) (prop))    \
    else begin                                                                 \
        `CALIPTRA_ASSERT_RPT(`STRINGIFY(assert_name))                                   \
    end                                                                        \
`endif

// Assert a concurrent property NEVER happens
`define CALIPTRA_ASSERT_NEVER(assert_name, prop, clk = `CALIPTRA_ASSERT_DEFAULT_CLK, rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
`ifdef CLP_ASSERT_ON                                                            \
  assert_name: assert property (@(posedge clk) disable iff (rst !== 0) not (prop)) \
    else begin                                                                  \
        `CALIPTRA_ASSERT_RPT(`STRINGIFY(assert_name))                                    \
    end                                                                         \
`endif

// Assert that signal is not x
`define CALIPTRA_ASSERT_KNOWN(assert_name, sig, clk = `CALIPTRA_ASSERT_DEFAULT_CLK, rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
  `CALIPTRA_ASSERT(assert_name, !$isunknown(sig), clk, rst)

// Assert that a vector of signals is mutually exclusive
`define CALIPTRA_ASSERT_MUTEX(assert_name, sig, clk = `CALIPTRA_ASSERT_DEFAULT_CLK, rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
    `CALIPTRA_ASSERT(assert_name, $onehot0(sig), clk, rst)

// Assert that a vector of signals is stable (does not change value)
`define CALIPTRA_ASSERT_STABLE(assert_name, sig, clk = `CALIPTRA_ASSERT_DEFAULT_CLK, rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
    `CALIPTRA_ASSERT(assert_name, $stable(sig), clk, rst)

`endif
