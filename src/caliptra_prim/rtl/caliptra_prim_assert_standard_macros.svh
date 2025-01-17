// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by caliptra_prim_assert.sv for tools that support full SystemVerilog and SVA syntax.
// See caliptra_prim_assert.sv for documentation for each of the macros.

`define CALIPTRA_ASSERT_I(__name, __prop) \
  __name: assert (__prop)        \
    else begin                   \
      `CALIPTRA_ASSERT_ERROR(__name)      \
    end

// Formal tools will ignore the initial construct, so use static assertion as a workaround.
// This workaround terminates design elaboration if the __prop predict is false.
// It calls $fatal() with the first argument equal to 2, it outputs the statistics about the memory
// and CPU time.
`define CALIPTRA_ASSERT_INIT(__name, __prop)                                                  \
`ifdef FPV_ON                                                                        \
  if (!(__prop)) $fatal(2, "Fatal static assertion [%s]: (%s) is not true.",         \
                        (__name), (__prop));                                         \
`else                                                                                \
  initial begin                                                                      \
    __name: assert (__prop)                                                          \
      else begin                                                                     \
        `CALIPTRA_ASSERT_ERROR(__name)                                                        \
      end                                                                            \
  end                                                                                \
`endif

`define CALIPTRA_ASSERT_INIT_NET(__name, __prop)                                                   \
  initial begin                                                                      \
    // When a net is assigned with a value, the assignment is evaluated after        \
    // initial in Xcelium. Add 1ps delay to check value after the assignment is      \
    // completed.                                                                    \
    #1ps;                                                                            \
    __name: assert (__prop)                                                          \
      else begin                                                                     \
        `CALIPTRA_ASSERT_ERROR(__name)                                                        \
      end                                                                            \
  end                                                                                \

`define CALIPTRA_ASSERT_FINAL(__name, __prop)                                         \
`ifndef FPV_ON                                                               \
  final begin                                                                \
    __name: assert (__prop || $test$plusargs("disable_assert_final_checks")) \
      else begin                                                             \
        `CALIPTRA_ASSERT_ERROR(__name)                                                \
      end                                                                    \
  end                                                                        \
`endif

`define CALIPTRA_ASSERT_AT_RESET(__name, __prop, __rst = `CALIPTRA_ASSERT_DEFAULT_RST)          \
  // `__rst` is active-high for these macros, so trigger on its posedge.      \
  // The values inside the property are sampled just before the trigger,      \
  // which is necessary to make the evaluation of `__prop` on a reset edge    \
  // meaningful.  On any reset posedge at the start of time, `__rst` itself   \
  // is unknown, and at that time `__prop` is likely not initialized either,  \
  // so this assertion does not evaluate `__prop` when `__rst` is unknown.    \
  //                                                                          \
  // This extra behaviour is not used for FPV, because Jasper doesn't support \
  // it and instead prints the WNL038 warning. Avoid the check and warning    \
  // message in this case.                                                    \
`ifndef FPV_ON                                                                \
  __name: assert property (@(posedge __rst) $isunknown(__rst) || (__prop))    \
`else                                                                         \
  __name: assert property (@(posedge __rst) (__prop))                         \
`endif                                                                        \
    else begin                                                                \
      `CALIPTRA_ASSERT_ERROR(__name)                                                   \
    end

`ifndef CALIPTRA_SVA
`define CALIPTRA_ASSERT_AT_RESET_AND_FINAL(__name, __prop, __rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
    `CALIPTRA_ASSERT_AT_RESET(AtReset_``__name``, __prop, __rst)                        \
    `CALIPTRA_ASSERT_FINAL(Final_``__name``, __prop)

`define CALIPTRA_ASSERT(__name, __prop, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
  __name: assert property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop))       \
    else begin                                                                           \
      `CALIPTRA_ASSERT_ERROR(__name)                                                              \
    end

`define CALIPTRA_ASSERT_NEVER(__name, __prop, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
  __name: assert property (@(posedge __clk) disable iff ((__rst) !== '0) not (__prop))         \
    else begin                                                                                 \
      `CALIPTRA_ASSERT_ERROR(__name)                                                                    \
    end

`define CALIPTRA_ASSERT_KNOWN(__name, __sig, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
  `CALIPTRA_ASSERT(__name, !$isunknown(__sig), __clk, __rst)
`endif

`define CALIPTRA_COVER(__name, __prop, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
  __name: cover property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop));

`define CALIPTRA_ASSUME(__name, __prop, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
  __name: assume property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop))       \
    else begin                                                                           \
      `CALIPTRA_ASSERT_ERROR(__name)                                                              \
    end

`define CALIPTRA_ASSUME_I(__name, __prop) \
  __name: assume (__prop)        \
    else begin                   \
      `CALIPTRA_ASSERT_ERROR(__name)      \
    end
