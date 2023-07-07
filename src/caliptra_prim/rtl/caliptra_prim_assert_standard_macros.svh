// Copyright lowRISC contributors.
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
  final begin                                                                \
    __name: assert (__prop || $test$plusargs("disable_assert_final_checks")) \
      else begin                                                             \
        `CALIPTRA_ASSERT_ERROR(__name)                                                \
      end                                                                    \
  end

`ifndef CALIPTRA_SVA
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
