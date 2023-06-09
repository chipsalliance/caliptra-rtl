// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by caliptra_prim_assert.sv for formal verification with Yosys. See caliptra_prim_assert.sv
// for documentation for each of the macros.

`define CALIPTRA_ASSERT_I(__name, __prop)    \
  always_comb begin : __name        \
    assert (__prop);                \
  end

`define CALIPTRA_ASSERT_INIT(__name, __prop)    \
  initial begin : __name               \
    assert (__prop);                   \
  end

`define CALIPTRA_ASSERT_INIT_NET(__name, __prop) \
  initial begin : __name                \
    #1ps assert (__prop);               \
  end

// This doesn't make much sense for a formal tool (we never get to the final block!)
`define CALIPTRA_ASSERT_FINAL(__name, __prop)

`ifndef CALIPTRA_SVA
`define CALIPTRA_ASSERT(__name, __prop, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
  always_ff @(posedge __clk) begin                                                       \
    if (! (__rst !== '0)) __name: assert (__prop);                                       \
  end

`define CALIPTRA_ASSERT_NEVER(__name, __prop, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
  always_ff @(posedge __clk) begin                                                             \
    if (! (__rst !== '0)) __name: assert (! (__prop));                                         \
  end

// Yosys uses 2-state logic, so this doesn't make sense here
`define CALIPTRA_ASSERT_KNOWN(__name, __sig, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST)
`endif

`define CALIPTRA_COVER(__name, __prop, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
  always_ff @(posedge __clk) begin : __name                                             \
    cover ((! (__rst !== '0)) && (__prop));                                             \
  end

`define CALIPTRA_ASSUME(__name, __prop, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST) \
  always_ff @(posedge __clk) begin                                                       \
    if (! (__rst !== '0)) __name: assume (__prop);                                       \
  end

`define CALIPTRA_ASSUME_I(__name, __prop)              \
  always_comb begin : __name                  \
    assume (__prop);                          \
  end
