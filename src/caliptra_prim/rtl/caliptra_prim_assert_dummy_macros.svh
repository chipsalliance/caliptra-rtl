// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by caliptra_prim_assert.sv for tools that don't support assertions. See
// caliptra_prim_assert.sv for documentation for each of the macros.

// Explicitly include the files that define the macros referenced below
// (CALIPTRA_ASSERT_DEFAULT_CLK/RST from caliptra_sva.svh; complex macros from
// caliptra_prim_assert.sv). Both are include-guarded, so these are no-ops when
// this fragment is pulled in via caliptra_prim_assert.sv.
`include "caliptra_sva.svh"
`include "caliptra_prim_assert.sv"

`define CALIPTRA_ASSERT_I(__name, __prop)
`define CALIPTRA_ASSERT_INIT(__name, __prop)
`define CALIPTRA_ASSERT_INIT_NET(__name, __prop)
`define CALIPTRA_ASSERT_FINAL(__name, __prop)
`define CALIPTRA_ASSERT_AT_RESET(__name, __prop, __rst = `CALIPTRA_ASSERT_DEFAULT_RST)
`define CALIPTRA_ASSERT_AT_RESET_AND_FINAL(__name, __prop, __rst = `CALIPTRA_ASSERT_DEFAULT_RST)
`define CALIPTRA_WITHIN_MARGIN(__actual, __expected, __allowed_less, __allowed_more) 
`ifndef CALIPTRA_SVA
`define CALIPTRA_ASSERT(__name, __prop, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST)
`define CALIPTRA_ASSERT_NEVER(__name, __prop, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST)
`define CALIPTRA_ASSERT_KNOWN(__name, __sig, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST)
`endif
`define CALIPTRA_COVER(__name, __prop, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST)
`define CALIPTRA_ASSUME(__name, __prop, __clk = `CALIPTRA_ASSERT_DEFAULT_CLK, __rst = `CALIPTRA_ASSERT_DEFAULT_RST)
`define CALIPTRA_ASSUME_I(__name, __prop)
