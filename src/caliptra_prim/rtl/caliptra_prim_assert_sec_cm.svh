// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// // Macros and helper code for security countermeasures.

`ifndef PRIM_ASSERT_SEC_CM_SVH
`define PRIM_ASSERT_SEC_CM_SVH

`define _SEC_CM_ALERT_MAX_CYC 30

// Helper macros
`define CALIPTRA_ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_, MAX_CYCLES_, ERR_NAME_) \
  `CALIPTRA_ASSERT(FpvSecCm``NAME_``, \
          $rose(PRIM_HIER_.ERR_NAME_) && !(GATE_) \
          |-> ##[0:MAX_CYCLES_] (ALERT_.alert_p)) \
  `ifdef INC_ASSERT \
  assign PRIM_HIER_.unused_assert_connected = 1'b1; \
  `endif \
  `CALIPTRA_ASSUME_FPV(``NAME_``TriggerAfterAlertInit_S, $stable(rst_ni) == 0 |-> \
                       PRIM_HIER_.ERR_NAME_ == 0 [*10])

`define CALIPTRA_ASSERT_ERROR_TRIGGER_ERR(NAME_, PRIM_HIER_, ERR_, GATE_, MAX_CYCLES_, ERR_NAME_, CLK_, RST_) \
  `CALIPTRA_ASSERT(FpvSecCm``NAME_``, \
          $rose(PRIM_HIER_.ERR_NAME_) && !(GATE_) \
          |-> ##[0:MAX_CYCLES_] (ERR_), CLK_, RST_) \
  `ifdef INC_ASSERT \
  assign PRIM_HIER_.unused_assert_connected = 1'b1; \
  `endif

// macros for security countermeasures that will trigger alert
`define CALIPTRA_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_SEC_CM_ALERT_MAX_CYC) \
  `CALIPTRA_ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_, MAX_CYCLES_, err_o)

`define CALIPTRA_ASSERT_PRIM_DOUBLE_LFSR_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_SEC_CM_ALERT_MAX_CYC) \
  `CALIPTRA_ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_, MAX_CYCLES_, err_o)

`define CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_SEC_CM_ALERT_MAX_CYC) \
  `CALIPTRA_ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_, MAX_CYCLES_, unused_err_o)

`define CALIPTRA_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_SEC_CM_ALERT_MAX_CYC) \
  `CALIPTRA_ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_, MAX_CYCLES_, err_o)

`define CALIPTRA_ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(NAME_, REG_TOP_HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_SEC_CM_ALERT_MAX_CYC) \
  `CALIPTRA_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ALERT(NAME_, \
    REG_TOP_HIER_.u_caliptra_prim_reg_we_check.u_caliptra_prim_onehot_check, ALERT_, GATE_, MAX_CYCLES_)

// macros for security countermeasures that will trigger other errors
`define CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(NAME_, PRIM_HIER_, ERR_, GATE_ = 0, MAX_CYCLES_ = 2, CLK_ = clk_i, RST_ = !rst_ni) \
  `CALIPTRA_ASSERT_ERROR_TRIGGER_ERR(NAME_, PRIM_HIER_, ERR_, GATE_, MAX_CYCLES_, unused_err_o, CLK_, RST_)

`define CALIPTRA_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ERR(NAME_, PRIM_HIER_, ERR_, GATE_ = 0, MAX_CYCLES_ = 2, CLK_ = clk_i, RST_ = !rst_ni) \
  `CALIPTRA_ASSERT_ERROR_TRIGGER_ERR(NAME_, PRIM_HIER_, ERR_, GATE_, MAX_CYCLES_, err_o, CLK_, RST_)

`define CALIPTRA_ASSERT_PRIM_DOUBLE_LFSR_ERROR_TRIGGER_ERR(NAME_, PRIM_HIER_, ERR_, GATE_ = 0, MAX_CYCLES_ = 2, CLK_ = clk_i, RST_ = !rst_ni) \
  `CALIPTRA_ASSERT_ERROR_TRIGGER_ERR(NAME_, PRIM_HIER_, ERR_, GATE_, MAX_CYCLES_, err_o, CLK_, RST_)

`define CALIPTRA_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ERR(NAME_, PRIM_HIER_, ERR_, GATE_ = 0, MAX_CYCLES_ = `_SEC_CM_ALERT_MAX_CYC, CLK_ = clk_i, RST_ = !rst_ni) \
  `CALIPTRA_ASSERT_ERROR_TRIGGER_ERR(NAME_, PRIM_HIER_, ERR_, GATE_, MAX_CYCLES_, err_o, CLK_, RST_)

`define CALIPTRA_ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ERR(NAME_, REG_TOP_HIER_, ERR_, GATE_ = 0, MAX_CYCLES_ = `_SEC_CM_ALERT_MAX_CYC, CLK_ = clk_i, RST_ = !rst_ni) \
  `CALIPTRA_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ERR(NAME_, \
    REG_TOP_HIER_.u_caliptra_prim_reg_we_check.u_caliptra_prim_onehot_check, ERR_, GATE_, MAX_CYCLES_, CLK_, RST_)

`endif // PRIM_ASSERT_SEC_CM_SVH
