// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: UART top level wrapper file

`include "prim_assert.sv"

module uart
    import uart_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  parameter AHBDataWidth = 64,
  parameter AHBAddrWidth = 32
) (
  input logic clk_i,
  input logic rst_ni,

  // AMBA AHB Lite Interface
  input logic [AHBAddrWidth-1:0]  haddr_i,
  input logic [AHBDataWidth-1:0]  hwdata_i,
  input logic                     hsel_i,
  input logic                     hwrite_i,
  input logic                     hready_i,
  input logic [1:0]               htrans_i,
  input logic [2:0]               hsize_i,

  output logic                    hresp_o,
  output logic                    hreadyout_o,
  output logic [AHBDataWidth-1:0] hrdata_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Generic IO
  input           cio_rx_i,
  output logic    cio_tx_o,
  output logic    cio_tx_en_o,

  // Interrupts
  output logic    intr_tx_watermark_o ,
  output logic    intr_rx_watermark_o ,
  output logic    intr_tx_empty_o  ,
  output logic    intr_rx_overflow_o  ,
  output logic    intr_rx_frame_err_o ,
  output logic    intr_rx_break_err_o ,
  output logic    intr_rx_timeout_o   ,
  output logic    intr_rx_parity_err_o
);

  logic [NumAlerts-1:0] alert_test, alerts;
  uart_reg2hw_t reg2hw;
  uart_hw2reg_t hw2reg;

  uart_reg_top #(
    .AHBDataWidth(AHBDataWidth),
    .AHBAddrWidth(AHBAddrWidth)
  ) u_reg (
    .clk_i,
    .rst_ni,
    .haddr_i,
    .hwdata_i,
    .hsel_i,
    .hwrite_i,
    .hready_i,
    .htrans_i,
    .hsize_i,
    .hresp_o,
    .hreadyout_o,
    .hrdata_o,
    .reg2hw,
    .hw2reg,
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o (alerts[0]),
    .devmode_i  (1'b1)
  );

  uart_core uart_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .rx    (cio_rx_i   ),
    .tx    (cio_tx_o   ),

    .intr_tx_watermark_o,
    .intr_rx_watermark_o,
    .intr_tx_empty_o,
    .intr_rx_overflow_o,
    .intr_rx_frame_err_o,
    .intr_rx_break_err_o,
    .intr_rx_timeout_o,
    .intr_rx_parity_err_o
  );

  // Alerts
  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[0]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  // always enable the driving out of TX
  assign cio_tx_en_o = 1'b1;

  // Outputs should have a known value after reset
  `CALIPTRA_ASSERT_KNOWN(AHBRespKnownO_A, hresp_o)
  `CALIPTRA_ASSERT_KNOWN(AHBReadyKnownO_A, hreadyout_o)

  // Assert Known for outputs
  `CALIPTRA_ASSERT(TxEnIsOne_A, cio_tx_en_o === 1'b1)
  `CALIPTRA_ASSERT_KNOWN(TxKnown_A, cio_tx_o, clk_i, !rst_ni || !cio_tx_en_o)

  // Assert Known for alerts
  `CALIPTRA_ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

  // Assert Known for interrupts
  `CALIPTRA_ASSERT_KNOWN(TxWatermarkKnown_A, intr_tx_watermark_o)
  `CALIPTRA_ASSERT_KNOWN(RxWatermarkKnown_A, intr_rx_watermark_o)
  `CALIPTRA_ASSERT_KNOWN(TxEmptyKnown_A, intr_tx_empty_o)
  `CALIPTRA_ASSERT_KNOWN(RxOverflowKnown_A, intr_rx_overflow_o)
  `CALIPTRA_ASSERT_KNOWN(RxFrameErrKnown_A, intr_rx_frame_err_o)
  `CALIPTRA_ASSERT_KNOWN(RxBreakErrKnown_A, intr_rx_break_err_o)
  `CALIPTRA_ASSERT_KNOWN(RxTimeoutKnown_A, intr_rx_timeout_o)
  `CALIPTRA_ASSERT_KNOWN(RxParityErrKnown_A, intr_rx_parity_err_o)

  // Alert assertions for reg_we onehot check
  `CALIPTRA_ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule
