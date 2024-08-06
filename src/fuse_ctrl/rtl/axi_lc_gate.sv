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

module axi_lc_gate 
    import axi_pkg::*;
    import lc_ctrl_pkg::*;
#(
    // Number of LC gating muxes in each direction.
    // It is recommended to set this parameter to 2, which results
    // in a total of 4 gating muxes.
    parameter int NumGatesPerDirection = 2
) (
    input clk_i, 
    input rst_ni,

    // AXI interface between host and device
    input  logic                                      prim_dv,
    input  logic [AW-1:0]                             prim_addr,
    input logic                                       prim_write,
    input logic   [IW-1:0]                            prim_id,
    input logic   [DW-1:0]                            prim_wdata,
    input logic   [BC-1:0]                            prim_wstrb,
    output logic  [DW-1:0]                            prim_rdata,
    input logic                                       prim_last,
    output logic                                      prim_hld,
    output logic                                      prim_err,

    output logic                                      prim_dv_gated,
    output logic [Aw-1:0]                             prim_addr_gated,
    output logic                                      prim_write_gated,
    output logic [IW-1:0]                             prim_id_gated,
    output logic [DW-1:0]                             prim_wdata_gated,
    output logic [BC-1:0]                             prim_wstrb_gated,
    input logic [DW-1:0]                             prim_rdata_gated,
    output logic                                      prim_last_gated,
    input logic                                       prim_hld_gated,
    input logic                                       prim_err_gated,

    // Flush control signaling
    input flush_req_i,
    output logic flush_ack_o,

    // Indicates whether there are pending responses
    output logic resp_pending_o,

    // LC onctrol signal
    input lc_tx_t   lc_en_i,
    output logic err_o
);

    //////////////////
    // Access Gates //
    //////////////////

    lc_tx_t err_en;
    lc_tx_t [NumGatesPerDirection-1:0] err_en_buf;

    caliptra_prim_lc_sync #(
        .NumCopies(NumGatesPerDirection),
        .AsyncOn(0)
    ) u_err_en_sync (
        .clk_i,
        .rst_ni,
        .lc_en_i(err_en),
        .lc_en_o(err_en_buf)
    );

    logic prim_dv_int [NumGatesPerDirection+1];
    logic [AW-1:0] prim_addr_int [NumGatesPerDirection+1];
    logic [IW-1:0] prim_id_int [NumGatesPerDirection+1];
    logic prim_write_int [NumGatesPerDirection+1];
    logic [DW-1:0] prim_wdata_int [NumGatesPerDirection+1];
    logic [BC-1:0] prim_wstrb_int [NumGatesPerDirection+1];
    logic [DW-1:0] prim_rdata_int [NumGatesPerDirection+1];
    logic prim_last_int [NumGatesPerDirection+1];
    logic prim_err_int [NumGatesPerDirection+1];
    logic prim_hld_int [NumGatesPerDirection+1];

    for (genvar k = 0; k < NumGatesPerDirection; k++) begin
        caliptra_prim_blanker #(
            .Width($bits())
        ) u_prim_blanker (
            .in_i (),
            .en_i (),
            .out_o ()
        );
    end

    ///////////////////////////
  // Host Side Interposing //
  ///////////////////////////

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 4 -n 8 \
  //      -s 3379253306 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (66.67%)
  //  6: |||||||||| (33.33%)
  //  7: --
  //  8: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 5
  //
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 5 -n 9 \
  //      -s 686407169 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (60.00%)
  //  6: ||||||||||||| (40.00%)
  //  7: --
  //  8: --
  //  9: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 6
  //
  localparam int StateWidth = 9;
  typedef enum logic [StateWidth-1:0] {
    StActive = 9'b100100001,
    StOutstanding = 9'b011100111,
    StFlush = 9'b001001100,
    StError = 9'b010111010,
    StErrorOutstanding = 9'b100010110
  } state_e;

  state_e state_d, state_q;
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StError)

  logic [1:0] outstanding_txn;
  logic a_ack;
  logic d_ack;
  assign a_ack = tl_h2d_i.a_valid & tl_d2h_o.a_ready;
  assign d_ack = tl_h2d_i.d_ready & tl_d2h_o.d_valid;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      outstanding_txn <= '0;
    end else if (a_ack && !d_ack) begin
      outstanding_txn <= outstanding_txn + 1'b1;
    end else if (d_ack && !a_ack) begin
      outstanding_txn <= outstanding_txn - 1'b1;
    end
  end

  logic block_cmd;
  always_comb begin
    block_cmd = '0;
    state_d = state_q;
    err_en = Off;
    err_o = '0;
    flush_ack_o = '0;
    resp_pending_o = 1'b0;

    unique case (state_q)
      StActive: begin
        if (lc_tx_test_false_loose(lc_en_i) || flush_req_i) begin
          state_d = StOutstanding;
        end
        if (outstanding_txn != '0) begin
          resp_pending_o = 1'b1;
        end
      end

      StOutstanding: begin
        block_cmd = 1'b1;
        if (outstanding_txn == '0) begin
          state_d = lc_tx_test_false_loose(lc_en_i) ? StError : StFlush;
        end else begin
          resp_pending_o = 1'b1;
        end
      end

      StFlush: begin
        block_cmd = 1'b1;
        flush_ack_o = 1'b1;
        if (lc_tx_test_false_loose(lc_en_i)) begin
          state_d = StError;
        end else if (!flush_req_i) begin
          state_d = StActive;
        end
      end

      StError: begin
        err_en = On;
        if (lc_tx_test_true_strict(lc_en_i)) begin
          state_d = StErrorOutstanding;
        end
      end

      StErrorOutstanding: begin
        err_en = On;
        block_cmd = 1'b1;
        if (outstanding_txn == '0) begin
          state_d = StActive;
        end
      end

      default: begin
        err_o = 1'b1;
        err_en = On;
      end

    endcase // unique case (state_q)
  end


  // At the host side, we interpose the ready / valid signals so that we can return a bus error
  // in case the lc signal is not set to ON. Note that this logic does not have to be duplicated
  // since erroring back is considered a convenience feature so that the bus does not lock up.
  tl_h2d_t tl_h2d_error;
  tl_d2h_t tl_d2h_error;
  always_comb begin
    tl_h2d_int[0] = tl_h2d_i;
    tl_d2h_o      = tl_d2h_int[0];
    tl_h2d_error  = '0;

    if (lc_tx_test_true_loose(err_en)) begin
      tl_h2d_error  = tl_h2d_i;
      tl_d2h_o      = tl_d2h_error;
    end

    if (block_cmd) begin
      tl_d2h_o.a_ready = 1'b0;
      tl_h2d_int[0].a_valid = 1'b0;
      tl_h2d_error.a_valid = 1'b0;
    end
  end

  tlul_err_resp u_tlul_err_resp (
    .clk_i,
    .rst_ni,
    .tl_h_i(tl_h2d_error),
    .tl_h_o(tl_d2h_error)
  );

  // Add assertion
  `ASSERT(OutStandingOvfl_A, &outstanding_txn |-> ~a_ack)

endmodule : axi_lc_gate