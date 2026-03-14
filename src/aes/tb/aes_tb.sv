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
// aes_tb.sv
// ---------
// Testbench for the AES top-level module (aes.sv).
// Drives the TLUL bus interface directly.
//
//======================================================================

module aes_tb
  import aes_pkg::*;
  import aes_reg_pkg::*;
  import caliptra_tlul_pkg::*;
  import caliptra_prim_alert_pkg::*;
  import caliptra_prim_mubi_pkg::*;
  import lc_ctrl_pkg::*;
  import edn_pkg::*;
  import keymgr_pkg::*;
();

  //----------------------------------------------------------------
  // Parameters
  //----------------------------------------------------------------
  parameter CLK_HALF_PERIOD = 1;
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  //----------------------------------------------------------------
  // DUT parameters (match aes.sv defaults)
  //----------------------------------------------------------------
  parameter bit AES192Enable         = 1;
  parameter bit AESGCMEnable         = 1;
  parameter bit SecMasking           = 1;
  parameter sbox_impl_e SecSBoxImpl  = SBoxImplDom;

  //----------------------------------------------------------------
  // Signal declarations
  //----------------------------------------------------------------
  logic clk_tb;
  logic rst_n_tb;
  logic rst_shadowed_n_tb;

  // Idle / clock manager
  mubi4_t idle_o_tb;

  // Life cycle
  lc_tx_t lc_escalate_en_tb;

  // EDN interface
  logic       clk_edn_tb;
  logic       rst_edn_n_tb;
  edn_req_t   edn_o_tb;
  edn_rsp_t   edn_i_tb;

  // Key manager sideload interface
  hw_key_req_t keymgr_key_tb;

  // TLUL bus interface
  tl_h2d_t tl_h2d_tb;
  tl_d2h_t tl_d2h_tb;

  // Alerts
  alert_rx_t [NumAlerts-1:0] alert_rx_tb;
  alert_tx_t [NumAlerts-1:0] alert_tx_tb;

  //----------------------------------------------------------------
  // Device Under Test
  //----------------------------------------------------------------
  aes #(
    .AES192Enable ( AES192Enable ),
    .AESGCMEnable ( AESGCMEnable ),
    .SecMasking   ( SecMasking   ),
    .SecSBoxImpl  ( SecSBoxImpl  )
  ) dut (
    .clk_i             ( clk_tb             ),
    .rst_ni            ( rst_n_tb           ),
    .rst_shadowed_ni   ( rst_shadowed_n_tb  ),

    .idle_o            ( idle_o_tb          ),

    .lc_escalate_en_i  ( lc_escalate_en_tb  ),

    .clk_edn_i         ( clk_edn_tb         ),
    .rst_edn_ni        ( rst_edn_n_tb       ),
    .edn_o             ( edn_o_tb           ),
    .edn_i             ( edn_i_tb           ),

    .keymgr_key_i      ( keymgr_key_tb      ),

    .tl_i              ( tl_h2d_tb          ),
    .tl_o              ( tl_d2h_tb          ),

    .alert_rx_i        ( alert_rx_tb        ),
    .alert_tx_o        ( alert_tx_tb        )
  );

  //----------------------------------------------------------------
  // Clock generators
  //----------------------------------------------------------------
  initial clk_tb = 1'b0;
  always
    begin : clk_gen
      #CLK_HALF_PERIOD clk_tb = ~clk_tb;
    end //clk_gen

  // EDN clock (same domain in this simple testbench; adjust if needed)
  assign clk_edn_tb = clk_tb;

  //----------------------------------------------------------------
  // Stub / tie-off assignments
  //----------------------------------------------------------------
  // Life cycle: no escalation
  assign lc_escalate_en_tb = lc_ctrl_pkg::Off;

  // EDN: acknowledge every request one cycle after it arrives
  always_ff @(posedge clk_edn_tb or negedge rst_edn_n_tb) begin
    if (!rst_edn_n_tb) begin
      edn_i_tb <= '0;
    end else begin
      edn_i_tb.edn_ack  <= edn_o_tb.edn_req;
      edn_i_tb.edn_bus  <= $urandom();  // pseudo-random entropy
      edn_i_tb.edn_fips <= 1'b0;
    end
  end

  // Key manager: no sideload key
  assign keymgr_key_tb = '0;

  // Alert receivers: idle (no ping, no ack)
  assign alert_rx_tb = '0;

  //----------------------------------------------------------------
  // init_sim()
  // Initialize all signals to a defined state.
  //----------------------------------------------------------------
  task automatic init_sim();
    rst_n_tb          = 1'b0;
    rst_shadowed_n_tb = 1'b0;
    rst_edn_n_tb      = 1'b0;
    tl_h2d_tb         = '0;
  endtask

  //----------------------------------------------------------------
  // reset_dut()
  // Assert then deassert reset.
  //----------------------------------------------------------------
  task automatic reset_dut();
    $display("[TB] Asserting reset");
    rst_n_tb          = 1'b0;
    rst_shadowed_n_tb = 1'b0;
    rst_edn_n_tb      = 1'b0;
    repeat (4) @(posedge clk_tb);

    rst_edn_n_tb = 1'b1;
    repeat (2) @(posedge clk_tb);

    rst_n_tb          = 1'b1;
    rst_shadowed_n_tb = 1'b1;
    repeat (2) @(posedge clk_tb);
    $display("[TB] Reset released");
  endtask

  //----------------------------------------------------------------
  // run_aes_block()
  // Inject a single AES block operation via hierarchical force,
  // bypassing the TLUL register interface. Uses FIPS 197 big-endian
  // word ordering (word 0 = most-significant 32 bits).
  //
  // Key masking: share 1 = 0, so share 0 XOR share 1 = actual key.
  //----------------------------------------------------------------
  task automatic run_aes_block(
      input  aes_mode_e    mode,       // AES_ECB, AES_CBC, AES_CTR, ...
      input  aes_op_e      operation,  // AES_ENC or AES_DEC
      input  key_len_e     key_len,    // AES_128, AES_192, AES_256
      input  logic [255:0] key,        // Big-endian; upper 128b unused for AES-128
      input  logic [127:0] iv,         // Big-endian; ignored for ECB
      input  logic [127:0] data_in,    // Plaintext (enc) or ciphertext (dec)
      output logic [127:0] data_out    // Ciphertext (enc) or plaintext (dec)
  );
    // Step 1: Force control signals
    force dut.u_aes_core.aes_mode_q         = mode;
    force dut.u_aes_core.aes_op_q           = operation;
    force dut.u_aes_core.key_len_q          = key_len;
    force dut.u_aes_core.manual_operation_q = 1'b1;

    // Step 2: Force key — share 0 = actual key, share 1 = 0 (zero mask)
    for (int i = 0; i < 8; i++) begin
      force dut.u_aes_core.key_init_q[i][0] = key[255 - i*32 -: 32];
      force dut.u_aes_core.key_init_q[i][1] = 32'h0;
    end

    // Step 3: Force IV (big-endian word order; harmless for ECB)
    for (int i = 0; i < 4; i++)
      force dut.u_aes_core.iv_q[i] = iv[127 - i*32 -: 32];

    // Step 4: Force data_in (big-endian word order)
    for (int i = 0; i < 4; i++)
      force dut.u_aes_core.data_in[i] = data_in[127 - i*32 -: 32];

    // Step 5: Pulse the software start trigger for one clock cycle
    @(posedge clk_tb);
    force dut.reg2hw.trigger.start.q = 1'b1;
    @(posedge clk_tb);
    release dut.reg2hw.trigger.start.q;

    // Step 6: Poll output_valid
    while (!dut.hw2reg.status.output_valid.d)
      @(posedge clk_tb);

    // Step 7: Capture data_out (big-endian word order)
    for (int i = 0; i < 4; i++)
      data_out[127 - i*32 -: 32] = dut.u_aes_core.data_out_q[i];

    // Step 8: Release all forced signals
    release dut.u_aes_core.aes_mode_q;
    release dut.u_aes_core.aes_op_q;
    release dut.u_aes_core.key_len_q;
    release dut.u_aes_core.manual_operation_q;
    for (int i = 0; i < 8; i++) begin
      release dut.u_aes_core.key_init_q[i][0];
      release dut.u_aes_core.key_init_q[i][1];
    end
    for (int i = 0; i < 4; i++) begin
      release dut.u_aes_core.iv_q[i];
      release dut.u_aes_core.data_in[i];
    end

    // Step 9: Display result
    $display("[TB] run_aes_block: data_out = %032h", data_out);
  endtask

  //----------------------------------------------------------------
  // Main test sequence
  //----------------------------------------------------------------
  initial begin : main
    logic [127:0] result;

    $display("[TB] aes_tb started");

    init_sim();
    reset_dut();

    // FIPS 197 Appendix B — AES-128 ECB encrypt
    // Key:      000102030405060708090a0b0c0d0e0f
    // Plaintext: 00112233445566778899aabbccddeeff
    // Expected:  69c4e0d86a7b04300d8a1c30b5a2ab83
    run_aes_block(
      AES_ECB,
      AES_ENC,
      AES_128,
      256'h000102030405060708090a0b0c0d0e0f_00000000000000000000000000000000,
      128'h0,                        // IV unused for ECB
      128'h00112233445566778899aabbccddeeff,
      result
    );
    $display("[TB] Expected: 69c4e0d86a7b04300d8a1c30b5a2ab83");
    $display("[TB] Got:      %032h", result);

    $display("[TB] aes_tb done");
    $finish;
  end

endmodule : aes_tb

//======================================================================
// EOF aes_tb.sv
//======================================================================
