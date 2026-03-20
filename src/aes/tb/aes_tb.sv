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
// Uses hierarchical force/release to drive internal DUT signals,
// following the OpenTitan AES Programmer's Guide sequence:
//   IDLE -> CTRL -> KEY -> IV -> DATA -> START -> OUTPUT_VALID
//
// Supports ECB, CBC, CTR, and GCM modes (multi-block capable).
// Manual operation mode is always enabled so the DUT never auto-triggers.
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
    .rst_edn_ni        ( rst_n_tb           ),
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
  always begin : clk_gen
    #CLK_HALF_PERIOD clk_tb = ~clk_tb;
  end

  // EDN clock (same domain in this simple testbench)
  assign clk_edn_tb = clk_tb;

  //----------------------------------------------------------------
  // Stub / tie-off assignments
  //----------------------------------------------------------------
  assign lc_escalate_en_tb = lc_ctrl_pkg::Off;
  assign edn_i_tb          = '0;
  assign keymgr_key_tb     = '0;
  assign alert_rx_tb       = '0;

  //----------------------------------------------------------------
  // init_sim()
  //----------------------------------------------------------------
  task init_sim();
    rst_n_tb          = 1'b0;
    rst_shadowed_n_tb = 1'b0;
    tl_h2d_tb         = '0;
  endtask

  //----------------------------------------------------------------
  // reset_dut()
  //----------------------------------------------------------------
  task reset_dut();
    $display("[TB] Asserting reset");
    rst_n_tb          = 1'b0;
    rst_shadowed_n_tb = 1'b0;
    repeat (4) @(posedge clk_tb);

    rst_n_tb          = 1'b1;
    rst_shadowed_n_tb = 1'b1;
    repeat (2) @(posedge clk_tb);
    $display("[TB] Reset released");
  endtask

  //================================================================
  // Step 1 — Primitive helper tasks
  //   Each task mirrors one step of the AES Programmer's Guide.
  //================================================================

  // --- Status polling (read-only; never forced) ---

  task wait_idle();
    $display("[TB] Waiting for IDLE...");
    while (!dut.hw2reg.status.idle.d) @(posedge clk_tb);
    $display("[TB] IDLE");
  endtask

  task wait_input_ready();
    while (!dut.hw2reg.status.input_ready.d) @(posedge clk_tb);
  endtask

  task wait_output_valid();
    while (!dut.hw2reg.status.output_valid.d) @(posedge clk_tb);
  endtask

  // --- Force tasks ---

  task force_ctrl(
    input aes_mode_e mode,
    input aes_op_e   op,
    input key_len_e  key_len
  );
    force dut.u_aes_core.aes_mode_q         = mode;
    force dut.u_aes_core.aes_op_q           = op;
    force dut.u_aes_core.key_len_q          = key_len;
    force dut.u_aes_core.manual_operation_q = 1'b1;
  endtask

  task force_key(input logic [255:0] key);
    static int i;
    for (i = 0; i < 8; i++) begin
      force dut.u_aes_core.key_init_q[i][0] = key[255 - i*32 -: 32];
      force dut.u_aes_core.key_init_q[i][1] = 32'h0;
    end
  endtask

  task force_iv(input logic [127:0] iv);
    static int i;
    for (i = 0; i < 4; i++)
      force dut.u_aes_core.iv_q[i] = iv[127 - i*32 -: 32];
  endtask

  task force_gcm_ctrl(
    input gcm_phase_e      phase,
    input logic [4:0]      num_valid_bytes
  );
    force dut.u_aes_core.gcm_phase_q       = phase;
    force dut.u_aes_core.num_valid_bytes_q = num_valid_bytes;
  endtask

  task force_data_in(input logic [127:0] data);
    static int i;
    for (i = 0; i < 4; i++)
      force dut.u_aes_core.data_in[i] = data[127 - i*32 -: 32];
  endtask

  task pulse_start();
    @(posedge clk_tb);
    force dut.reg2hw.trigger.start.q = 1'b1;
    @(posedge clk_tb);
    release dut.reg2hw.trigger.start.q;
  endtask

  task read_data_out(output logic [127:0] data);
    static int i;
    for (i = 0; i < 4; i++)
      data[127 - i*32 -: 32] = dut.u_aes_core.data_out_q[i];
  endtask

  // --- Release tasks ---

  task release_ctrl();
    release dut.u_aes_core.aes_mode_q;
    release dut.u_aes_core.aes_op_q;
    release dut.u_aes_core.key_len_q;
    release dut.u_aes_core.manual_operation_q;
  endtask

  task release_key();
    static int i;
    for (i = 0; i < 8; i++) begin
      release dut.u_aes_core.key_init_q[i][0];
      release dut.u_aes_core.key_init_q[i][1];
    end
  endtask

  task release_iv();
    static int i;
    for (i = 0; i < 4; i++)
      release dut.u_aes_core.iv_q[i];
  endtask

  task release_gcm_ctrl();
    release dut.u_aes_core.gcm_phase_q;
    release dut.u_aes_core.num_valid_bytes_q;
  endtask

  task release_data_in();
    static int i;
    for (i = 0; i < 4; i++)
      release dut.u_aes_core.data_in[i];
  endtask

  //================================================================
  // Step 2 — aes_run: multi-block ECB / CBC / CTR
  //
  // Follows the Programmer's Guide sequence for N blocks.
  // For CBC/CTR, the IV is forced only for block 0; from block 1
  // onward the force is released so the DUT can auto-update iv_q.
  //================================================================
  task aes_run(
    input  aes_mode_e     mode,
    input  aes_op_e       op,
    input  key_len_e      key_len,
    input  logic [255:0]  key,
    input  logic [127:0]  iv,
    input  logic [127:0]  data_in[],   // dynamic array, N elements
    output logic [127:0]  data_out[]
  );
    int N;
    N        = data_in.size();
    data_out = new[N];

    wait_idle();
    force_ctrl(mode, op, key_len);
    force_key(key);
    if (mode != AES_ECB) force_iv(iv);

    for (int blk = 0; blk < N; blk++) begin
      // Release IV after block 0 so the DUT owns it for CBC/CTR chaining
      if (blk == 1 && mode != AES_ECB) release_iv();

      wait_input_ready();
      force_data_in(data_in[blk]);
      pulse_start();
      wait_output_valid();
      read_data_out(data_out[blk]);
      $display("[TB] Block %0d: %032h", blk, data_out[blk]);
    end

    release_ctrl();
    release_key();
    // release_iv() is safe even if already released after block 0
    if (mode != AES_ECB) release_iv();
    release_data_in();
  endtask

  //================================================================
  // Step 3 — aes_gcm: GCM encrypt (INIT → AAD → TEXT → TAG)
  //
  // GCM phase enum values (aes_pkg.sv):
  //   GCM_INIT=6'h01, GCM_RESTORE=6'h02, GCM_AAD=6'h04,
  //   GCM_TEXT=6'h08, GCM_SAVE=6'h10,    GCM_TAG=6'h20
  //================================================================
  task aes_gcm(
    input  key_len_e      key_len,
    input  logic [255:0]  key,
    input  logic [95:0]   nonce,           // 96-bit GCM IV/nonce
    input  logic [127:0]  aad[],           // AAD blocks (dynamic array)
    input  logic [4:0]    aad_last_bytes,  // valid bytes in last AAD block (1–16)
    input  logic [127:0]  plaintext[],     // plaintext blocks
    input  logic [4:0]    text_last_bytes, // valid bytes in last PT block (1–16)
    output logic [127:0]  ciphertext[],
    output logic [127:0]  tag
  );
    int N_aad;
    int N_text;
    logic [4:0] nbytes;

    N_aad      = aad.size();
    N_text     = plaintext.size();
    ciphertext = new[N_text];

    // ---- GCM_INIT: derive hash subkey H ----
    wait_idle();
    force_ctrl(AES_GCM, AES_ENC, key_len);
    force_key(key);
    force_gcm_ctrl(GCM_INIT, 5'd16);
    force_iv({nonce, 32'h0});   // counter = 0 → encrypt zero block → H
    force_data_in(128'h0);
    pulse_start();
    wait_output_valid();
    // DATA_OUT not captured; GHASH unit loads H internally

    // ---- GCM_AAD: process additional authenticated data ----
    for (int i = 0; i < N_aad; i++) begin
      nbytes = (i == N_aad-1) ? aad_last_bytes : 5'd16;
      force_gcm_ctrl(GCM_AAD, nbytes);
      wait_input_ready();
      force_data_in(aad[i]);
      pulse_start();
      wait_output_valid();
    end

    // ---- GCM_TEXT: encrypt plaintext blocks ----
    // Provide the first CTR block (counter=1); DUT increments thereafter.
    force_iv({nonce, 32'h1});
    @(posedge clk_tb);
    release_iv();

    for (int i = 0; i < N_text; i++) begin
      nbytes = (i == N_text-1) ? text_last_bytes : 5'd16;
      force_gcm_ctrl(GCM_TEXT, nbytes);
      wait_input_ready();
      force_data_in(plaintext[i]);
      pulse_start();
      wait_output_valid();
      read_data_out(ciphertext[i]);
      $display("[TB] GCM block %0d CT: %032h", i, ciphertext[i]);
    end

    // ---- GCM_TAG: finalize authentication tag ----
    force_gcm_ctrl(GCM_TAG, 5'd16);
    pulse_start();
    wait_output_valid();
    read_data_out(tag);
    $display("[TB] GCM tag: %032h", tag);

    release_ctrl();
    release_key();
    release_gcm_ctrl();
    release_data_in();
  endtask

  //================================================================
  // Step 4 — Main test sequence
  //   Four test vectors covering ECB, CBC, CTR, and GCM.
  //================================================================
  initial begin : main
    // ECB result (single block, scalar)
    logic [127:0] ecb_result;

    // CBC / CTR: dynamic arrays (one block each for quick check)
    logic [127:0] cbc_in[];
    logic [127:0] cbc_out[];
    logic [127:0] ctr_in[];
    logic [127:0] ctr_out[];

    // GCM: no AAD, single plaintext block
    logic [127:0] gcm_aad[];
    logic [127:0] gcm_pt[];
    logic [127:0] gcm_ct[];
    logic [127:0] gcm_tag;

    $display("[TB] aes_tb started");

    init_sim();
    reset_dut();

    // Disable key-touch-triggered PRNG reseed to avoid hundreds of stall cycles
    // every time force_key() is called. The signal is driven by a shadowed register
    // that is never written via TLUL in this testbench, so the force is safe to leave
    // permanently asserted throughout the simulation.
    force dut.u_aes_core.key_touch_forces_reseed = 1'b0;

    // ------------------------------------------------------------------
    // Test 1: ECB-AES-128 encrypt — FIPS 197 Appendix B
    //   Key:       000102030405060708090a0b0c0d0e0f
    //   Plaintext: 00112233445566778899aabbccddeeff
    //   Expected:  69c4e0d86a7b04300d8a1c30b5a2ab83
    // ------------------------------------------------------------------
    $display("[TB] ---- Test 1: ECB-AES-128 (FIPS 197 App.B) ----");
    begin
      logic [127:0] ecb_din[];
      logic [127:0] ecb_dout[];
      ecb_din    = new[1];
      ecb_din[0] = 128'h00112233445566778899aabbccddeeff;
      aes_run(
        AES_ECB,
        AES_ENC,
        AES_128,
        256'h000102030405060708090a0b0c0d0e0f_00000000000000000000000000000000,
        128'h0,
        ecb_din,
        ecb_dout
      );
      ecb_result = ecb_dout[0];
    end
    $display("[TB] ECB Expected: 69c4e0d86a7b04300d8a1c30b5a2ab83");
    $display("[TB] ECB Got:      %032h", ecb_result);
    if (ecb_result === 128'h69c4e0d86a7b04300d8a1c30b5a2ab83)
      $display("[TB] ECB PASS");
    else
      $display("[TB] ECB FAIL");

    // ------------------------------------------------------------------
    // Test 2: CBC-AES-128 encrypt — NIST SP 800-38A §F.2.1, block 1
    //   Key: 2b7e151628aed2a6abf7158809cf4f3c
    //   IV:  000102030405060708090a0b0c0d0e0f
    //   PT:  6bc1bee22e409f96e93d7e117393172a
    //   Expected CT block 1: 7649abac8119b246cee98e9b12e9197d
    // ------------------------------------------------------------------
    $display("[TB] ---- Test 2: CBC-AES-128 (NIST SP 800-38A F.2.1) ----");
    cbc_in    = new[1];
    cbc_in[0] = 128'h6bc1bee22e409f96e93d7e117393172a;
    aes_run(
      AES_CBC,
      AES_ENC,
      AES_128,
      256'h2b7e151628aed2a6abf7158809cf4f3c_00000000000000000000000000000000,
      128'h000102030405060708090a0b0c0d0e0f,
      cbc_in,
      cbc_out
    );
    $display("[TB] CBC Expected: 7649abac8119b246cee98e9b12e9197d");
    $display("[TB] CBC Got:      %032h", cbc_out[0]);
    if (cbc_out[0] === 128'h7649abac8119b246cee98e9b12e9197d)
      $display("[TB] CBC PASS");
    else
      $display("[TB] CBC FAIL");

    // ------------------------------------------------------------------
    // Test 3: CTR-AES-128 encrypt — NIST SP 800-38A §F.5.1, block 1
    //   Key: 2b7e151628aed2a6abf7158809cf4f3c
    //   IV (initial counter): f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff
    //   PT:  6bc1bee22e409f96e93d7e117393172a
    //   Expected CT block 1: 874d6191b620e3261bef6864990db6ce
    // ------------------------------------------------------------------
    $display("[TB] ---- Test 3: CTR-AES-128 (NIST SP 800-38A F.5.1) ----");
    ctr_in    = new[1];
    ctr_in[0] = 128'h6bc1bee22e409f96e93d7e117393172a;
    aes_run(
      AES_CTR,
      AES_ENC,
      AES_128,
      256'h2b7e151628aed2a6abf7158809cf4f3c_00000000000000000000000000000000,
      128'hf0f1f2f3f4f5f6f7f8f9fafbfcfdfeff,
      ctr_in,
      ctr_out
    );
    $display("[TB] CTR Expected: 874d6191b620e3261bef6864990db6ce");
    $display("[TB] CTR Got:      %032h", ctr_out[0]);
    if (ctr_out[0] === 128'h874d6191b620e3261bef6864990db6ce)
      $display("[TB] CTR PASS");
    else
      $display("[TB] CTR FAIL");

/*    // ------------------------------------------------------------------
    // Test 4: GCM-AES-128 encrypt — NIST SP 800-38D Test Case 2
    //   Key:    00000000000000000000000000000000
    //   Nonce:  000000000000000000000000 (96-bit)
    //   AAD:    (empty)
    //   PT:     00000000000000000000000000000000
    //   Expected CT:  0388dace60b6a392f328c2b971b2fe78
    //   Expected tag: ab6e47d42cec13bdf53a67b21257bddf
    // ------------------------------------------------------------------
    $display("[TB] ---- Test 4: GCM-AES-128 (NIST SP 800-38D TC2) ----");
    gcm_aad   = new[0];   // no AAD
    gcm_pt    = new[1];
    gcm_pt[0] = 128'h00000000000000000000000000000000;
    aes_gcm(
      AES_128,
      256'h00000000000000000000000000000000_00000000000000000000000000000000,
      96'h000000000000000000000000,  // 96-bit nonce
      gcm_aad,
      5'd16,                        // aad_last_bytes (unused — no AAD)
      gcm_pt,
      5'd16,                        // text_last_bytes
      gcm_ct,
      gcm_tag
    );
    $display("[TB] GCM CT  Expected: 0388dace60b6a392f328c2b971b2fe78");
    $display("[TB] GCM CT  Got:      %032h", gcm_ct[0]);
    $display("[TB] GCM Tag Expected: ab6e47d42cec13bdf53a67b21257bddf");
    $display("[TB] GCM Tag Got:      %032h", gcm_tag);
    if (gcm_ct[0] === 128'h0388dace60b6a392f328c2b971b2fe78)
      $display("[TB] GCM CT  PASS");
    else
      $display("[TB] GCM CT  FAIL");
    if (gcm_tag === 128'hab6e47d42cec13bdf53a67b21257bddf)
      $display("[TB] GCM Tag PASS");
    else
      $display("[TB] GCM Tag FAIL");*/

    $display("[TB] aes_tb done");
    $finish;
  end

endmodule : aes_tb

//======================================================================
// EOF aes_tb.sv
//======================================================================
