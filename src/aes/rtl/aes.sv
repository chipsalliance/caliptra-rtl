// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES top-level wrapper

`include "caliptra_prim_assert.sv"

module aes
  import aes_pkg::*;
  import aes_reg_pkg::*;
#(
  parameter bit          AES192Enable          = 1, // Can be 0 (disable), or 1 (enable).
  parameter bit          AESGCMEnable          = 1, // Can be 0 (disable), or 1 (enable).
  parameter bit          SecMasking            = 1, // Can be 0 (no masking), or
                                                    // 1 (first-order masking) of the cipher
                                                    // core. Masking requires the use of a
                                                    // masked S-Box, see SecSBoxImpl parameter.
  parameter sbox_impl_e  SecSBoxImpl           = SBoxImplDom, // See aes_pkg.sv
  parameter int unsigned SecStartTriggerDelay  = 0, // Manual start trigger delay, useful for
                                                    // SCA measurements. A value of e.g. 40
                                                    // allows the processor to go into sleep
                                                    // before AES starts operation.
  parameter bit          SecAllowForcingMasks  = 0, // Allow forcing masks to constant values using
                                                    // FORCE_MASKS bit in Auxiliary Control
                                                    // Register. Useful for SCA only.
  parameter bit          SecSkipPRNGReseeding  = 0, // The current SCA setup doesn't provide enough
                                                    // resources to implement the infrastucture
                                                    // required for PRNG reseeding (CSRNG, EDN).
                                                    // To enable SCA resistance evaluations, we
                                                    // need to skip reseeding requests.
                                                    // Useful for SCA only.
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  parameter clearing_lfsr_seed_t RndCnstClearingLfsrSeed  = RndCnstClearingLfsrSeedDefault,
  parameter clearing_lfsr_perm_t RndCnstClearingLfsrPerm  = RndCnstClearingLfsrPermDefault,
  parameter clearing_lfsr_perm_t RndCnstClearingSharePerm = RndCnstClearingSharePermDefault,
  parameter masking_lfsr_seed_t  RndCnstMaskingLfsrSeed   = RndCnstMaskingLfsrSeedDefault,
  parameter masking_lfsr_perm_t  RndCnstMaskingLfsrPerm   = RndCnstMaskingLfsrPermDefault
) (
  input  logic                                      clk_i,
  input  logic                                      rst_ni,
  input  logic                                      rst_shadowed_ni,

  // Idle indicator for clock manager
  output caliptra_prim_mubi_pkg::mubi4_t                     idle_o,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t                       lc_escalate_en_i,

  // Entropy distribution network (EDN) interface
  input  logic                                      clk_edn_i,
  input  logic                                      rst_edn_ni,
  output edn_pkg::edn_req_t                         edn_o,
  input  edn_pkg::edn_rsp_t                         edn_i,
  
  // status signals
  output logic input_ready_o,
  output logic output_valid_o,

  // Caliptra interface
  input  caliptra2aes_t caliptra2aes,
  output aes2caliptra_t aes2caliptra,


  // Key manager (keymgr) key sideload interface
  input  keymgr_pkg::hw_key_req_t                   keymgr_key_i,

  // Bus interface
  input  caliptra_tlul_pkg::tl_h2d_t                         tl_i,
  output caliptra_tlul_pkg::tl_d2h_t                         tl_o,

  // Alerts
  input  caliptra_prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output caliptra_prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o
);

  localparam int unsigned EntropyWidth = edn_pkg::ENDPOINT_BUS_WIDTH;

  // Signals
  aes_reg2hw_t               reg2hw;
  aes_hw2reg_t               hw2reg;

  logic      [NumAlerts-1:0] alert;
  lc_ctrl_pkg::lc_tx_t       lc_escalate_en;

  logic                      edn_req_int;
  logic                      edn_req_hold_d, edn_req_hold_q;
  logic                      edn_req;
  logic                      edn_ack;
  logic   [EntropyWidth-1:0] edn_data;
  logic                      unused_edn_fips;
  logic                      entropy_clearing_req, entropy_masking_req;
  logic                      entropy_clearing_ack, entropy_masking_ack;

  ////////////
  // Inputs //
  ////////////

  // SEC_CM: BUS.INTEGRITY
  // SEC_CM: AUX.CONFIG.SHADOW
  // SEC_CM: AUX.CONFIG.REGWEN
  // SEC_CM: KEY.SW_UNREADABLE
  // SEC_CM: DATA_REG.SW_UNREADABLE
  // Register interface
  logic intg_err_alert;
  logic shadowed_storage_err, shadowed_update_err;
  aes_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni,
    .tl_i,
    .tl_o,
    .input_ready_o,
    .output_valid_o,
    .reg2hw,
    .hw2reg,
    .shadowed_storage_err_o(shadowed_storage_err),
    .shadowed_update_err_o(shadowed_update_err),
    .intg_err_o(intg_err_alert)
  );

  // SEC_CM: LC_ESCALATE_EN.INTERSIG.MUBI
  // Synchronize life cycle input
  caliptra_prim_lc_sync #(
    .NumCopies (1)
  ) u_caliptra_prim_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i ( lc_escalate_en_i ),
    .lc_en_o ( {lc_escalate_en} )
  );

  ////////////////////////////////
  // Caliptra Control Intercept //
  ////////////////////////////////
  localparam CLP_AES_KV_CHUNK_SIZE = NumRegsData*32; // Size of data that can be stored at once, atomically, at end of AES op
  genvar kv_ii;

  aes_hw2reg_t hw2reg_caliptra;
  aes_reg2hw_t reg2hw_caliptra;
  logic                        aes2caliptra_kv_data_out_valid;
  logic [CLP_AES_KV_WR_DW-1:0] aes2caliptra_kv_data_out;
  logic kv_data_intercept;
  logic kv_data_intercept_end;
  logic [$clog2(CLP_AES_KV_WR_DW/CLP_AES_KV_CHUNK_SIZE)-1:0] kv_data_counter; // This will peg at the key_size value if decrypted plaintext is larger than CLP_AES_KV_WR_DW
  logic [$clog2(CLP_AES_KV_WR_DW/CLP_AES_KV_CHUNK_SIZE)-1:0] kv_data_thresh; // Comparison value for kv_data_counter to saturate, i.e. the key_size normalized to data chunk size
  logic incr_kv_data_counter;
  logic hw2reg_data_out_mask_en;
  logic [$bits(aes_hw2reg_data_out_mreg_t)-1:0] hw2reg_data_out_mask;
  logic output_blocked_de;
  logic output_valid_r;

  // Mask to conceal data_out from reg API (when dest is KV)
  assign hw2reg_data_out_mask = {$bits(aes_hw2reg_data_out_mreg_t){hw2reg_data_out_mask_en}};

  // Enable signal to drive an update to the status.output_lost register field
  always_comb output_blocked_de = hw2reg_caliptra.status.output_valid.de &&
                                  hw2reg_caliptra.status.output_valid.d  &&
                                  caliptra2aes.block_reg_output;

  always_comb begin
      // Passthrough
      hw2reg                                    = hw2reg_caliptra;
      // Augmented
      // For OCP LOCK use-cases, add a condition to set output_lost if output data is required to go to KV.
      // Output Lost is usually only used for Manual mode. TODO if we support manual mode with OCP LOCK flows (and KV WR) this may
      // need to be updated.
      hw2reg.status.output_lost.d               = output_blocked_de ? 1'b1 :
                                                                      hw2reg_caliptra.status.output_lost.d;
      hw2reg.status.output_lost.de              = hw2reg_caliptra.status.output_lost.de ||
                                                  output_blocked_de;
      // Concealed
      foreach (hw2reg.data_out[idx]) begin
      hw2reg.data_out[idx].d                    = hw2reg_caliptra.data_out[idx].d & hw2reg_data_out_mask;
      end
  end
  always_comb begin
      // Passthrough
      reg2hw_caliptra                   = reg2hw;
      // RE intercept
      foreach (reg2hw.data_out[idx]) begin
      reg2hw_caliptra.data_out[idx].q   = reg2hw.data_out[idx].q  ;
      reg2hw_caliptra.data_out[idx].re  = kv_data_intercept ? output_valid_r :
                                                              reg2hw.data_out[idx].re;
      end
  end

  // Flag to detect when data out shall be routed to Caliptra KeyVault
  always_ff @(posedge clk_i or negedge rst_ni) begin: kv_data_intercept_reg
      if (!rst_ni) begin
          kv_data_intercept       <= 1'b0;
          hw2reg_data_out_mask_en <= 1'b1;
      end
      // FW must arm the KV write prior to starting AES operation
      else if ((kv_data_counter == 0) && reg2hw_caliptra.data_in[0].qe) begin
          kv_data_intercept       <=  caliptra2aes.kv_en;
          hw2reg_data_out_mask_en <= ~caliptra2aes.kv_en && ~caliptra2aes.block_reg_output; // This signal winds up being effectively (~kv_data_intercept && ~caliptra2aes.block_reg_output)
      end
      // TODO support for Manual operation mode with trigger.start.q?
      else if (kv_data_intercept_end) begin
          kv_data_intercept       <= 1'b0;
          hw2reg_data_out_mask_en <= 1'b1;
      end
  end

  // NOTE if key size is not an integer multiple of CLP_AES_KV_CHUNK_SIZE, this is a rounded down value
  always_comb kv_data_thresh = ($clog2(CLP_AES_KV_WR_DW/CLP_AES_KV_CHUNK_SIZE))'(caliptra2aes.key_release_key_size/(CLP_AES_KV_CHUNK_SIZE/8)-1);
  // NOTE: This assumes that output_valid will always assert prior to entering idle state, which should be true.
  //       If this doesn't hold, then kv_data_intercept will deassert before the final data beat is captured, and
  //       the KV write won't be issued
  always_comb kv_data_intercept_end = hw2reg.status.idle.de && hw2reg.status.idle.d && !reg2hw_caliptra.status.idle.q && (kv_data_counter == kv_data_thresh);

  // Latch when data_out is valid, used to generate read-enable and signal data capture
  always_ff @(posedge clk_i or negedge rst_ni) begin: output_valid_dd_reg
      if (!rst_ni) begin
          output_valid_r <= 1'b0;
      end
      else if (hw2reg_caliptra.status.output_valid.de) begin
          output_valid_r <= hw2reg_caliptra.status.output_valid.d;
      end
  end

  // Index into the KV output data based on number of AES rounds observed
  always_comb incr_kv_data_counter = kv_data_intercept && output_valid_r;
  always_ff @(posedge clk_i or negedge rst_ni) begin: aes2caliptra_kv_data_counter_reg
      if (!rst_ni) begin
          kv_data_counter <= '0;
      end
      else if (!kv_data_intercept) begin
          kv_data_counter <= '0;
      end
      else if (incr_kv_data_counter && (kv_data_counter == kv_data_thresh)) begin
          kv_data_counter <= kv_data_counter;
      end
      else if (incr_kv_data_counter) begin
          kv_data_counter <= kv_data_counter + 1;
      end
  end

  // Signal data is valid for KV write client once full AES operation is done
  always_ff @(posedge clk_i or negedge rst_ni) begin: aes2caliptra_kv_data_valid_reg
      if (!rst_ni) begin
          aes2caliptra_kv_data_out_valid <= 1'b0;
      end
      else if (caliptra2aes.clear_secrets || reg2hw_caliptra.trigger.data_out_clear.q) begin
          aes2caliptra_kv_data_out_valid <= 1'b0;
      end
      else if (kv_data_intercept_end) begin
          aes2caliptra_kv_data_out_valid <= 1'b1;
      end
      else if (caliptra2aes.kv_write_done) begin
          aes2caliptra_kv_data_out_valid <= 1'b0;
      end
  end
  assign aes2caliptra.kv_data_out_valid = aes2caliptra_kv_data_out_valid;
  assign aes2caliptra.kv_key_in_use = hw2reg.ctrl_shadowed.sideload.d;
  // TODO: Qualify this with anything?
  //       Probably not needed. Timing of the kv write request is tightly controlled, and that's the only
  //       place this signal is used.
  always_comb aes2caliptra.aes_operation_is_ecb_decrypt = (  aes_op_e'(hw2reg.ctrl_shadowed.operation.d)     == AES_DEC) &&
                                                          (aes_mode_e'(hw2reg.ctrl_shadowed.mode.d)          == AES_ECB);

  // Capture data_out until operation is done
  generate
      for (kv_ii=0; kv_ii < CLP_AES_KV_WR_DW/CLP_AES_KV_CHUNK_SIZE; kv_ii++) begin
          always_ff @(posedge clk_i or negedge rst_ni) begin: aes2caliptra_kv_data_reg
              if (!rst_ni) begin
                  aes2caliptra_kv_data_out[(kv_ii)*CLP_AES_KV_CHUNK_SIZE+:CLP_AES_KV_CHUNK_SIZE] <= CLP_AES_KV_CHUNK_SIZE'(0);
              end
              else if ((caliptra2aes.clear_secrets) || reg2hw_caliptra.trigger.data_out_clear.q) begin
                  aes2caliptra_kv_data_out[(kv_ii)*CLP_AES_KV_CHUNK_SIZE+:CLP_AES_KV_CHUNK_SIZE] <= CLP_AES_KV_CHUNK_SIZE'(0);
              end
              else if (incr_kv_data_counter && (kv_data_counter == kv_ii)) begin
                  aes2caliptra_kv_data_out[(kv_ii)*CLP_AES_KV_CHUNK_SIZE+:CLP_AES_KV_CHUNK_SIZE] <= {hw2reg_caliptra.data_out[3].d,
                                                                                                     hw2reg_caliptra.data_out[2].d,
                                                                                                     hw2reg_caliptra.data_out[1].d,
                                                                                                     hw2reg_caliptra.data_out[0].d};
              end
              else if (caliptra2aes.kv_write_done) begin
                  aes2caliptra_kv_data_out[(kv_ii)*CLP_AES_KV_CHUNK_SIZE+:CLP_AES_KV_CHUNK_SIZE] <= CLP_AES_KV_CHUNK_SIZE'(0);
              end
          end
      end
  endgenerate
  assign aes2caliptra.kv_data_out = aes2caliptra_kv_data_out;

  ///////////////////
  // EDN Interface //
  ///////////////////

  // Internally, we have up to two PRNGs that share the EDN interface for reseeding. Here, we just
  // arbitrate the requests. Upsizing of the entropy to the correct width is performed inside the
  // PRNGs.
  // Reseed operations for the clearing PRNG are initiated by software. Reseed operations for the
  // masking PRNG can also be automatically initiated.
  assign edn_req_int          = entropy_clearing_req | entropy_masking_req;
  // Only forward ACK to PRNG currently requesting entropy. Give higher priority to clearing PRNG.
  assign entropy_clearing_ack =  entropy_clearing_req & edn_ack;
  assign entropy_masking_ack  = ~entropy_clearing_req & entropy_masking_req & edn_ack;

  // Upon escalation or detection of a fatal alert, an EDN request signal can be dropped before
  // getting acknowledged. This is okay with respect to AES as the module will need to be reset
  // anyway. However, to not leave EDN in a strange state, we hold the request until it's actually
  // acknowledged.
  assign edn_req        = edn_req_int | edn_req_hold_q;
  assign edn_req_hold_d = (edn_req_hold_q | edn_req) & ~edn_ack;
  always_ff @(posedge clk_i or negedge rst_ni) begin : edn_req_reg
    if (!rst_ni) begin
      edn_req_hold_q <= '0;
    end else begin
      edn_req_hold_q <= edn_req_hold_d;
    end
  end

  // Synchronize EDN interface
  caliptra_prim_sync_reqack_data #(
    .Width(EntropyWidth),
    .DataSrc2Dst(1'b0),
    .DataReg(1'b0)
  ) u_caliptra_prim_sync_reqack_data (
    .clk_src_i  ( clk_i         ),
    .rst_src_ni ( rst_ni        ),
    .clk_dst_i  ( clk_edn_i     ),
    .rst_dst_ni ( rst_edn_ni    ),
    .req_chk_i  ( 1'b1          ),
    .src_req_i  ( edn_req       ),
    .src_ack_o  ( edn_ack       ),
    .dst_req_o  ( edn_o.edn_req ),
    .dst_ack_i  ( edn_i.edn_ack ),
    .data_i     ( edn_i.edn_bus ),
    .data_o     ( edn_data      )
  );
  // We don't track whether the entropy is pre-FIPS or not inside AES.
  assign unused_edn_fips = edn_i.edn_fips;

  //////////
  // Core //
  //////////

  // AES core
  aes_core #(
    .AES192Enable             ( AES192Enable             ),
    .AESGCMEnable             ( AESGCMEnable             ),
    .SecMasking               ( SecMasking               ),
    .SecSBoxImpl              ( SecSBoxImpl              ),
    .SecStartTriggerDelay     ( SecStartTriggerDelay     ),
    .SecAllowForcingMasks     ( SecAllowForcingMasks     ),
    .SecSkipPRNGReseeding     ( SecSkipPRNGReseeding     ),
    .EntropyWidth             ( EntropyWidth             ),
    .RndCnstClearingLfsrSeed  ( RndCnstClearingLfsrSeed  ),
    .RndCnstClearingLfsrPerm  ( RndCnstClearingLfsrPerm  ),
    .RndCnstClearingSharePerm ( RndCnstClearingSharePerm ),
    .RndCnstMaskingLfsrSeed   ( RndCnstMaskingLfsrSeed   ),
    .RndCnstMaskingLfsrPerm   ( RndCnstMaskingLfsrPerm   )
  ) u_aes_core (
    .clk_i                  ( clk_i                ),
    .rst_ni                 ( rst_ni               ),
    .rst_shadowed_ni        ( rst_shadowed_ni      ),
    .entropy_clearing_req_o ( entropy_clearing_req ),
    .entropy_clearing_ack_i ( entropy_clearing_ack ),
    .entropy_clearing_i     ( edn_data             ),
    .entropy_masking_req_o  ( entropy_masking_req  ),
    .entropy_masking_ack_i  ( entropy_masking_ack  ),
    .entropy_masking_i      ( edn_data             ),

    .keymgr_key_i           ( keymgr_key_i         ),

    .lc_escalate_en_i       ( lc_escalate_en       ),

    .shadowed_storage_err_i ( shadowed_storage_err ),
    .shadowed_update_err_i  ( shadowed_update_err  ),
    .intg_err_alert_i       ( intg_err_alert       ),
    .alert_recov_o          ( alert[0]             ),
    .alert_fatal_o          ( alert[1]             ),

    .reg2hw                 ( reg2hw_caliptra      ),
    .hw2reg                 ( hw2reg_caliptra      )
  );

  assign idle_o = caliptra_prim_mubi_pkg::mubi4_bool_to_mubi(reg2hw.status.idle.q);


  ////////////
  // Alerts //
  ////////////

  logic [NumAlerts-1:0] alert_test;
  assign alert_test = {
    reg2hw.alert_test.fatal_fault.q &
    reg2hw.alert_test.fatal_fault.qe,
    reg2hw.alert_test.recov_ctrl_update_err.q &
    reg2hw.alert_test.recov_ctrl_update_err.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    caliptra_prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(i)
    ) u_caliptra_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alert[i]      ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  ////////////////
  // Assertions //
  ////////////////

  // All outputs should have a known value after reset
  `CALIPTRA_ASSERT_KNOWN(TlODValidKnown, tl_o.d_valid)
  `CALIPTRA_ASSERT_KNOWN(TlOAReadyKnown, tl_o.a_ready)
  `CALIPTRA_ASSERT_KNOWN(IdleKnown, idle_o)
  `CALIPTRA_ASSERT_KNOWN(EdnReqKnown, edn_o)
  `CALIPTRA_ASSERT_KNOWN(AlertTxKnown, alert_tx_o)

  // Alert assertions for sparse FSMs.
  for (genvar i = 0; i < Sp2VWidth; i++) begin : gen_control_fsm_svas
    if (SP2V_LOGIC_HIGH[i] == 1'b1) begin : gen_control_fsm_svas_p
      `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesControlFsmCheck_A,
          u_aes_core.u_aes_control.gen_fsm[i].gen_fsm_p.
              u_aes_control_fsm_i.u_aes_control_fsm.u_state_regs,
          alert_tx_o[1])
    end else begin : gen_control_fsm_svas_n
      `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesControlFsmCheck_A,
          u_aes_core.u_aes_control.gen_fsm[i].gen_fsm_n.
              u_aes_control_fsm_i.u_aes_control_fsm.u_state_regs,
          alert_tx_o[1])
    end
  end

  for (genvar i = 0; i < Sp2VWidth; i++) begin : gen_ctr_fsm_svas
    if (SP2V_LOGIC_HIGH[i] == 1'b1) begin : gen_ctr_fsm_svas_p
      `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesCtrFsmCheck_A,
          u_aes_core.u_aes_ctr.gen_fsm[i].gen_fsm_p.
              u_aes_ctr_fsm_i.u_aes_ctr_fsm.u_state_regs,
          alert_tx_o[1])
    end else begin : gen_ctr_fsm_svas_n
      `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesCtrFsmCheck_A,
          u_aes_core.u_aes_ctr.gen_fsm[i].gen_fsm_n.
              u_aes_ctr_fsm_i.u_aes_ctr_fsm.u_state_regs,
          alert_tx_o[1])
    end
  end

  for (genvar i = 0; i < Sp2VWidth; i++) begin : gen_cipher_control_fsm_svas
    if (SP2V_LOGIC_HIGH[i] == 1'b1) begin : gen_cipher_control_fsm_svas_p
      `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesCipherControlFsmCheck_A,
          u_aes_core.u_aes_cipher_core.u_aes_cipher_control.gen_fsm[i].gen_fsm_p.
              u_aes_cipher_control_fsm_i.u_aes_cipher_control_fsm.u_state_regs,
          alert_tx_o[1])
    end else begin : gen_cipher_control_fsm_svas_n
      `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesCipherControlFsmCheck_A,
          u_aes_core.u_aes_cipher_core.u_aes_cipher_control.gen_fsm[i].gen_fsm_n.
              u_aes_cipher_control_fsm_i.u_aes_cipher_control_fsm.u_state_regs,
          alert_tx_o[1])
    end
  end

  if (AESGCMEnable) begin : gen_ghash_fsm_sva
    `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(AesGhashFsmCheck_A,
        u_aes_core.gen_ghash.u_aes_ghash.u_state_regs,
        alert_tx_o[1])
  end

  if (AESGCMEnable && SecMasking) begin : gen_ghash_onehot_sva
    for (genvar s = 0; s < 2; s++) begin : gen_ghash_onehot_add_in_sva
      `CALIPTRA_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ALERT(GhashAadOnehotCheck_A,
          u_aes_core.gen_ghash.u_aes_ghash.gen_masked_add.gen_add_in_muxes[s].
              u_caliptra_prim_onehot_check_add_in_sel,
          alert_tx_o[1])
    end
    `CALIPTRA_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ALERT(GhashMultOnehotCheck_A,
        u_aes_core.gen_ghash.u_aes_ghash.gen_gf_mult1_mux.u_caliptra_prim_onehot_check_gf_mult1_in_sel,
        alert_tx_o[1])
  end

  // Alert assertions for reg_we onehot check
  `CALIPTRA_ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[1])
endmodule
