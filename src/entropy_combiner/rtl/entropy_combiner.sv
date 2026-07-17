// SPDX-License-Identifier: Apache-2.0
//
// SHA3-384 entropy combiner for dual entropy_src instances.
//
// In bypass mode (`combine_en_i == 0`), the combiner is transparent: CSRNG's
// entropy_src_hw_if request is forwarded to ES0 and ES0's response is returned
// directly, while ES1 remains quiescent. In combine mode, one CSRNG request is
// fanned out to ES0 and ES1, both 384b responses are latched, ES0||ES1 forms a
// 768b SHA3-384 message (one block because 768 < the 832b SHA3-384 rate), and
// the 384b digest is returned to CSRNG with a clean one-cycle ack.
//
// The AHB port exposes a purpose-built minimal KAT register map plus combiner
// policy registers from entropy_combiner_reg.rdl. ROM can run a power-on KAT by
// writing up to 96 bytes into KAT_MSG, programming beat-aligned KAT_MSG_LEN,
// and pulsing KAT_CTRL.start; hardware hashes that bounded single-block message
// through the same ot_sha3 gates used operationally and exposes the digest through
// KAT_DIGEST. After KAT, ROM sets the W1S AHB_LOCK bit. `ahb_lock_o` is driven
// from that W1S register; this module silently ignores later AHB accesses so
// runtime firmware cannot read combiner state.

`include "caliptra_prim_assert.sv"

module entropy_combiner
  import entropy_src_pkg::*;
  import ot_sha3_pkg::*;
  import caliptra_prim_mubi_pkg::*;
  import entropy_combiner_pkg::*;
  import entropy_combiner_reg_pkg::*;
#(
  parameter AHB_DATA_WIDTH = 32,
  parameter AHB_ADDR_WIDTH = 32
) (
  input wire clk,
  input wire reset_n,
  input wire cptra_pwrgood_i,

  input entropy_src_hw_if_req_t csrng_hw_if_req_i,
  output entropy_src_hw_if_rsp_t csrng_hw_if_rsp_o,

  output entropy_src_hw_if_req_t es0_hw_if_req_o,
  input entropy_src_hw_if_rsp_t es0_hw_if_rsp_i,
  output entropy_src_hw_if_req_t es1_hw_if_req_o,
  input entropy_src_hw_if_rsp_t es1_hw_if_rsp_i,

  input logic combine_en_i,

  input logic [AHB_ADDR_WIDTH-1:0] haddr_i,
  input logic [AHB_DATA_WIDTH-1:0] hwdata_i,
  input logic hsel_i,
  input logic hwrite_i,
  input logic hready_i,
  input logic [1:0] htrans_i,
  input logic [2:0] hsize_i,

  output logic hresp_o,
  output logic hreadyout_o,
  output logic [AHB_DATA_WIDTH-1:0] hrdata_o,

  output logic error_intr_o,
  output logic notif_intr_o,
  output logic ahb_lock_o
);

  localparam int unsigned seed_width = entropy_src_pkg::CSRNG_BUS_WIDTH;
  localparam int unsigned combine_msg_width = 2 * seed_width;
  localparam int unsigned sha3_word_width = MsgWidth;
  localparam int unsigned combine_sha3_words = combine_msg_width / sha3_word_width;
  localparam int unsigned kat_msg_words32 = combine_msg_width / 32;
  localparam int unsigned kat_digest_words32 = seed_width / 32;
  localparam logic [3:0] combine_sha3_words_c = combine_sha3_words;

  // FSM state and datapath latches. ES response latches hold each upstream seed
  // until both have arrived; KAT latches snapshot the bounded 0..96 byte message
  // and hold the digest for ROM readback until W1S AHB_LOCK zeroizes them.
  entropy_combiner_state_e state_q, state_d;

  logic op_is_kat_q, op_is_kat_d;
  logic es0_valid_q, es0_valid_d;
  logic es1_valid_q, es1_valid_d;
  logic [seed_width-1:0] es0_bits_q, es0_bits_d;
  logic [seed_width-1:0] es1_bits_q, es1_bits_d;
  logic es0_fips_q, es0_fips_d;
  logic es1_fips_q, es1_fips_d;
  logic [seed_width-1:0] digest_q, digest_d;
  logic digest_fips_q, digest_fips_d;

  logic [combine_msg_width-1:0] kat_msg_q, kat_msg_d;
  logic [seed_width-1:0] kat_digest_q, kat_digest_d;
  logic [6:0] kat_msg_len_q, kat_msg_len_d;
  logic kat_digest_valid_q, kat_digest_valid_d;

  // The static combine_en_i strap is registered inside the register block: hardware
  // continuously loads it into COMBINER_STATUS.combine_en (hw=rw) and reads it back
  // here as the single registered copy that drives the bypass/combine datapath.
  logic combine_en_status;

  logic [3:0] feed_idx_q, feed_idx_d;
  logic [3:0] feed_words_q, feed_words_d;

  logic ahb_dv;
  logic reg_req;
  logic ahb_hold;
  logic ahb_err;
  logic ahb_locked;
  logic ahb_write;
  logic [31:0] ahb_wdata;
  logic [31:0] ahb_rdata;
  logic [31:0] reg_rdata;
  logic [AHB_ADDR_WIDTH-1:0] ahb_addr;

  logic reg_rd_err;
  logic reg_wr_err;
  logic reg_rd_ack;
  logic reg_wr_ack;

  entropy_combiner_reg__in_t hwif_in;
  entropy_combiner_reg__out_t hwif_out;

  logic kat_start_cmd;
  logic kat_done_event;
  logic [31:0] kat_msg_len_value;

  logic sha3_msg_valid;
  logic [MsgWidth-1:0] sha3_msg_data [1];
  logic [MsgStrbW-1:0] sha3_msg_strb;
  logic sha3_msg_ready;
  logic sha3_start;
  logic sha3_process;
  mubi4_t sha3_done;
  mubi4_t sha3_absorbed;
  logic sha3_squeezing;
  logic sha3_block_processed;
  sha3_st_e sha3_fsm;
  logic sha3_state_valid;
  logic [StateW-1:0] sha3_state [1];
  logic sha3_run_req;
  err_t sha3_error;
  logic sha3_sparse_fsm_error;
  logic sha3_count_error;
  logic sha3_storage_rst_error;

  logic bypass_active;
  logic [MsgWidth-1:0] feed_word;
  logic feed_accept;
  logic fips_combined;
  logic [3:0] kat_feed_words;

  assign ahb_hold = 1'b0;
  assign ahb_locked = hwif_out.AHB_LOCK.lock.value;
  // ROM's W1S AHB_LOCK: after ROM finishes the KAT it sets the lock. AHB accesses
  // (reads AND writes) stay forwarded to the register block; the lock is enforced
  // by targeted, per-function gates rather than a coarse bus write-drop, so no
  // separate reg_req masking is needed:
  //   - KAT operation      : kat_start_cmd = start && !ahb_locked (no KAT can run)
  //   - KAT internal state : kat_msg_q/kat_digest_q/kat_msg_len_q/valid held 0
  //                          while locked (see always_ff), so sha3 is never fed
  //   - KAT readback       : KAT_DIGEST/KAT_STATUS.busy/valid forced 0 at hwif
  //   - FIPS policy         : COMBINER_CTRL.es_fips_policy/es_fips_cfg swwe=!lock
  //                          freezes the ROM-programmed value
  // Entropy never appears in any register (it flows ES0/ES1->ot_sha3->CSRNG), so
  // forwarding writes leaks nothing. Reads stay serviced (status/error observable)
  // and every transfer completes OKAY (ahb_hold=0).
  assign reg_req = ahb_dv;
  assign ahb_err = reg_rd_err | reg_wr_err;
  assign ahb_rdata = reg_rdata;

  assign kat_start_cmd = hwif_out.KAT_CTRL.start.value && !ahb_locked;
  assign kat_msg_len_value = hwif_out.KAT_MSG_LEN.msg_len.value;
  assign kat_feed_words = kat_msg_len_q[6:3];

  // Read the registered strap back from COMBINER_STATUS.combine_en (hw=rw) to drive
  // the datapath. When deasserted, the combiner is transparent and only ES0 is used;
  // when asserted, all CSRNG requests use the dual-ES SHA3-384 combine path.
  assign combine_en_status = hwif_out.COMBINER_STATUS.combine_en.value;
  assign bypass_active = !combine_en_status;
  // Standard Caliptra interrupt block (intr_block_rf) aggregates the sticky error
  // events (power-good/error_reset_b domain) into error_intr_o. Errors stay
  // observable regardless of the AHB lock, since the combiner keeps combining for
  // CSRNG after ROM locks the AHB. The notification interrupt (KAT-done) is only
  // meaningful during ROM time; it is disabled once ROM sets W1S AHB_LOCK so RT FW
  // is never interrupted by combiner activity.
  assign error_intr_o = hwif_out.intr_block_rf.error_global_intr_r.intr;
  assign notif_intr_o = hwif_out.intr_block_rf.notif_global_intr_r.intr && !ahb_locked;
  // KAT-done notification: single-cycle pulse when a ROM KAT digest is captured
  // (the cycle the KAT operation leaves sha_wait with a valid ot_sha3 state).
  assign kat_done_event = (state_q == combiner_st_sha_wait) && op_is_kat_q && sha3_state_valid;
  // W1S AHB_LOCK resets to 0, sets on a write-1, and clears only on reset in
  // the generated register block. Integration uses this output to disable AHB
  // reads after ROM finishes KAT.
  assign ahb_lock_o = hwif_out.AHB_LOCK.lock.value;
  assign feed_accept = sha3_msg_valid && sha3_msg_ready;

  // Combined es_fips policy is register-controlled. Reset/default is
  // AND_OF_BOTH_ES, PRIMARY_ES0_ONLY preserves ES0's FIPS bit, and CONFIG_VALUE
  // returns the programmed `es_fips_cfg` bit.
  always_comb begin
    unique case (entropy_combiner_fips_policy_e'(hwif_out.COMBINER_CTRL.es_fips_policy.value))
      fips_policy_and_both: fips_combined = es0_fips_q & es1_fips_q;
      fips_policy_es0_only: fips_combined = es0_fips_q;
      fips_policy_cfg:      fips_combined = hwif_out.COMBINER_CTRL.es_fips_cfg.value;
      default:              fips_combined = es0_fips_q & es1_fips_q;
    endcase
  end

  // SHA3 message-source mux: normal operation feeds twelve 64b beats,
  // ES0[383:0] followed by ES1[383:0]. KAT feeds a snapped KAT_MSG window for
  // KAT_MSG_LEN/8 full 64b beats. ROM is trusted to program KAT_MSG_LEN as a
  // multiple of 8 in the range 0..96.
  always_comb begin
    // feed_word is only consumed in combiner_st_sha_feed, where the valid/ready
    // handshake and the feed_words_q counter bound feed_idx_q to 0..feed_words_q-1
    // (<= 11). No range guard is needed - the FSM never indexes past the message.
    if (op_is_kat_q) begin
      feed_word = kat_msg_q[(feed_idx_q * MsgWidth) +: MsgWidth];
    end else if (feed_idx_q < 4'd6) begin // the first half of 768-bit
      feed_word = es0_bits_q[(feed_idx_q * MsgWidth) +: MsgWidth];
    end else begin // the second half of 768-bit
      feed_word = es1_bits_q[((feed_idx_q - 4'd6) * MsgWidth) +: MsgWidth];
    end
  end

  // entropy_src_hw_if bridge. In bypass mode ES0 is transparent to CSRNG and ES1
  // is never requested. In combine mode a CSRNG request is held internally until
  // the SHA3 digest is ready, then one CSRNG-facing ack returns the digest.
  always_comb begin
    csrng_hw_if_rsp_o = entropy_src_pkg::ENTROPY_SRC_HW_IF_RSP_DEFAULT;
    es0_hw_if_req_o = entropy_src_pkg::ENTROPY_SRC_HW_IF_REQ_DEFAULT;
    es1_hw_if_req_o = entropy_src_pkg::ENTROPY_SRC_HW_IF_REQ_DEFAULT;

    if (bypass_active) begin
      es0_hw_if_req_o = csrng_hw_if_req_i;
      csrng_hw_if_rsp_o = es0_hw_if_rsp_i;
    end else begin
      es0_hw_if_req_o.es_req = (state_q == combiner_st_req_entropy) && !es0_valid_q;
      es1_hw_if_req_o.es_req = (state_q == combiner_st_req_entropy) && !es1_valid_q;
      csrng_hw_if_rsp_o.es_ack = (state_q == combiner_st_comb_ack);
      csrng_hw_if_rsp_o.es_bits = digest_q;
      csrng_hw_if_rsp_o.es_fips = digest_fips_q;
    end
  end

  // Convert FSM states into the small SHA3 core control protocol: start, stream
  // message beats while ready, process, wait for state_valid, and issue done
  // after normal ack or the one-cycle KAT done flush state.
  always_comb begin
    sha3_start = 1'b0;
    sha3_process = 1'b0;
    sha3_done = MuBi4False;
    sha3_msg_valid = 1'b0;
    sha3_msg_data[0] = feed_word;
    sha3_msg_strb = '1;

    unique case (state_q)
      combiner_st_sha_start: begin
        sha3_start = 1'b1;
      end
      combiner_st_sha_feed: begin
        sha3_msg_valid = 1'b1;
      end
      combiner_st_sha_process: begin
        sha3_process = 1'b1;
      end
      combiner_st_comb_ack: begin
        sha3_done = MuBi4True;
      end
      combiner_st_kat_done: begin
        sha3_done = MuBi4True;
      end
      default: begin
      end
    endcase

  end

  // Main FSM:
  //   idle          : wait for ROM KAT start or CSRNG entropy request.
  //   req_entropy   : assert es_req to both ES instances until each ack/data is captured.
  //   sha_start     : pulse SHA3 start.
  //   sha_feed      : feed ES0||ES1 or bounded KAT message beats into SHA3.
  //   sha_process   : pulse SHA3 process; both operation types fit in one L384 block.
  //   sha_wait      : wait for SHA3 state_valid and latch digest.
  //   comb_ack      : present digest/es_fips to CSRNG for one ack cycle.
  //   wait_req_low  : wait for CSRNG to drop es_req before accepting a new request.
  //   kat_done      : pulse SHA3 done after a KAT digest is latched, then return idle.
  //   error         : terminal safe state for unexpected FSM encodings.
  always_comb begin
    state_d = state_q;
    op_is_kat_d = op_is_kat_q;
    es0_valid_d = es0_valid_q;
    es1_valid_d = es1_valid_q;
    es0_bits_d = es0_bits_q;
    es1_bits_d = es1_bits_q;
    es0_fips_d = es0_fips_q;
    es1_fips_d = es1_fips_q;
    digest_d = digest_q;
    digest_fips_d = digest_fips_q;
    kat_msg_d = kat_msg_q;
    kat_digest_d = kat_digest_q;
    kat_msg_len_d = kat_msg_len_q;
    kat_digest_valid_d = kat_digest_valid_q;
    feed_idx_d = feed_idx_q;
    feed_words_d = feed_words_q;

    unique case (state_q)
      combiner_st_idle: begin
        // Prefer ROM KAT START over HW entropy work. Normal combine starts only
        // on a CSRNG request while combine mode is enabled. A KAT start
        // snapshots the ROM-programmed 0..96 byte KAT window before hashing so
        // later AHB writes cannot perturb an in-flight KAT.
        op_is_kat_d = 1'b0;
        es0_valid_d = 1'b0;
        es1_valid_d = 1'b0;
        feed_idx_d = '0;

        if (kat_start_cmd) begin
          kat_digest_d = '0;
          kat_digest_valid_d = 1'b0;
          for (int word_idx = 0; word_idx < kat_msg_words32; word_idx++) begin
            kat_msg_d[(word_idx * 32) +: 32] = hwif_out.KAT_MSG[word_idx].data.value;
          end
          kat_msg_len_d = kat_msg_len_value[6:0];
          op_is_kat_d = 1'b1;
          state_d = combiner_st_sha_start;
        end else if (combine_en_status && csrng_hw_if_req_i.es_req) begin
          op_is_kat_d = 1'b0;
          state_d = combiner_st_req_entropy;
        end
      end

      combiner_st_req_entropy: begin
        // Request ES0 and ES1 in parallel, then retain each seed after its ack.
        // The SHA3 operation starts only after both 384b samples are available.
        if (es0_hw_if_rsp_i.es_ack && !es0_valid_q) begin
          es0_valid_d = 1'b1;
          es0_bits_d = es0_hw_if_rsp_i.es_bits;
          es0_fips_d = es0_hw_if_rsp_i.es_fips[0];
        end
        if (es1_hw_if_rsp_i.es_ack && !es1_valid_q) begin
          es1_valid_d = 1'b1;
          es1_bits_d = es1_hw_if_rsp_i.es_bits;
          es1_fips_d = es1_hw_if_rsp_i.es_fips[0];
        end
        if (es0_valid_d && es1_valid_d) begin
          feed_idx_d = '0;
          state_d = combiner_st_sha_start;
        end
      end

      combiner_st_sha_start: begin
        // KAT streams KAT_MSG_LEN/8 full beats from the snapped KAT_MSG window;
        // length 0 skips feed and processes the empty message. Normal combine
        // streams the fixed 12-beat ES0||ES1 message.
        feed_idx_d = '0;
        if (op_is_kat_q) begin
          feed_words_d = kat_feed_words;
          state_d = (kat_feed_words == 4'h0) ? combiner_st_sha_process :
                                                combiner_st_sha_feed;
        end else begin
          feed_words_d = combine_sha3_words_c;
          state_d = combiner_st_sha_feed;
        end
      end

      combiner_st_sha_feed: begin
        // Advance one 64b beat per SHA3 ready/valid acceptance. Operational
        // combine always feeds 12 beats; KAT feeds 0..12 beats from KAT_MSG.
        // Do not increment on the final beat (we move to process anyway) so
        // feed_idx_q never exceeds the message bound and the feed_word mux
        // needs no range guard.
        if (feed_accept) begin
          if ((feed_idx_q + 4'h1) == feed_words_q) begin
            state_d = combiner_st_sha_process;
          end else begin
            feed_idx_d = feed_idx_q + 4'h1;
          end
        end
      end

      combiner_st_sha_process: begin
        // A single process pulse finalizes the current single-block SHA3 message.
        state_d = combiner_st_sha_wait;
      end

      combiner_st_sha_wait: begin
        // Capture the digest either into KAT_DIGEST readback storage or into the
        // CSRNG-facing response register with the selected es_fips policy.
        if (sha3_state_valid) begin
          if (op_is_kat_q) begin
            kat_digest_d = sha3_state[0][seed_width-1:0];
            kat_digest_valid_d = 1'b1;
            state_d = combiner_st_kat_done;
          end else begin
            digest_d = sha3_state[0][seed_width-1:0];
            digest_fips_d = fips_combined;
            state_d = combiner_st_comb_ack;
          end
        end
      end

      combiner_st_comb_ack: begin
        // Ack CSRNG for one cycle. CSRNG samples digest/fips on this ack.
        state_d = combiner_st_wait_req_low;
      end

      combiner_st_wait_req_low: begin
        // Match entropy_src_ack_sm semantics: wait for req deassertion before
        // allowing the next combine request.
        if (!csrng_hw_if_req_i.es_req) begin
          state_d = combiner_st_idle;
        end
      end

      combiner_st_kat_done: begin
        // Flush ot_sha3 after KAT completion. KAT_DIGEST remains readable from
        // the generated register storage, and the combiner returns to normal
        // traffic without a separate SHA3 DONE command register.
        op_is_kat_d = 1'b0;
        state_d = combiner_st_idle;
      end

      combiner_st_error: begin
        state_d = combiner_st_error;
      end

      default: begin
        state_d = combiner_st_error;
      end
    endcase
  end

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      state_q <= combiner_st_idle;
      op_is_kat_q <= 1'b0;
      es0_valid_q <= 1'b0;
      es1_valid_q <= 1'b0;
      es0_bits_q <= '0;
      es1_bits_q <= '0;
      es0_fips_q <= 1'b0;
      es1_fips_q <= 1'b0;
      digest_q <= '0;
      digest_fips_q <= 1'b0;
      kat_msg_q <= '0;
      kat_digest_q <= '0;
      kat_msg_len_q <= '0;
      kat_digest_valid_q <= 1'b0;
      feed_idx_q <= '0;
      feed_words_q <= '0;
    end else begin
      // Default update: every register takes its computed next value once.
      // Security overrides below wipe only the register-visible KAT residuals
      // when ROM has set W1S AHB_LOCK.
      state_q <= state_d;
      op_is_kat_q <= op_is_kat_d;
      es0_valid_q <= es0_valid_d;
      es1_valid_q <= es1_valid_d;
      es0_bits_q <= es0_bits_d;
      es1_bits_q <= es1_bits_d;
      es0_fips_q <= es0_fips_d;
      es1_fips_q <= es1_fips_d;
      digest_q <= digest_d;
      digest_fips_q <= digest_fips_d;
      kat_msg_q <= kat_msg_d;
      kat_digest_q <= kat_digest_d;
      kat_msg_len_q <= kat_msg_len_d;
      kat_digest_valid_q <= kat_digest_valid_d;
      feed_idx_q <= feed_idx_d;
      feed_words_q <= feed_words_d;

      if (ahb_locked) begin
        // RoT zeroization: after ROM sets W1S AHB_LOCK, wipe and hold clear all
        // register-visible KAT residuals. Operational combine state/digest is
        // not register-visible and is left untouched.
        kat_msg_q <= '0;
        kat_digest_q <= '0;
        kat_msg_len_q <= '0;
        kat_digest_valid_q <= 1'b0;
        if (!op_is_kat_q && (state_q == combiner_st_idle)) begin
          feed_idx_q <= '0;
          feed_words_q <= '0;
        end
      end
    end
  end


  // AHB slave shim mirrors other Caliptra blocks: AHB-Lite is converted into
  // the generated register block's 32b CPU interface. The register layout is
  // combiner-owned and purpose-built; it does not reuse sha3_reg/kmac windows.
  ahb_slv_sif #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(32),
    .CLIENT_ADDR_WIDTH(AHB_ADDR_WIDTH)
  ) u_ahb_slv_sif (
    .hclk(clk),
    .hreset_n(reset_n),
    .haddr_i(haddr_i),
    .hwdata_i(hwdata_i),
    .hsel_i(hsel_i),
    .hwrite_i(hwrite_i),
    .hready_i(hready_i),
    .htrans_i(htrans_i),
    .hsize_i(hsize_i),
    .hresp_o(hresp_o),
    .hreadyout_o(hreadyout_o),
    .hrdata_o(hrdata_o),
    .dv(ahb_dv),
    .hld(ahb_hold),
    .err(ahb_err),
    .write(ahb_write),
    .wdata(ahb_wdata),
    .addr(ahb_addr),
    .rdata(ahb_rdata)
  );

  // Expected generated register module from entropy_combiner_reg.rdl.
  // Step-4 regeneration must provide entropy_combiner_reg_pkg with
  // entropy_combiner_reg__in_t/out_t and flat paths such as COMBINER_NAME,
  // KAT_CTRL, KAT_MSG_LEN, KAT_MSG, KAT_DIGEST, COMBINER_CTRL, AHB_LOCK,
  // COMBINER_STATUS.
  entropy_combiner_reg u_entropy_combiner_reg (
    .clk(clk),
    .rst(1'b0),

    .s_cpuif_req(reg_req),
    .s_cpuif_req_is_wr(ahb_write),
    .s_cpuif_addr(ahb_addr[entropy_combiner_reg_pkg::ENTROPY_COMBINER_REG_MIN_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data(ahb_wdata),
    .s_cpuif_wr_biten('1),
    .s_cpuif_req_stall_wr(),
    .s_cpuif_req_stall_rd(),
    .s_cpuif_rd_ack(reg_rd_ack),
    .s_cpuif_rd_err(reg_rd_err),
    .s_cpuif_rd_data(reg_rdata),
    .s_cpuif_wr_ack(reg_wr_ack),
    .s_cpuif_wr_err(reg_wr_err),

    .hwif_in(hwif_in),
    .hwif_out(hwif_out)
  );

  // Drive hardware-owned register fields. KAT_DIGEST and KAT_STATUS are derived
  // only from the real shared ot_sha3 datapath and the combiner FSM. KAT_MSG and
  // KAT_MSG_LEN are normally SW-owned, but hardware clears them while locked so
  // register storage does not retain KAT residuals after ROM sets W1S AHB_LOCK.
  always_comb begin
    hwif_in = '0;

    hwif_in.reset_b = reset_n;
    hwif_in.error_reset_b = cptra_pwrgood_i;

    // Advertise the combiner's own identity, not a reused SHA3/kmac identity.
    hwif_in.COMBINER_NAME[0].NAME.next = ENTROPY_COMBINER_CORE_NAME[31:0];
    hwif_in.COMBINER_NAME[1].NAME.next = ENTROPY_COMBINER_CORE_NAME[63:32];
    hwif_in.COMBINER_VERSION[0].VERSION.next = ENTROPY_COMBINER_CORE_VERSION[31:0];
    hwif_in.COMBINER_VERSION[1].VERSION.next = ENTROPY_COMBINER_CORE_VERSION[63:32];

    // KAT digest readback is hardware-owned storage populated from the real
    // ot_sha3 state output after state_valid. When W1S AHB_LOCK is set, force
    // the hwif value to zero as belt-and-suspenders protection on top of AHB
    // read-data masking and flop zeroization.
    for (int word_idx = 0; word_idx < kat_digest_words32; word_idx++) begin
      hwif_in.KAT_DIGEST[word_idx].data.next =
          ahb_locked ? '0 : kat_digest_q[(word_idx * 32) +: 32];
    end

    // KAT busy = a KAT operation is in flight (the FSM has left idle for a KAT
    // and has not yet returned). op_is_kat_q is set the cycle a KAT leaves idle
    // and cleared only when the FSM returns to idle after kat_done, so it is
    // asserted for exactly the non-idle KAT states and 0 in idle -- i.e. it is
    // already "KAT active and not idle", so no fragile per-state compare is
    // needed. It also isolates KAT status from operational ES0||ES1 combine
    // traffic (which never sets op_is_kat_q). valid rises at kat_done and holds,
    // so ROM polls busy==0 and then reads valid + KAT_DIGEST.
    hwif_in.KAT_STATUS.busy.next  = !ahb_locked && op_is_kat_q;
    hwif_in.KAT_STATUS.valid.next = !ahb_locked && kat_digest_valid_q;

    // Standard interrupt block hwset sources. Each ot_sha3 error latches its own
    // sticky bit in the power-good (error_reset_b) reset domain; SW clears via W1C.
    // Errors are not gated by the AHB lock so a fault stays observable and
    // survives warm reset. The KAT-done notification pulses for one cycle when a
    // ROM KAT digest is captured.
    hwif_in.intr_block_rf.error_internal_intr_r.sha3_error_sts.hwset        = sha3_error.valid;
    hwif_in.intr_block_rf.error_internal_intr_r.sparse_fsm_error_sts.hwset  = sha3_sparse_fsm_error;
    hwif_in.intr_block_rf.error_internal_intr_r.count_error_sts.hwset       = sha3_count_error;
    hwif_in.intr_block_rf.error_internal_intr_r.storage_rst_error_sts.hwset = sha3_storage_rst_error;
    hwif_in.intr_block_rf.notif_internal_intr_r.notif_kat_done_sts.hwset    = kat_done_event;

    hwif_in.COMBINER_STATUS.combine_en.next = combine_en_i;
    hwif_in.COMBINER_STATUS.combine_en.we   = 1'b1;

    // Freeze the FIPS combine policy once ROM sets W1S AHB_LOCK. swwe gates SW
    // writes at the register-block level (idiomatic Caliptra pattern, see
    // hmac.sv), keeping the ROM-programmed value intact so RT FW cannot weaken
    // the ES0/ES1 FIPS combination after boot. Defense-in-depth on top of the
    // AHB write-drop in the bus shim.
    hwif_in.COMBINER_CTRL.es_fips_policy.swwe = !ahb_locked;
    hwif_in.COMBINER_CTRL.es_fips_cfg.swwe    = !ahb_locked;
  end

  ot_sha3 #(
    .EnMasking(0)
  ) u_sha3 (
    .clk_i(clk),
    .rst_ni(reset_n),
    .msg_valid_i(sha3_msg_valid),
    .msg_data_i(sha3_msg_data),
    .msg_strb_i(sha3_msg_strb),
    .msg_ready_o(sha3_msg_ready),
    .rand_valid_i(1'b0),
    .rand_early_i(1'b0),
    .rand_data_i('0),
    .rand_aux_i(1'b0),
    .rand_update_o(),
    .rand_consumed_o(),
    .ns_data_i('0),
    .mode_i(ot_sha3_pkg::Sha3),
    .strength_i(ot_sha3_pkg::L384),
    .start_i(sha3_start),
    .process_i(sha3_process),
    .run_i(1'b0),
    .done_i(sha3_done),
    .absorbed_o(sha3_absorbed),
    .squeezing_o(sha3_squeezing),
    .block_processed_o(sha3_block_processed),
    .sha3_fsm_o(sha3_fsm),
    .state_valid_o(sha3_state_valid),
    .state_o(sha3_state),
    .run_req_o(sha3_run_req),
    .run_ack_i(1'b1),
    .lc_escalate_en_i(lc_ctrl_pkg::Off),
    .error_o(sha3_error),
    .sparse_fsm_error_o(sha3_sparse_fsm_error),
    .count_error_o(sha3_count_error),
    .keccak_storage_rst_error_o(sha3_storage_rst_error)
  );

  logic unused_signals;
  assign unused_signals = ^{sha3_absorbed, sha3_squeezing, sha3_block_processed, sha3_fsm,
                            sha3_run_req, reg_rd_ack, reg_wr_ack};

  `CALIPTRA_ASSERT_KNOWN(AhbRespKnownO_A, hresp_o, clk, !reset_n)
  `CALIPTRA_ASSERT_KNOWN(AhbReadyKnownO_A, hreadyout_o, clk, !reset_n)
  `CALIPTRA_ASSERT_KNOWN(CsrngEsAckKnownO_A, csrng_hw_if_rsp_o.es_ack, clk, !reset_n)
  `CALIPTRA_ASSERT_KNOWN(Es0ReqKnownO_A, es0_hw_if_req_o.es_req, clk, !reset_n)
  `CALIPTRA_ASSERT_KNOWN(Es1ReqKnownO_A, es1_hw_if_req_o.es_req, clk, !reset_n)
  `CALIPTRA_ASSERT_KNOWN(AhbLockKnownO_A, ahb_lock_o, clk, !reset_n)
  `CALIPTRA_ASSERT_KNOWN(ErrorIntrKnownO_A, error_intr_o, clk, !reset_n)
  `CALIPTRA_ASSERT_KNOWN(NotifIntrKnownO_A, notif_intr_o, clk, !reset_n)

  // ot_sha3 is instantiated standalone here (not via kmac), so its prim_count /
  // sparse-FSM security countermeasures need their "connected" assertions wired
  // up by this parent, mirroring kmac.sv. Every ot_sha3 CM error latches into the
  // sticky error interrupt status (intr_block_rf.error_internal_intr_r) and drives
  // error_intr_o, so the _TRIGGER_ERR variants point at error_intr_o and use this
  // module's clk / !reset_n.
  `CALIPTRA_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ERR(SentMsgCountCheck_A, u_sha3.u_pad.u_sentmsg_count,
                                                error_intr_o, 1'b0, 30, clk, !reset_n)
  `CALIPTRA_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ERR(RoundCountCheck_A, u_sha3.u_keccak.u_round_count,
                                                error_intr_o, 1'b0, 30, clk, !reset_n)
  `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(SHA3FsmCheck_A, u_sha3.u_state_regs,
                                              error_intr_o, 1'b0, 30, clk, !reset_n)
  `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(SHA3padFsmCheck_A, u_sha3.u_pad.u_state_regs,
                                              error_intr_o, 1'b0, 30, clk, !reset_n)
  `CALIPTRA_ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(KeccakFsmCheck_A, u_sha3.u_keccak.u_state_regs,
                                              error_intr_o, 1'b0, 30, clk, !reset_n)

endmodule
