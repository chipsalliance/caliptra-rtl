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
// writing KAT_MSG/KAT_MSG_LEN and pulsing KAT_CTRL.start; the KAT hashes through
// the same ot_sha3 gates used operationally. After KAT, ROM sets the W1S AHB_LOCK bit.
// `ahb_lock_o` is driven from that W1S register so step-3 integration can block
// runtime firmware reads of combiner entropy state.

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

  output logic busy_o,
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
  localparam int unsigned kat_msg_max_bytes = combine_msg_width / 8;
  localparam logic [3:0] combine_sha3_words_c = combine_sha3_words;
  localparam logic [6:0] kat_msg_max_bytes_c = kat_msg_max_bytes;

  // FSM state and datapath latches. ES response latches hold each upstream seed
  // until both have arrived; KAT message/digest latches snapshot the
  // combiner-owned KAT registers while the shared SHA3 datapath is busy.
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
  logic error_q, error_d;

  // COMBINER_STATUS strap capture-enable, mirroring soc_ifc's strap_we: a flop reset
  // to 1 that clears to 0 after the first cycle, so combine_en_i is captured once at
  // power-good, then held.
  logic combine_en_strap_we;

  logic [3:0] feed_idx_q, feed_idx_d;
  logic [3:0] feed_words_q, feed_words_d;
  logic [MsgStrbW-1:0] kat_last_strb_q, kat_last_strb_d;

  logic ahb_dv;
  logic ahb_hold;
  logic ahb_err;
  logic ahb_write;
  logic [31:0] ahb_wdata;
  logic [31:0] ahb_rdata;
  logic [AHB_ADDR_WIDTH-1:0] ahb_addr;

  logic reg_rd_err;
  logic reg_wr_err;
  logic reg_rd_ack;
  logic reg_wr_ack;

  entropy_combiner_reg__in_t hwif_in;
  entropy_combiner_reg__out_t hwif_out;

  logic kat_start_cmd;
  logic kat_msg_len_valid;

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

  logic normal_op_busy;
  logic bypass_active;
  logic [MsgWidth-1:0] feed_word;
  logic [MsgStrbW-1:0] feed_strb;
  logic feed_accept;
  logic fips_combined;
  logic [3:0] kat_feed_words;
  logic kat_last_word_partial;
  logic [MsgStrbW-1:0] kat_last_strb;
  logic error_event;
  logic notif_event;

  assign ahb_hold = 1'b0;
  assign ahb_err = reg_rd_err | reg_wr_err;

  assign kat_start_cmd = hwif_out.KAT_CTRL.start.value;
  assign kat_msg_len_valid = hwif_out.KAT_MSG_LEN.msg_len.value <= kat_msg_max_bytes_c;

  // ROM writes up to 96 bytes into KAT_MSG and programs KAT_MSG_LEN. The SHA3
  // core consumes 64b beats, so the byte length is converted into a beat count
  // plus a final-byte strobe for non-64b-aligned KAT vectors.
  assign kat_feed_words = (kat_msg_len_q[2:0] != 3'b000) ?
                          kat_msg_len_q[6:3] + 4'h1 :
                          kat_msg_len_q[6:3];
  assign kat_last_word_partial = kat_msg_len_q[2:0] != 3'b000;

  // Bypass is only allowed when no combine operation is in flight. This avoids
  // switching CSRNG's handshake partner mid-request if `combine_en_i` changes
  // while the combiner is gathering entropy or waiting for SHA3.
  assign normal_op_busy = !op_is_kat_q && !(state_q inside {
      combiner_st_idle, combiner_st_kat_done, combiner_st_error});
  assign bypass_active = !combine_en_i && !normal_op_busy;
  assign busy_o = (state_q != combiner_st_idle) && (state_q != combiner_st_kat_done) &&
                  (state_q != combiner_st_error);
  assign error_event = error_q | sha3_error.valid | sha3_sparse_fsm_error |
                       sha3_count_error | sha3_storage_rst_error;
  assign notif_event = kat_digest_valid_d & !kat_digest_valid_q;
  // The purpose-built combiner map has no interrupt status/enable registers.
  // Interrupt outputs are direct combiner-local event pulses/levels: errors are
  // level-sensitive until reset, notification pulses when a KAT digest becomes valid.
  assign error_intr_o = error_event;
  assign notif_intr_o = notif_event;
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

  // Last-beat byte strobes for shorter KAT vectors. KAT_MSG bytes are consumed
  // little-endian within each 64b beat, matching the operational ES bit packing.
  always_comb begin
    unique case (kat_msg_len_q[2:0])
      3'd1:   kat_last_strb = 8'h01;
      3'd2:   kat_last_strb = 8'h03;
      3'd3:   kat_last_strb = 8'h07;
      3'd4:   kat_last_strb = 8'h0f;
      3'd5:   kat_last_strb = 8'h1f;
      3'd6:   kat_last_strb = 8'h3f;
      3'd7:   kat_last_strb = 8'h7f;
      default: kat_last_strb = 8'hff;
    endcase
  end

  // SHA3 message-source mux. Normal operation feeds twelve 64b beats:
  // ES0[383:0] followed by ES1[383:0]. KAT mode feeds the latched KAT_MSG
  // register contents and honors KAT_MSG_LEN for shorter standard vectors.
  always_comb begin
    feed_word = '0;
    feed_strb = '0;

    if (op_is_kat_q) begin
      feed_word = kat_msg_q[(feed_idx_q * MsgWidth) +: MsgWidth];
      feed_strb = ((feed_idx_q + 4'h1) == feed_words_q) && kat_last_word_partial ?
                  kat_last_strb_q : 8'hff;
    end else if (feed_idx_q < 4'd6) begin
      feed_word = es0_bits_q[(feed_idx_q * MsgWidth) +: MsgWidth];
      feed_strb = 8'hff;
    end else begin
      feed_word = es1_bits_q[((feed_idx_q - 4'd6) * MsgWidth) +: MsgWidth];
      feed_strb = 8'hff;
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
    sha3_msg_strb = feed_strb;

    unique case (state_q)
      combiner_st_sha_start: begin
        sha3_start = 1'b1;
      end
      combiner_st_sha_feed: begin
        sha3_msg_valid = (feed_words_q != 4'h0);
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
  //   sha_feed      : feed either ES0||ES1 or KAT message beats into SHA3.
  //   sha_process   : pulse SHA3 process; 768b combine input fits in one L384 block.
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
    error_d = error_q;
    feed_idx_d = feed_idx_q;
    feed_words_d = feed_words_q;
    kat_last_strb_d = kat_last_strb_q;

    unique case (state_q)
      combiner_st_idle: begin
        // Prefer ROM KAT START over HW entropy work. Normal combine starts only
        // on a CSRNG request while combine mode is enabled. A KAT start snapshots
        // the purpose-built KAT_MSG/KAT_MSG_LEN registers before hashing so later
        // AHB writes cannot perturb an in-flight KAT.
        op_is_kat_d = 1'b0;
        es0_valid_d = 1'b0;
        es1_valid_d = 1'b0;
        feed_idx_d = '0;
        feed_words_d = '0;
        kat_last_strb_d = 8'hff;

        if (kat_start_cmd) begin
          kat_digest_d = '0;
          kat_digest_valid_d = 1'b0;
          if (kat_msg_len_valid) begin
            op_is_kat_d = 1'b1;
            kat_msg_len_d = hwif_out.KAT_MSG_LEN.msg_len.value;
            for (int word_idx = 0; word_idx < kat_msg_words32; word_idx++) begin
              kat_msg_d[(word_idx * 32) +: 32] = hwif_out.KAT_MSG[word_idx].data.value;
            end
            state_d = combiner_st_sha_start;
          end else begin
            error_d = 1'b1;
          end
        end else if (combine_en_i && csrng_hw_if_req_i.es_req) begin
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
          feed_words_d = combine_sha3_words_c;
          kat_last_strb_d = 8'hff;
          state_d = combiner_st_sha_start;
        end
      end

      combiner_st_sha_start: begin
        // Both KAT and normal combine have their messages latched by this point.
        // Program the shared feed counter, then stream directly into ot_sha3.
        if (op_is_kat_q) begin
          feed_idx_d = '0;
          feed_words_d = kat_feed_words;
          kat_last_strb_d = kat_last_strb;
        end else begin
          feed_idx_d = '0;
          feed_words_d = combine_sha3_words_c;
          kat_last_strb_d = 8'hff;
        end
        state_d = combiner_st_sha_feed;
      end

      combiner_st_sha_feed: begin
        // Advance one 64b beat per SHA3 ready/valid acceptance.
        if (feed_words_q == 4'h0) begin
          state_d = combiner_st_sha_process;
        end else if (feed_accept) begin
          if ((feed_idx_q + 4'h1) == feed_words_q) begin
            state_d = combiner_st_sha_process;
          end
          feed_idx_d = feed_idx_q + 4'h1;
        end
      end

      combiner_st_sha_process: begin
        // A single process pulse finalizes the current SHA3 message.
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
        error_d = 1'b1;
      end

      default: begin
        state_d = combiner_st_error;
        error_d = 1'b1;
      end
    endcase

    if ((state_q != combiner_st_idle) && kat_start_cmd) begin
      error_d = 1'b1;
    end

    if (sha3_error.valid || sha3_sparse_fsm_error || sha3_count_error || sha3_storage_rst_error) begin
      error_d = error_q | sha3_error.valid | sha3_sparse_fsm_error |
                sha3_count_error | sha3_storage_rst_error;
    end
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
      error_q <= 1'b0;
      feed_idx_q <= '0;
      feed_words_q <= '0;
      kat_last_strb_q <= 8'hff;
    end else begin
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
      error_q <= error_d;
      feed_idx_q <= feed_idx_d;
      feed_words_q <= feed_words_d;
      kat_last_strb_q <= kat_last_strb_d;
    end
  end


  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      combine_en_strap_we <= 1'b1;
    end else begin
      if (combine_en_strap_we)
        combine_en_strap_we <= 1'b0;
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
  // KAT_CTRL, KAT_MSG, KAT_DIGEST, COMBINER_CTRL, AHB_LOCK, COMBINER_STATUS.
  entropy_combiner_reg u_entropy_combiner_reg (
    .clk(clk),
    .rst(1'b0),

    .s_cpuif_req(ahb_dv),
    .s_cpuif_req_is_wr(ahb_write),
    .s_cpuif_addr(ahb_addr[entropy_combiner_reg_pkg::ENTROPY_COMBINER_REG_MIN_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data(ahb_wdata),
    .s_cpuif_wr_biten('1),
    .s_cpuif_req_stall_wr(),
    .s_cpuif_req_stall_rd(),
    .s_cpuif_rd_ack(reg_rd_ack),
    .s_cpuif_rd_err(reg_rd_err),
    .s_cpuif_rd_data(ahb_rdata),
    .s_cpuif_wr_ack(reg_wr_ack),
    .s_cpuif_wr_err(reg_wr_err),

    .hwif_in(hwif_in),
    .hwif_out(hwif_out)
  );

  // Drive hardware-owned register fields. KAT_DIGEST and KAT_STATUS are derived
  // only from the real shared ot_sha3 datapath and the combiner FSM. KAT_MSG and
  // KAT_MSG_LEN are SW-owned inputs read from hwif_out and latched on KAT start.
  always_comb begin
    hwif_in = '0;

    hwif_in.error_reset_b = cptra_pwrgood_i;
    hwif_in.reset_b = reset_n;

    // Advertise the combiner's own identity, not a reused SHA3/kmac identity.
    hwif_in.COMBINER_NAME[0].NAME.next = ENTROPY_COMBINER_CORE_NAME[31:0];
    hwif_in.COMBINER_NAME[1].NAME.next = ENTROPY_COMBINER_CORE_NAME[63:32];
    hwif_in.COMBINER_VERSION[0].VERSION.next = ENTROPY_COMBINER_CORE_VERSION[31:0];
    hwif_in.COMBINER_VERSION[1].VERSION.next = ENTROPY_COMBINER_CORE_VERSION[63:32];

    // KAT digest readback is hardware-owned storage populated from the real
    // ot_sha3 state output after state_valid. It is cleared only by reset or by
    // the next KAT start invalidating `kat_digest_valid_q`.
    for (int word_idx = 0; word_idx < kat_digest_words32; word_idx++) begin
      hwif_in.KAT_DIGEST[word_idx].data.next = kat_digest_q[(word_idx * 32) +: 32];
    end

    // KAT_STATUS exposes real datapath/FSM state. The SHA3 FSM bits are direct
    // comparisons against ot_sha3's exported sparse FSM state.
    hwif_in.KAT_STATUS.busy.next = op_is_kat_q && (state_q != combiner_st_kat_done);
    hwif_in.KAT_STATUS.valid.next = kat_digest_valid_q;
    hwif_in.KAT_STATUS.error.next = error_event;
    hwif_in.KAT_STATUS.sha3_idle.next = sha3_fsm == ot_sha3_pkg::StIdle;
    hwif_in.KAT_STATUS.sha3_absorb.next = sha3_fsm == ot_sha3_pkg::StAbsorb;
    hwif_in.KAT_STATUS.sha3_squeeze.next = sha3_fsm == ot_sha3_pkg::StSqueeze;

    hwif_in.COMBINER_STATUS.combine_en.next = combine_en_i;
    hwif_in.COMBINER_STATUS.combine_en.we   = combine_en_strap_we;
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
  assign unused_signals = ^{sha3_absorbed, sha3_squeezing, sha3_block_processed, sha3_run_req,
                            reg_rd_ack, reg_wr_ack};

  `CALIPTRA_ASSERT_KNOWN(AhbRespKnownO_A, hresp_o, clk, !reset_n)
  `CALIPTRA_ASSERT_KNOWN(AhbReadyKnownO_A, hreadyout_o, clk, !reset_n)
  `CALIPTRA_ASSERT_KNOWN(CsrngEsAckKnownO_A, csrng_hw_if_rsp_o.es_ack, clk, !reset_n)
  `CALIPTRA_ASSERT_KNOWN(Es0ReqKnownO_A, es0_hw_if_req_o.es_req, clk, !reset_n)
  `CALIPTRA_ASSERT_KNOWN(Es1ReqKnownO_A, es1_hw_if_req_o.es_req, clk, !reset_n)
  `CALIPTRA_ASSERT_KNOWN(AhbLockKnownO_A, ahb_lock_o, clk, !reset_n)

endmodule
