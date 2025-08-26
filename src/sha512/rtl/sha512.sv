//======================================================================
// Updated by Caliptra team to modify data access width
// and removing the work factor
//
// sha512.sv
// --------
// Top level wrapper for the SHA-512 hash function providing
// a simple memory like interface with 32 bit data access.
//
//
// Author: Joachim Strombergson
// Copyright (c) 2014,  Secworks Sweden AB
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or
// without modification, are permitted provided that the following
// conditions are met:
//
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
// FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
// COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
// BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
// STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
// ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
//======================================================================

module sha512
    import sha512_reg_pkg::*;
    import sha512_params_pkg::*;
    import kv_defines_pkg::*;  
    import pv_defines_pkg::*;    
    #(
        parameter ADDR_WIDTH = 32,
        parameter DATA_WIDTH = 64
    )(
        // Clock and reset.
        input wire           clk,
        input wire           reset_n,
        input wire           cptra_pwrgood,

        // Control.
        input wire           cs,
        input wire           we,

        // Data ports.
        input wire  [ADDR_WIDTH-1 : 0] address,
        input wire  [DATA_WIDTH-1 : 0] write_data,
        output wire [DATA_WIDTH-1 : 0] read_data,
        output wire          err,

        // PV interface
        output pv_read_t pv_read,
        output pv_write_t pv_write,
        input pv_rd_resp_t pv_rd_resp,
        input pv_wr_resp_t pv_wr_resp,
        output logic [PCR_HASH_NUM_DWORDS-1:0][DATA_WIDTH-1:0] pcr_signing_hash,

        // Interrupts
        output wire error_intr,
        output wire notif_intr,
        input  logic debugUnlock_or_scan_mode_switch
    );

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  reg init_reg;
  reg next_reg;
  reg restore_reg;
  reg ready_reg;
  reg [1 : 0] mode_reg;
  logic zeroize_reg;
  logic last_reg;

  localparam BLOCK_SIZE   = 1024;
  localparam DIG_SIZE     = 512;

  localparam BLOCK_NUM_DWORDS = BLOCK_SIZE / DATA_WIDTH;
  localparam DIG_NUM_DWORDS = DIG_SIZE / DATA_WIDTH;
  localparam NONCE_NUM_DWORDS = PV_SIZE_OF_NONCE / DATA_WIDTH;

  reg [DATA_WIDTH-1 : 0][BLOCK_NUM_DWORDS-1 : 0]    block_reg ;
  reg [DIG_NUM_DWORDS-1 : 0][DATA_WIDTH-1 : 0]      digest_reg;
  reg [PV_NUM_DWORDS -1 : 0][DATA_WIDTH-1 : 0]      kv_reg;
  
  
  reg [PCR_HASH_NUM_DWORDS -1 : 0][DATA_WIDTH-1 : 0]  pcr_sign_reg;
  logic [PCR_HASH_NUM_DWORDS-1 : 0][DATA_WIDTH-1 : 0] pcr_sign;
  logic                                               pcr_sign_we;
  reg                                                 digest_valid_reg;
  logic                                               digest_we;
  
  sha512_reg__in_t hwif_in;
  sha512_reg__out_t hwif_out;
  logic read_error, write_error;

  //KV/PV Gasket
  kv_read_t vault_read;
  kv_write_t vault_write;
  kv_rd_resp_t vault_rd_resp;
  kv_wr_resp_t vault_wr_resp;

  pv_read_t gen_hash_pv_read;

  //interface with client
  logic kv_src_write_en;
  logic [4:0] kv_src_write_offset;
  logic [31:0] kv_src_write_data;

  kv_error_code_e kv_src_error, kv_dest_error;
  logic kv_src_ready, kv_src_done;
  logic kv_dest_ready, kv_dest_done;

  logic dest_keyvault;
  kv_write_ctrl_reg_t kv_write_ctrl_reg;
  kv_write_ctrl_reg_t kv_write_ctrl_reg_q;
  kv_read_ctrl_reg_t kv_read_ctrl_reg;
  kv_read_filter_metrics_t kv_read_metrics;
  kv_write_filter_metrics_t kv_write_metrics;

  //KV Read Data Present 
  logic kv_read_data_present;
  logic kv_read_data_present_set, kv_read_data_present_reset;
  //PCR Hash Extend Function
  logic pcr_hash_extend_ip;
  logic pcr_hash_extend_set, pcr_hash_extend_reset;
  logic [KV_ENTRY_ADDR_W-1:0] hash_extend_entry;
  logic dest_data_avail; 
  logic [31:0] block_reg_lock,block_reg_lock_nxt;
  //PCR Gen Hash Function
  logic gen_hash_start;
  logic gen_hash_ip;
  logic gen_hash_init_reg;
  logic gen_hash_next_reg;
  logic gen_hash_last_reg;
  logic gen_hash_block_write_en;
  logic [4:0] gen_hash_block_write_offset;
  logic [31:0] gen_hash_block_write_data;

  logic [NONCE_NUM_DWORDS-1 : 0][DATA_WIDTH-1 : 0] pv_nonce;
  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  wire                                          core_ready;
  wire [BLOCK_SIZE-1 : 0]                       core_block;
  wire [DIG_NUM_DWORDS-1 : 0][DATA_WIDTH-1 : 0] core_digest;
  wire                                          core_digest_valid;
  logic [DIG_NUM_DWORDS-1 : 0][DATA_WIDTH-1 : 0] restore_digest;

  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
   assign core_block = { block_reg[00], block_reg[01], block_reg[02], block_reg[03],
                         block_reg[04], block_reg[05], block_reg[06], block_reg[07],
                         block_reg[08], block_reg[09], block_reg[10], block_reg[11],
                         block_reg[12], block_reg[13], block_reg[14], block_reg[15],
                         block_reg[16], block_reg[17], block_reg[18], block_reg[19],
                         block_reg[20], block_reg[21], block_reg[22], block_reg[23],
                         block_reg[24], block_reg[25], block_reg[26], block_reg[27],
                         block_reg[28], block_reg[29], block_reg[30], block_reg[31]};
  
  assign err = read_error | write_error;

  always_comb begin // ecc_reg_writing
      for (int dword=0; dword < PCR_HASH_NUM_DWORDS; dword++)begin
        pcr_signing_hash[dword] = pcr_sign_reg[(PCR_HASH_NUM_DWORDS-1)-dword];
      end
  end

  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  sha512_core core(
                   .clk(clk),
                   .reset_n(reset_n),
                   .zeroize(zeroize_reg),

                   .init_cmd(init_reg),
                   .next_cmd(next_reg),
                   .restore_cmd(restore_reg),
                   .mode(mode_reg),

                   .block_msg(core_block),
                   .restore_digest(restore_digest),

                   .ready(core_ready),

                   .digest(core_digest),
                   .digest_valid(core_digest_valid)
                  );


  //----------------------------------------------------------------
  // reg_update
  //
  // Update functionality for all registers in the core.
  // All registers are positive edge triggered with asynchronous
  // active low reset. All registers have write enable.
  //----------------------------------------------------------------
  always @ (posedge clk or negedge reset_n) begin : reg_update
    if (!reset_n) begin
      ready_reg            <= '0;
      digest_reg           <= '0;
      digest_valid_reg     <= '0;
      kv_reg               <= '0;
      pcr_sign_reg         <= '0;
      block_reg_lock       <= '0;
      pcr_hash_extend_ip   <= '0;
      hash_extend_entry    <= '0;
      kv_read_data_present <= '0;
      digest_we            <= '0;
    end
    else if (zeroize_reg) begin
      ready_reg            <= '0;
      digest_reg           <= '0;
      digest_valid_reg     <= '0;
      kv_reg               <= '0;
      pcr_sign_reg         <= '0;
      kv_read_data_present <= '0;
      digest_we            <= '0;
      block_reg_lock       <= '0;
    end
    else begin
      ready_reg        <= core_ready;
      digest_valid_reg <= core_digest_valid;

      if (core_digest_valid & ~digest_valid_reg & ~(dest_keyvault | kv_read_data_present)) begin
        digest_reg <= core_digest;
        digest_we <= 1'b1;
      end
      else
        digest_we <= '0;
      if (core_digest_valid & ~digest_valid_reg & (dest_keyvault | kv_read_data_present))
        kv_reg <= core_digest[DIG_NUM_DWORDS-1:DIG_NUM_DWORDS-PV_NUM_DWORDS];
      if (pcr_sign_we)
        pcr_sign_reg <= pcr_sign;

      block_reg_lock <= block_reg_lock_nxt;
      pcr_hash_extend_ip <= pcr_hash_extend_set ? '1 :
                            pcr_hash_extend_reset ? '0 : pcr_hash_extend_ip;
      hash_extend_entry <= pcr_hash_extend_set ? kv_read_ctrl_reg.read_entry : hash_extend_entry;
      kv_read_data_present <= kv_read_data_present_set ? '1 :
                              kv_read_data_present_reset ? '0 : kv_read_data_present;
    end
  end // reg_update

  always_comb begin
    pcr_sign_we = (dest_data_avail & gen_hash_ip);
    pcr_sign = core_digest[DIG_NUM_DWORDS-1:DIG_NUM_DWORDS-PCR_HASH_NUM_DWORDS];
  end

  //register hw interface
  always_comb begin

    hwif_in.SHA512_NAME[0].NAME.next = SHA512_CORE_NAME0;
    hwif_in.SHA512_NAME[1].NAME.next = SHA512_CORE_NAME1;

    hwif_in.SHA512_VERSION[0].VERSION.next = SHA512_CORE_VERSION0;
    hwif_in.SHA512_VERSION[1].VERSION.next = SHA512_CORE_VERSION1;

    //Mask commands when keyvault is busy to prevent runs with partial keys.
    init_reg = gen_hash_ip ? gen_hash_init_reg : (hwif_out.SHA512_CTRL.INIT.value & kv_src_ready);
    next_reg = gen_hash_ip ? gen_hash_next_reg : (hwif_out.SHA512_CTRL.NEXT.value & kv_src_ready);
    restore_reg = gen_hash_ip ? '0 : (hwif_out.SHA512_CTRL.RESTORE.value & kv_src_ready);
    mode_reg = gen_hash_ip ? MODE_SHA_512 : hwif_out.SHA512_CTRL.MODE.value;
    zeroize_reg = hwif_out.SHA512_CTRL.ZEROIZE.value || debugUnlock_or_scan_mode_switch;
    last_reg = gen_hash_ip ? gen_hash_last_reg : hwif_out.SHA512_CTRL.LAST.value;
    hwif_in.SHA512_CTRL.LAST.hwclr = core_digest_valid & ~digest_valid_reg;

    hwif_in.SHA512_STATUS.READY.next = ready_reg;
    hwif_in.SHA512_STATUS.VALID.next = digest_valid_reg;

    //output comes in big endian
    for (int dword =0; dword < DIG_NUM_DWORDS; dword++) begin
      restore_digest[dword] = hwif_out.SHA512_DIGEST[(DIG_NUM_DWORDS-1)-dword].DIGEST.value;
      hwif_in.SHA512_DIGEST[dword].DIGEST.we = zeroize_reg? 0 : digest_we;
      hwif_in.SHA512_DIGEST[dword].DIGEST.next = digest_reg[(DIG_NUM_DWORDS-1)-dword];
      hwif_in.SHA512_DIGEST[dword].DIGEST.hwclr = zeroize_reg;
    end
    //output comes in big endian
    for (int dword =0; dword < PCR_HASH_NUM_DWORDS; dword++) begin
      hwif_in.SHA512_GEN_PCR_HASH_DIGEST[dword].DIGEST.next = pcr_sign_reg[(PCR_HASH_NUM_DWORDS-1)-dword];
      hwif_in.SHA512_GEN_PCR_HASH_DIGEST[dword].DIGEST.hwclr = zeroize_reg;
    end

    for (int dword=0; dword< BLOCK_NUM_DWORDS; dword++) begin
      block_reg[dword] = hwif_out.SHA512_BLOCK[dword].BLOCK.value;
      hwif_in.SHA512_BLOCK[dword].BLOCK.we = zeroize_reg ? 0 : 
                                             gen_hash_ip ? gen_hash_block_write_en & (gen_hash_block_write_offset == dword) :
                                             (kv_src_write_en & (kv_src_write_offset == dword));
      hwif_in.SHA512_BLOCK[dword].BLOCK.next = gen_hash_ip ? gen_hash_block_write_data : kv_src_write_data;
      hwif_in.SHA512_BLOCK[dword].BLOCK.hwclr = zeroize_reg | kv_read_data_present_reset;
      //lock the block during gen hash operation
      hwif_in.SHA512_BLOCK[dword].BLOCK.swwel = gen_hash_ip ? '1 : block_reg_lock[dword];
    end
    //Set valid when fsm is done
    hwif_in.SHA512_VAULT_RD_STATUS.ERROR.next = kv_src_error;
    hwif_in.SHA512_KV_WR_STATUS.ERROR.next = kv_dest_error;
    //Set valid when fsm is done
    hwif_in.SHA512_VAULT_RD_STATUS.READY.next = kv_src_ready;
    hwif_in.SHA512_KV_WR_STATUS.READY.next = kv_dest_ready;
    //Set valid when fsm is done
    hwif_in.SHA512_VAULT_RD_STATUS.VALID.hwset = kv_src_done;
    hwif_in.SHA512_KV_WR_STATUS.VALID.hwset = kv_dest_done;
    //reset valid when fsm is started
    hwif_in.SHA512_VAULT_RD_STATUS.VALID.hwclr = kv_read_ctrl_reg.read_en;
    hwif_in.SHA512_KV_WR_STATUS.VALID.hwclr = kv_write_ctrl_reg.write_en;
    //clear en when busy
    hwif_in.SHA512_VAULT_RD_CTRL.read_en.hwclr = ~kv_src_ready;
    hwif_in.SHA512_KV_WR_CTRL.write_en.hwclr = ~kv_dest_ready;

    gen_hash_start = hwif_out.SHA512_GEN_PCR_HASH_CTRL.START.value;
    hwif_in.SHA512_GEN_PCR_HASH_STATUS.READY.next = ~gen_hash_ip & ~pcr_hash_extend_ip & ready_reg;
    hwif_in.SHA512_GEN_PCR_HASH_STATUS.VALID.hwset = gen_hash_ip & dest_data_avail;
    hwif_in.SHA512_GEN_PCR_HASH_STATUS.VALID.hwclr = gen_hash_start;

  end

    // Software write-enables to prevent KV reg manipulation mid-operation
    always_comb hwif_in.SHA512_VAULT_RD_CTRL.read_en.swwe         = !kv_read_data_present && ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_VAULT_RD_CTRL.read_entry.swwe      = !kv_read_data_present && ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_VAULT_RD_CTRL.pcr_hash_extend.swwe = !kv_read_data_present && ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_VAULT_RD_CTRL.rsvd.swwe            = !kv_read_data_present && ready_reg && !gen_hash_ip;

    // KV write control must be written before SHA core operation begins, even though
    // output isn't written to KV until the end of the operation.
    // Prevent partial-key attacks by blocking register modifications during core execution.
    always_comb hwif_in.SHA512_KV_WR_CTRL.write_en.swwe              = ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_KV_WR_CTRL.write_entry.swwe           = ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_KV_WR_CTRL.hmac_key_dest_valid.swwe   = ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_KV_WR_CTRL.hmac_block_dest_valid.swwe = ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_KV_WR_CTRL.mldsa_seed_dest_valid.swwe = ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_KV_WR_CTRL.ecc_pkey_dest_valid.swwe   = ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_KV_WR_CTRL.ecc_seed_dest_valid.swwe   = ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_KV_WR_CTRL.aes_key_dest_valid.swwe    = ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_KV_WR_CTRL.mlkem_seed_dest_valid.swwe = ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_KV_WR_CTRL.mlkem_msg_dest_valid.swwe  = ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_KV_WR_CTRL.dma_data_dest_valid.swwe   = ready_reg && !gen_hash_ip;
    always_comb hwif_in.SHA512_KV_WR_CTRL.rsvd.swwe                  = ready_reg && !gen_hash_ip;

  `CALIPTRA_KV_WRITE_CTRL_REG2STRUCT(kv_write_ctrl_reg, SHA512_KV_WR_CTRL)
  `CALIPTRA_KV_READ_CTRL_REG2STRUCT(kv_read_ctrl_reg, SHA512_VAULT_RD_CTRL)

//Force result into KV reg whenever source came from KV
  always_comb kv_read_data_present_set = kv_read_ctrl_reg.read_en & ~kv_read_ctrl_reg.pcr_hash_extend;
  always_comb kv_read_data_present_reset = kv_read_data_present & dest_data_avail;

//Hash extend logic
  always_comb pcr_hash_extend_set = kv_read_ctrl_reg.read_en & kv_read_ctrl_reg.pcr_hash_extend;
  always_comb pcr_hash_extend_reset = pcr_hash_extend_ip & kv_dest_done;

//set the lock for the part of the block being written by KV logic during PCR hash extend
//release the lock once init has been seen
always_comb begin
  for (int dword=0; dword< BLOCK_NUM_DWORDS; dword++) begin
    if (init_reg | next_reg) begin
      block_reg_lock_nxt[dword] = '0;
    end
    else begin
      //Lock the block for any keyvault data
      block_reg_lock_nxt[dword] =  (kv_src_write_en & (kv_src_write_offset == dword)) ? '1 :  block_reg_lock[dword];
    end
  end
end

// Register Block
sha512_reg i_sha512_reg (
    .clk(clk),
    .rst(1'b0),

    .s_cpuif_req         (cs),
    .s_cpuif_req_is_wr   (we),
    .s_cpuif_addr        (address[SHA512_REG_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data     (write_data),
    .s_cpuif_wr_biten    ('1),
    .s_cpuif_req_stall_wr( ),
    .s_cpuif_req_stall_rd( ),
    .s_cpuif_rd_ack      ( ),
    .s_cpuif_rd_err      (read_error),
    .s_cpuif_rd_data     (read_data),
    .s_cpuif_wr_ack      ( ),
    .s_cpuif_wr_err      (write_error),

    .hwif_in (hwif_in ),
    .hwif_out(hwif_out)
);

//interrupt register hw interface
assign hwif_in.reset_b = reset_n;
assign hwif_in.error_reset_b = cptra_pwrgood;
assign hwif_in.sha512_ready = ready_reg;
assign hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = core_digest_valid & ~digest_valid_reg;
assign hwif_in.intr_block_rf.error_internal_intr_r.error0_sts.hwset = 1'b0; // TODO
assign hwif_in.intr_block_rf.error_internal_intr_r.error1_sts.hwset = 1'b0; // TODO
assign hwif_in.intr_block_rf.error_internal_intr_r.error2_sts.hwset = 1'b0; // TODO
assign hwif_in.intr_block_rf.error_internal_intr_r.error3_sts.hwset = 1'b0; // TODO

assign error_intr = hwif_out.intr_block_rf.error_global_intr_r.intr;
assign notif_intr = hwif_out.intr_block_rf.notif_global_intr_r.intr;

//Read Block
always_comb pv_read =  gen_hash_ip ? gen_hash_pv_read :
                       pcr_hash_extend_ip ? vault_read : '0;
always_comb vault_rd_resp = pv_rd_resp;



kv_read_client #(
    .DATA_WIDTH(BLOCK_SIZE),
    .PAD(1)
)
sha512_block_kv_read
(
    .clk(clk),
    .rst_b(reset_n),
    .zeroize(zeroize_reg),

    //client control register
    .read_ctrl_reg(kv_read_ctrl_reg),
    .read_metrics(kv_read_metrics),

    //interface with kv
    .kv_read(vault_read),
    .kv_resp(vault_rd_resp),

    //interface with client
    .write_en(kv_src_write_en),
    .write_offset(kv_src_write_offset),
    .write_data(kv_src_write_data),

    .error_code(kv_src_error),
    .kv_ready(kv_src_ready),
    .read_done(kv_src_done)
);

always_comb begin
  pv_write.write_data = pcr_hash_extend_ip ? vault_write.write_data : '0;
  pv_write.write_en = pcr_hash_extend_ip ? vault_write.write_en : '0;
  pv_write.write_entry = pcr_hash_extend_ip ? vault_write.write_entry : '0;
  pv_write.write_offset = pcr_hash_extend_ip ? vault_write.write_offset : '0;
end
always_comb vault_wr_resp = pv_wr_resp;

//during PCR hash extend overload write control
//force write enable and always write to the source address that we read from
always_comb begin
  kv_write_ctrl_reg_q = kv_write_ctrl_reg;
  kv_write_ctrl_reg_q.write_en = ~pcr_hash_extend_ip ? kv_write_ctrl_reg.write_en : '1;
  kv_write_ctrl_reg_q.write_entry = ~pcr_hash_extend_ip ? kv_write_ctrl_reg.write_entry : hash_extend_entry;
end

//write out the dest data to KV or PCR on last iteration of SHA
always_comb dest_data_avail = core_digest_valid & ~digest_valid_reg & last_reg;

always_comb begin
  for (int dword=0; dword< NONCE_NUM_DWORDS; dword++) begin
      pv_nonce[dword] = hwif_out.SHA512_GEN_PCR_HASH_NONCE[dword].NONCE.value;
  end
end

//No filtering rules for SHA512, goes to PCR vault
always_comb begin
  kv_read_metrics = '{default: '0};
  kv_write_metrics = '{default: '0};
end

kv_write_client #(
  .DATA_WIDTH(PV_NUM_DWORDS*PV_DATA_W)
)
sha512_result_kv_write
(
  .clk(clk),
  .rst_b(reset_n),
  .zeroize(zeroize_reg),

  //client control register
  .write_ctrl_reg(kv_write_ctrl_reg_q),
  .num_dwords(PV_NUM_DWORDS[4:0]),
  .write_metrics(kv_write_metrics),

  //interface with kv
  .kv_write(vault_write),
  .kv_resp(vault_wr_resp),

  //interface with client
  .dest_keyvault(dest_keyvault),
  .dest_data_avail(dest_data_avail),
  .dest_data(kv_reg),

  .error_code(kv_dest_error),
  .kv_ready(kv_dest_ready),
  .dest_done(kv_dest_done)
);

pv_gen_hash
pv_gen_hash1
(
  .clk(clk),
  .rst_b(reset_n),
  .zeroize(zeroize_reg),

  .core_ready(ready_reg),
  .core_digest_valid(gen_hash_ip & dest_data_avail),

  .start(gen_hash_start),
  .nonce(pv_nonce),

  .gen_hash_ip(gen_hash_ip),
  .gen_hash_init_reg(gen_hash_init_reg),
  .gen_hash_next_reg(gen_hash_next_reg),
  .gen_hash_last_reg(gen_hash_last_reg),

  .block_we(gen_hash_block_write_en),
  .block_offset(gen_hash_block_write_offset),
  .block_wr_data(gen_hash_block_write_data),

  .pv_read(gen_hash_pv_read),
  .pv_rd_resp(pv_rd_resp)
);

`CALIPTRA_ASSERT_STABLE(ERR_SHA_KEY_RD_CTRL_NOT_STABLE, kv_read_ctrl_reg, clk, (!reset_n || ready_reg) )
`CALIPTRA_ASSERT_STABLE(ERR_SHA_WR_CTRL_NOT_STABLE, kv_write_ctrl_reg, clk, (!reset_n || ready_reg) )
`CALIPTRA_ASSERT_STABLE(ERR_SHA_BLOCK_NOT_STABLE, block_reg, clk, (!reset_n || ready_reg) )

endmodule // sha512

//======================================================================
// EOF sha512.sv
//======================================================================
