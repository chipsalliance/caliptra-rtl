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

module sha512_acc_iccm_hash
    import soc_ifc_pkg::*;
    import pv_defines_pkg::*;
    import kv_defines_pkg::*;
  #(
    parameter DATA_WIDTH = 32,
    parameter BLOCK_NO   = 1024 / DATA_WIDTH
   )(
    input  logic         clk,
    input  logic         rst_b,

    // Snoop and control from ICCM / SHA acc top
    input  logic         iccm_hash_dv_i,
    input  logic         iccm_lock_i,
    input  logic         iccm_unlock_i,
    input  logic         soc_has_lock,
    input  logic         lock_value,
    input  logic         block_full,

    // SHA core visibility (for extend FSM)
    input  sha_fsm_state_e            sha_fsm_ps,
    input  logic [15:0][31:0]         core_digest,
    input  logic                      core_digest_valid,
    input  logic                      digest_valid_reg,
    input  logic [0:15][31:0]         digest_reg,

    // PV read response
    input  pv_rd_resp_t  pv_rd_resp_i,

    // ICCM mode / hash outputs into sha512_acc_top data path
    output logic         iccm_mode,
    output logic         iccm_lock_acquire,
    output logic         iccm_lock_clear,
    output logic         iccm_mode_block_we,
    output logic         iccm_mode_execute,
    output logic [31:0]  iccm_num_bytes_wr,
    output logic         extend_init,
    output logic         extend_load_block,
    output logic [0:BLOCK_NO-1][DATA_WIDTH-1:0] extend_block,

    // PV interface out
    output pv_write_t    pv_write_o,
    output pv_read_t     pv_read_o
   );

  // ICCM hash mode signals
  logic iccm_mode_done;
  logic iccm_armed;

  // PCR write via kv_write_client
  logic iccm_pcr_dest_done;
  logic [PV_NUM_DWORDS-1:0][31:0] iccm_pcr_dest_data;
  kv_write_t iccm_kv_write;
  logic iccm_pcr_data_avail;

  // PCR extend FSM
  typedef enum logic [3:0] {
    EXTEND_IDLE,
    EXTEND_SAVE_DIGEST,
    EXTEND_READ_PCR4,
    EXTEND_LOAD_HASH_PCR4,
    EXTEND_WAIT_PCR4,
    EXTEND_WRITE_PCR4,
    EXTEND_READ_PCR5,
    EXTEND_LOAD_HASH_PCR5,
    EXTEND_WAIT_PCR5,
    EXTEND_WRITE_PCR5,
    EXTEND_DONE
  } iccm_extend_fsm_e;

  iccm_extend_fsm_e extend_fsm_ps, extend_fsm_ns;
  logic [PV_NUM_DWORDS-1:0][31:0] iccm_digest_hold;
  logic [PV_NUM_DWORDS-1:0][31:0] extend_pcr_data;
  logic [3:0] extend_rd_dword_ctr;
  logic extend_pcr_read_en;
  logic [PV_ENTRY_ADDR_W-1:0] extend_pcr_entry;
  logic iccm_extend_ip;
  logic extend_write_trigger;

// ICCM mode: arms on the first ICCM write the snoop sees, or on
// iccm_lock_i for the zero-length case. The OR with the live trigger
// engages the same cycle the snoop fires to capture the first dword
// without a one-cycle slip.
always_comb iccm_mode = (iccm_armed | ((iccm_hash_dv_i | iccm_lock_i) & ~soc_has_lock)) & ~iccm_mode_done;

// HW SHA acc lock acquire: pulse hwset on the very first ICCM activity
// (snoop or iccm_lock_i). Gated by ~iccm_armed so the pulse fires exactly
// once at the start of the measurement, not again during release.
always_comb iccm_lock_acquire = (iccm_hash_dv_i | iccm_lock_i) &
                                ~soc_has_lock & ~iccm_armed & ~iccm_mode_done &
                                ~lock_value;

// HW lock release: clear LOCK back to 0 (free) after the full extend
// sequence completes (EXTEND_DONE). Using extend_fsm_ps == EXTEND_DONE
// ensures the lock is held through both the PCR4 and PCR5 writes.
always_comb iccm_lock_clear = (extend_fsm_ps == EXTEND_DONE);

// Extend FSM active flag
always_comb iccm_extend_ip = (extend_fsm_ps != EXTEND_IDLE) & (extend_fsm_ps != EXTEND_DONE);

// iccm_lock rising edge triggers finalization (equivalent to execute_set)
always_comb iccm_mode_execute = iccm_mode & iccm_lock_i;
// block_we for iccm mode: write when data valid and not stalled by block_full
always_comb iccm_mode_block_we = iccm_mode & iccm_hash_dv_i & ~block_full;

// ICCM mode done flag: sticky until iccm_unlock re-enables measurement.
// Prevents re-trigger of iccm_mode after hash completes.
// Set when the full extend sequence (PCR4 + PCR5) is complete.
always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b)
    iccm_mode_done <= 1'b0;
  else if (iccm_unlock_i)
    iccm_mode_done <= 1'b0;
  else if (extend_fsm_ps == EXTEND_DONE)
    iccm_mode_done <= 1'b1;
end

// ICCM armed: sticky, set on the first ICCM write the snoop sees, or on
// iccm_lock_i for the zero-length case. Cleared by iccm_unlock_i (fired
// by the boot FSM on fw_update_reset).
always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b)
    iccm_armed <= 1'b0;
  else if (iccm_unlock_i)
    iccm_armed <= 1'b0;
  else if ((iccm_hash_dv_i | iccm_lock_i) & ~soc_has_lock & ~iccm_mode_done)
    iccm_armed <= 1'b1;
end

// ICCM byte counter: tracks total bytes written for SHA padding
always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b)
    iccm_num_bytes_wr <= '0;
  else if (iccm_unlock_i)
    iccm_num_bytes_wr <= '0;
  else if (iccm_mode & iccm_mode_block_we)
    iccm_num_bytes_wr <= iccm_num_bytes_wr + 32'd4;
end

//----------------------------------------------------------------
// PCR Extend FSM
// After ICCM hash completes, extends PCR4 (Current) and PCR5 (Journey)
// using the standard extend operation: new = SHA-384(current_PCR || digest).
// Mirrors sha512.sv's pcr_hash_extend flow but controlled by HW FSM.
//----------------------------------------------------------------

// Digest holding register: latched before sha512_core is reused for extend
always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b)
    iccm_digest_hold <= '0;
  else if (extend_fsm_ps == EXTEND_SAVE_DIGEST) begin
    for (int i = 0; i < PV_NUM_DWORDS; i++)
      iccm_digest_hold[i] <= digest_reg[i];
  end
end

// Extend FSM state register
always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b)
    extend_fsm_ps <= EXTEND_IDLE;
  else if (iccm_unlock_i)
    extend_fsm_ps <= EXTEND_IDLE;
  else
    extend_fsm_ps <= extend_fsm_ns;
end

// Dword counter for PCR reads and block_reg loading
always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b)
    extend_rd_dword_ctr <= '0;
  else if (extend_fsm_ps == EXTEND_READ_PCR4 || extend_fsm_ps == EXTEND_READ_PCR5)
    extend_rd_dword_ctr <= extend_rd_dword_ctr + 4'd1;
  else
    extend_rd_dword_ctr <= '0;
end

// PCR read data capture: store read response into extend_pcr_data
always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b)
    extend_pcr_data <= '0;
  else if ((extend_fsm_ps == EXTEND_READ_PCR4 || extend_fsm_ps == EXTEND_READ_PCR5) &&
           extend_rd_dword_ctr < PV_NUM_DWORDS[3:0])
    extend_pcr_data[extend_rd_dword_ctr] <= pv_rd_resp_i.read_data;
end

// Extend FSM next-state logic
always_comb begin
  extend_fsm_ns = extend_fsm_ps;
  extend_init = 1'b0;
  extend_pcr_read_en = 1'b0;
  extend_pcr_entry = '0;
  extend_write_trigger = 1'b0;

  case (extend_fsm_ps) inside
    EXTEND_IDLE: begin
      if (iccm_mode & (sha_fsm_ps == SHA_DONE) & ~iccm_mode_done)
        extend_fsm_ns = EXTEND_SAVE_DIGEST;
    end

    EXTEND_SAVE_DIGEST: begin
      extend_fsm_ns = EXTEND_READ_PCR4;
    end

    EXTEND_READ_PCR4: begin
      extend_pcr_read_en = 1'b1;
      extend_pcr_entry = PV_ENTRY_ADDR_W'(4);
      if (extend_rd_dword_ctr == PV_NUM_DWORDS[3:0] - 1)
        extend_fsm_ns = EXTEND_LOAD_HASH_PCR4;
    end

    EXTEND_LOAD_HASH_PCR4: begin
      // block_reg will be loaded combinationally (see block_reg_nxt override below)
      extend_init = 1'b1;  // triggers SHA-384 init on next clock
      extend_fsm_ns = EXTEND_WAIT_PCR4;
    end

    EXTEND_WAIT_PCR4: begin
      if (core_digest_valid & ~digest_valid_reg)
        extend_fsm_ns = EXTEND_WRITE_PCR4;
    end

    EXTEND_WRITE_PCR4: begin
      extend_write_trigger = 1'b1;
      if (iccm_pcr_dest_done)
        extend_fsm_ns = EXTEND_READ_PCR5;
    end

    EXTEND_READ_PCR5: begin
      extend_pcr_read_en = 1'b1;
      extend_pcr_entry = PV_ENTRY_ADDR_W'(5);
      if (extend_rd_dword_ctr == PV_NUM_DWORDS[3:0] - 1)
        extend_fsm_ns = EXTEND_LOAD_HASH_PCR5;
    end

    EXTEND_LOAD_HASH_PCR5: begin
      extend_init = 1'b1;
      extend_fsm_ns = EXTEND_WAIT_PCR5;
    end

    EXTEND_WAIT_PCR5: begin
      if (core_digest_valid & ~digest_valid_reg)
        extend_fsm_ns = EXTEND_WRITE_PCR5;
    end

    EXTEND_WRITE_PCR5: begin
      extend_write_trigger = 1'b1;
      if (iccm_pcr_dest_done)
        extend_fsm_ns = EXTEND_DONE;
    end

    EXTEND_DONE: begin
      extend_fsm_ns = EXTEND_IDLE;
    end

    default: extend_fsm_ns = EXTEND_IDLE;
  endcase
end

// pv_read output: driven by extend FSM (HW-only, no FW control path)
always_comb begin
  pv_read_o.read_entry  = extend_pcr_entry;
  pv_read_o.read_offset = extend_rd_dword_ctr[PV_ENTRY_SIZE_WIDTH-1:0];
end

// Block register override for extend: load PCR value + digest + padding
// SHA-384 block = 1024 bits = 32 x 32-bit dwords
// Layout: [0:11] = PCR (48B), [12:23] = digest (48B), [24:31] = padding
// This feeds block_reg_nxt during EXTEND_LOAD_HASH_PCR4/PCR5 states
always_comb extend_load_block = (extend_fsm_ps == EXTEND_LOAD_HASH_PCR4) |
                                 (extend_fsm_ps == EXTEND_LOAD_HASH_PCR5);

always_comb begin
  for (int i = 0; i < PV_NUM_DWORDS; i++) begin
    // PCR current value in dwords 0-11
    extend_block[i] = extend_pcr_data[i];
    // ICCM digest in dwords 12-23
    extend_block[PV_NUM_DWORDS + i] = iccm_digest_hold[i];
  end
  // SHA-384 padding in dwords 24-31
  extend_block[2 * PV_NUM_DWORDS] = 32'h80000000;         // 0x80 pad byte
  for (int i = 2 * PV_NUM_DWORDS + 1; i < BLOCK_NO - 1; i++) begin
    extend_block[i] = 32'h0;
  end
  extend_block[BLOCK_NO - 1] = 32'h00000300;              // length = 768 bits
end

//----------------------------------------------------------------
// PCR Write via kv_write_client
// Used for both initial ICCM digest (future: removed) and extend results.
// During extend, write_entry is overloaded by the extend FSM.
//----------------------------------------------------------------

// Dest data source: during extend, use core_digest (extend result).
// core_digest[15] is MSB, core_digest[4] is LSB for SHA-384 (top 12 of 16 dwords).
// Match sha512.sv convention: kv_reg <= core_digest[DIG_NUM_DWORDS-1:DIG_NUM_DWORDS-PV_NUM_DWORDS]
always_comb begin
  for (int i = 0; i < PV_NUM_DWORDS; i++)
    iccm_pcr_dest_data[i] = core_digest[15 - i];
end

// Data available: pulse when extend FSM enters WRITE_PCR4 or WRITE_PCR5
always_comb iccm_pcr_data_avail = extend_write_trigger & ~iccm_pcr_dest_done;

// Write entry: 4 for PCR4, 5 for PCR5
logic [4:0] iccm_write_entry;
always_comb begin
  if (extend_fsm_ps == EXTEND_WRITE_PCR4 || extend_fsm_ps == EXTEND_WAIT_PCR4)
    iccm_write_entry = 5'd4;
  else
    iccm_write_entry = 5'd5;
end

kv_write_ctrl_reg_t       iccm_write_ctrl_reg;
kv_write_filter_metrics_t iccm_write_metrics;
kv_wr_resp_t              iccm_kv_resp;

always_comb begin
  iccm_write_ctrl_reg.rsvd           = '0;
  iccm_write_ctrl_reg.write_dest_vld = '0;
  iccm_write_ctrl_reg.write_entry    = iccm_write_entry;
  iccm_write_ctrl_reg.write_en       = 1'b1;
end

always_comb iccm_write_metrics = '0;
always_comb iccm_kv_resp.error = 1'b0;

kv_write_client #(
  .DATA_WIDTH(PV_NUM_DWORDS * PV_DATA_W),
  .KV_WRITE_SWAP_DWORDS(0)
)
iccm_pcr_write_client
(
  .clk(clk),
  .rst_b(rst_b),
  .zeroize(1'b0),

  .num_dwords(PV_NUM_DWORDS[4:0]),
  .write_ctrl_reg(iccm_write_ctrl_reg),
  .write_metrics(iccm_write_metrics),

  .kv_write(iccm_kv_write),
  .kv_resp(iccm_kv_resp),

  .dest_keyvault(),
  .dest_data_avail(iccm_pcr_data_avail),
  .dest_data(iccm_pcr_dest_data),

  .error_code(),
  .kv_ready(),
  .dest_done(iccm_pcr_dest_done)
);

// Map kv_write_t output to pv_write_t
always_comb begin
  pv_write_o.write_en     = iccm_kv_write.write_en;
  pv_write_o.write_entry  = iccm_kv_write.write_entry[PV_ENTRY_ADDR_W-1:0];
  pv_write_o.write_offset = iccm_kv_write.write_offset[PV_ENTRY_SIZE_WIDTH-1:0];
  pv_write_o.write_data   = iccm_kv_write.write_data;
end

endmodule
