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
// AES CLP Wrapper Testbench
// Target DUT: aes_clp_wrapper
// Interface:  AHB-Lite (no hierarchical force/release)
//
// Register address map (all addresses are absolute AHB addresses):
//   AES registers (TLUL space) are at base 0x0000_0000 (AHB addr < 0x800)
//   CLP registers (ENTROPY_IF_SEED, CTRL0, etc.) are at base 0x0000_0800 (VH_REGISTER_ADDRESS_OFFSET, AHB addr >= 0x800)
//
// CTRL_SHADOWED [15:0]:
//   [1:0]  operation       (AES_ENC=01, AES_DEC=10)
//   [7:2]  mode            (ECB=6'b000001, CBC=6'b000010, CTR=6'b010000, GCM=6'b100000)
//   [10:8] key_len         (AES_128=001, AES_192=010, AES_256=100)
//   [11]   sideload        (0 = software key)
//   [14:12] prng_reseed_rate (001 = per-1)
//   [15]   manual_operation (1 = manual; required so DUT waits for TRIGGER.start)
//
// TRIGGER [3:0]:
//   [0] start
//   [1] key_iv_data_in_clear
//   [2] data_out_clear
//   [3] prng_reseed
//
// STATUS [6:0]:
//   [0] idle
//   [1] stall
//   [2] output_lost
//   [3] output_valid
//   [4] input_ready
//   [5] alert_recov_ctrl_update_err
//   [6] alert_fatal_fault
//
// CTRL_GCM_SHADOWED [10:0]:
//   [5:0]  phase            (GCM_INIT=6'h01, GCM_AAD=6'h04, GCM_TEXT=6'h08, GCM_TAG=6'h20)
//   [10:6] num_valid_bytes

`timescale 1ns/1ps

module aes_clp_tb
  import kv_defines_pkg::*;
();

  //--------------------------------------------------------------------------
  // Parameters
  //--------------------------------------------------------------------------
  parameter CLK_HALF_PERIOD = 5;   // 100 MHz clock
  parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  // AHB HTRANS values
  parameter [1:0] AHB_HTRANS_IDLE   = 2'b00;
  parameter [1:0] AHB_HTRANS_NONSEQ = 2'b10;

  // AES register base address (VH_REGISTER_ADDRESS_OFFSET)
  parameter [31:0] AES_BASE     = 32'h0000_0000;
  parameter [31:0] AES_CLP_BASE = 32'h0000_0800;

  // AES register offsets (from aes_reg_pkg.sv)
  parameter [31:0] AES_KEY_SHARE0_0  = AES_BASE + 32'h04;
  parameter [31:0] AES_KEY_SHARE0_1  = AES_BASE + 32'h08;
  parameter [31:0] AES_KEY_SHARE0_2  = AES_BASE + 32'h0c;
  parameter [31:0] AES_KEY_SHARE0_3  = AES_BASE + 32'h10;
  parameter [31:0] AES_KEY_SHARE0_4  = AES_BASE + 32'h14;
  parameter [31:0] AES_KEY_SHARE0_5  = AES_BASE + 32'h18;
  parameter [31:0] AES_KEY_SHARE0_6  = AES_BASE + 32'h1c;
  parameter [31:0] AES_KEY_SHARE0_7  = AES_BASE + 32'h20;

  parameter [31:0] AES_KEY_SHARE1_0  = AES_BASE + 32'h24;
  parameter [31:0] AES_KEY_SHARE1_1  = AES_BASE + 32'h28;
  parameter [31:0] AES_KEY_SHARE1_2  = AES_BASE + 32'h2c;
  parameter [31:0] AES_KEY_SHARE1_3  = AES_BASE + 32'h30;
  parameter [31:0] AES_KEY_SHARE1_4  = AES_BASE + 32'h34;
  parameter [31:0] AES_KEY_SHARE1_5  = AES_BASE + 32'h38;
  parameter [31:0] AES_KEY_SHARE1_6  = AES_BASE + 32'h3c;
  parameter [31:0] AES_KEY_SHARE1_7  = AES_BASE + 32'h40;

  parameter [31:0] AES_IV_0          = AES_BASE + 32'h44;
  parameter [31:0] AES_IV_1          = AES_BASE + 32'h48;
  parameter [31:0] AES_IV_2          = AES_BASE + 32'h4c;
  parameter [31:0] AES_IV_3          = AES_BASE + 32'h50;

  parameter [31:0] AES_DATA_IN_0     = AES_BASE + 32'h54;
  parameter [31:0] AES_DATA_IN_1     = AES_BASE + 32'h58;
  parameter [31:0] AES_DATA_IN_2     = AES_BASE + 32'h5c;
  parameter [31:0] AES_DATA_IN_3     = AES_BASE + 32'h60;

  parameter [31:0] AES_DATA_OUT_0    = AES_BASE + 32'h64;
  parameter [31:0] AES_DATA_OUT_1    = AES_BASE + 32'h68;
  parameter [31:0] AES_DATA_OUT_2    = AES_BASE + 32'h6c;
  parameter [31:0] AES_DATA_OUT_3    = AES_BASE + 32'h70;

  parameter [31:0] AES_CTRL_SHADOWED     = AES_BASE + 32'h74;
  parameter [31:0] AES_CTRL_GCM_SHADOWED = AES_BASE + 32'h88;
  parameter [31:0] AES_TRIGGER           = AES_BASE + 32'h80;
  parameter [31:0] AES_STATUS            = AES_BASE + 32'h84;

  // CLP register addresses (ENTROPY_IF_SEED, no +0x800 offset)
  parameter [31:0] AES_ENTROPY_IF_SEED_0 = AES_CLP_BASE + 32'h0000_0110;
  parameter [31:0] AES_ENTROPY_IF_SEED_1 = AES_CLP_BASE + 32'h0000_0114;
  parameter [31:0] AES_ENTROPY_IF_SEED_2 = AES_CLP_BASE + 32'h0000_0118;
  parameter [31:0] AES_ENTROPY_IF_SEED_3 = AES_CLP_BASE + 32'h0000_011c;
  parameter [31:0] AES_ENTROPY_IF_SEED_4 = AES_CLP_BASE + 32'h0000_0120;
  parameter [31:0] AES_ENTROPY_IF_SEED_5 = AES_CLP_BASE + 32'h0000_0124;
  parameter [31:0] AES_ENTROPY_IF_SEED_6 = AES_CLP_BASE + 32'h0000_0128;
  parameter [31:0] AES_ENTROPY_IF_SEED_7 = AES_CLP_BASE + 32'h0000_012c;
  parameter [31:0] AES_ENTROPY_IF_SEED_8 = AES_CLP_BASE + 32'h0000_0130;

  // CTRL_SHADOWED field encodings
  // operation
  parameter [1:0]  AES_OP_ENC  = 2'b01;
  parameter [1:0]  AES_OP_DEC  = 2'b10;
  // mode
  parameter [5:0]  AES_MODE_ECB = 6'b000001;
  parameter [5:0]  AES_MODE_CBC = 6'b000010;
  parameter [5:0]  AES_MODE_CFB = 6'b000100;   // from aes_pkg.sv AES_CFB
  parameter [5:0]  AES_MODE_OFB = 6'b001000;   // from aes_pkg.sv AES_OFB
  parameter [5:0]  AES_MODE_CTR = 6'b010000;
  parameter [5:0]  AES_MODE_GCM = 6'b100000;
  // key_len
  parameter [2:0]  AES_KEY_128 = 3'b001;
  parameter [2:0]  AES_KEY_192 = 3'b010;
  parameter [2:0]  AES_KEY_256 = 3'b100;
  // prng_reseed_rate: PER_1 = 3'b001
  parameter [2:0]  PRNG_PER_1  = 3'b001;
  // STATUS bit positions
  parameter        ST_IDLE          = 0;
  parameter        ST_OUTPUT_VALID  = 3;
  parameter        ST_INPUT_READY   = 4;

  // GCM phase encodings (from aes_pkg.sv)
  parameter [5:0]  GCM_INIT    = 6'h01;
  parameter [5:0]  GCM_RESTORE = 6'h02;
  parameter [5:0]  GCM_AAD     = 6'h04;
  parameter [5:0]  GCM_TEXT    = 6'h08;
  parameter [5:0]  GCM_SAVE    = 6'h10;
  parameter [5:0]  GCM_TAG     = 6'h20;

  //--------------------------------------------------------------------------
  // DUT signals
  //--------------------------------------------------------------------------
  logic        clk_tb;
  logic        reset_n_tb;
  logic        cptra_pwrgood_tb;

  logic [31:0] haddr_i_tb;
  logic [31:0] hwdata_i_tb;
  logic        hsel_i_tb;
  logic        hwrite_i_tb;
  logic        hready_i_tb;
  logic [1:0]  htrans_i_tb;
  logic [2:0]  hsize_i_tb;

  logic        hresp_o_tb;
  logic        hreadyout_o_tb;
  logic [31:0] hrdata_o_tb;

  // KV interface (stubbed)
  kv_read_t      kv_read_tb;
  kv_rd_resp_t   kv_rd_resp_tb;
  kv_write_t     kv_write_tb;
  kv_wr_resp_t   kv_wr_resp_tb;

  // New 2.1 ports (stubbed)
  logic        ocp_lock_in_progress_tb;
  logic [15:0] key_release_key_size_tb;

  logic        input_ready_o_tb;
  logic        output_valid_o_tb;
  logic        status_idle_o_tb;

  logic        dma_req_dv_tb;
  logic        dma_req_write_tb;
  logic [31:0] dma_req_addr_tb;
  logic [31:0] dma_req_wdata_tb;
  logic        dma_req_hold_tb;
  logic        dma_req_error_tb;
  logic [31:0] dma_req_rdata_tb;

  logic        busy_o_tb;
  logic        error_intr_tb;
  logic        notif_intr_tb;
  logic        debugUnlock_or_scan_mode_switch_tb;

  // Read data capture register
  logic [31:0] read_data;

  //--------------------------------------------------------------------------
  // DUT instantiation
  //--------------------------------------------------------------------------
  aes_clp_wrapper #(
    .AHB_DATA_WIDTH(32),
    .AHB_ADDR_WIDTH(32)
  ) dut (
    .clk                         (clk_tb),
    .reset_n                     (reset_n_tb),
    .cptra_pwrgood               (cptra_pwrgood_tb),

    .haddr_i                     (haddr_i_tb),
    .hwdata_i                    (hwdata_i_tb),
    .hsel_i                      (hsel_i_tb),
    .hwrite_i                    (hwrite_i_tb),
    .hready_i                    (hready_i_tb),
    .htrans_i                    (htrans_i_tb),
    .hsize_i                     (hsize_i_tb),

    .hresp_o                     (hresp_o_tb),
    .hreadyout_o                 (hreadyout_o_tb),
    .hrdata_o                    (hrdata_o_tb),

    // OCP lock - not used in TB; tie off inactive
    .ocp_lock_in_progress        (ocp_lock_in_progress_tb),
    .key_release_key_size        (key_release_key_size_tb),

    // Direct status outputs - observed but not polled (TB uses STATUS reg via AHB)
    .input_ready_o               (input_ready_o_tb),
    .output_valid_o              (output_valid_o_tb),
    .status_idle_o               (status_idle_o_tb),

    // DMA CIF - not used in TB; tie off inactive
    .dma_req_dv                  (dma_req_dv_tb),
    .dma_req_write               (dma_req_write_tb),
    .dma_req_addr                (dma_req_addr_tb),
    .dma_req_wdata               (dma_req_wdata_tb),
    .dma_req_hold                (dma_req_hold_tb),
    .dma_req_error               (dma_req_error_tb),
    .dma_req_rdata               (dma_req_rdata_tb),

    .kv_read                     (kv_read_tb),
    .kv_rd_resp                  (kv_rd_resp_tb),
    .kv_write                    (kv_write_tb),
    .kv_wr_resp                  (kv_wr_resp_tb),

    .busy_o                      (busy_o_tb),
    .error_intr                  (error_intr_tb),
    .notif_intr                  (notif_intr_tb),
    .debugUnlock_or_scan_mode_switch (debugUnlock_or_scan_mode_switch_tb)
  );

  //--------------------------------------------------------------------------
  // KV stub
  //--------------------------------------------------------------------------
  assign kv_rd_resp_tb          = '0;  // No KV key; software key path used throughout
  assign kv_wr_resp_tb          = '0;  // KV write not used; immediately ack with no error

  // OCP lock and DMA not exercised in this TB
  assign ocp_lock_in_progress_tb = 1'b0;
  assign key_release_key_size_tb = '0;
  assign dma_req_dv_tb           = 1'b0;
  assign dma_req_write_tb        = 1'b0;
  assign dma_req_addr_tb         = '0;
  assign dma_req_wdata_tb        = '0;

  //--------------------------------------------------------------------------
  // Clock generation
  //--------------------------------------------------------------------------
  initial clk_tb = 0;
  always #CLK_HALF_PERIOD clk_tb = ~clk_tb;

  //--------------------------------------------------------------------------
  // AHB bus primitives
  //--------------------------------------------------------------------------

  // Idle the bus between transactions
  task ahb_idle;
    hsel_i_tb   = 0;
    hwrite_i_tb = 0;
    hready_i_tb = 1;
    htrans_i_tb = AHB_HTRANS_IDLE;
    haddr_i_tb  = 'Z;
    hwdata_i_tb = '0;
    hsize_i_tb  = 3'b010;
  endtask

  // Single 32-bit AHB write
  // Address phase: assert address + NONSEQ for one cycle
  // Data   phase:  present write data, release address
  task write_single_word(input [31:0] address, input [31:0] word);
    begin
      @(posedge clk_tb);
      hsel_i_tb   = 1;
      haddr_i_tb  = address;
      hwrite_i_tb = 1;
      hready_i_tb = 1;
      htrans_i_tb = AHB_HTRANS_NONSEQ;
      hsize_i_tb  = 3'b010;
      @(posedge clk_tb);                // end of address phase
      wait(hreadyout_o_tb == 1'b1);
      hwdata_i_tb = word;
      @(posedge clk_tb);                // end of data phase
      haddr_i_tb  = '0;
      hwrite_i_tb = 0;
      htrans_i_tb = AHB_HTRANS_IDLE;
      hsel_i_tb   = 0;
    end
  endtask

  // Single 32-bit AHB read
  // Address phase: assert address + NONSEQ for one cycle (no write data)
  // Data   phase:  sample hrdata_o on the next cycle
  task read_single_word(input [31:0] address);
    begin
      // --- Address phase ---
      @(posedge clk_tb);
      hsel_i_tb   = 1;
      haddr_i_tb  = address;
      hwrite_i_tb = 0;
      hready_i_tb = 1;
      htrans_i_tb = AHB_HTRANS_NONSEQ;
      hsize_i_tb  = 3'b010;

      // --- Data phase ---
      // ahb_slv_sif latches dv=1 at this clock edge from the address phase.
      // Release the address bus immediately (address has been captured), then
      // mirror hreadyout_o back to hready_i so the slave cannot overwrite dv
      // with an idle sample while a TLUL response is pending.  Without this,
      // ahb_slv_sif sees hready_i=1 + hsel=0 and clears dv the very next
      // cycle, collapsing dv_i before req_ack fires.
      // For internal-register reads hreadyout_o stays high throughout, so
      // the while body is never entered and hrdata is sampled immediately.
      //
      // #1 (1 ps) after each posedge lets the always_comb in ahb_slv_sif
      // re-evaluate with the newly latched dv before the TB samples
      // hreadyout_o_tb, avoiding a reactive-vs-NBA delta cycle race where
      // the TB reads the stale hreadyout_o=1 and skips the while body.
      @(posedge clk_tb); #1;
      htrans_i_tb = AHB_HTRANS_IDLE;
      hsel_i_tb   = 0;
      haddr_i_tb  = '0;
      while (hreadyout_o_tb !== 1'b1) begin
        hready_i_tb = 0;   // hold slave; prevents dv from being cleared
        @(posedge clk_tb); #1;
      end
      hready_i_tb = 1;
      read_data   = hrdata_o_tb;
    end
  endtask

  //--------------------------------------------------------------------------
  // Entropy seeding
  // The Trivium primitive must have all 9 x 32-bit seed registers written
  // before it generates valid entropy for AES.  Order does not matter.
  // Any non-zero pattern avoids the all-zero Trivium degenerate state.
  //--------------------------------------------------------------------------
  task seed_entropy;
    begin
      $display("[TB] Seeding Trivium entropy (9 x 32-bit writes)...");
      write_single_word(AES_ENTROPY_IF_SEED_0, 32'hDEAD_BEEF);
      write_single_word(AES_ENTROPY_IF_SEED_1, 32'hCAFE_F00D);
      write_single_word(AES_ENTROPY_IF_SEED_2, 32'h1234_5678);
      write_single_word(AES_ENTROPY_IF_SEED_3, 32'hABCD_EF01);
      write_single_word(AES_ENTROPY_IF_SEED_4, 32'h9876_5432);
      write_single_word(AES_ENTROPY_IF_SEED_5, 32'hFEED_C0DE);
      write_single_word(AES_ENTROPY_IF_SEED_6, 32'h0BAD_F00D);
      write_single_word(AES_ENTROPY_IF_SEED_7, 32'hBAB0_5678);
      write_single_word(AES_ENTROPY_IF_SEED_8, 32'h1357_9BDF);
      $display("[TB] Entropy seeding complete.");
    end
  endtask

  //--------------------------------------------------------------------------
  // Status polling
  // Polls the STATUS register via AHB until the requested bit is set.
  // Uses a timeout to prevent infinite loops in simulation.
  //--------------------------------------------------------------------------
  task wait_status_bit(input int bit_pos, input string label);
    int timeout;
    begin
      timeout = 0;
      read_single_word(AES_STATUS);
      while (!read_data[bit_pos]) begin
        timeout++;
        if (timeout > 10000) begin
          $fatal(1, "[TB] TIMEOUT waiting for STATUS[%0d] (%s) after %0d cycles",
                 bit_pos, label, timeout);
        end
        read_single_word(AES_STATUS);
      end
     $display("[TB] STATUS[%0d] (%s) asserted after %0d polls.", bit_pos, label, timeout);
    end
  endtask

  task wait_idle;        wait_status_bit(ST_IDLE,         "IDLE");         endtask
  task wait_input_ready; wait_status_bit(ST_INPUT_READY,  "INPUT_READY");  endtask
  task wait_output_valid;wait_status_bit(ST_OUTPUT_VALID, "OUTPUT_VALID"); endtask

  //--------------------------------------------------------------------------
  // Alternatively, wait on the combinational busy_o port (faster in sim)
  //--------------------------------------------------------------------------
  task wait_not_busy;
    int timeout;
    begin
      timeout = 0;
      while (busy_o_tb) begin
        @(posedge clk_tb);
        timeout++;
        if (timeout > 10000)
          $fatal(1, "[TB] TIMEOUT waiting for busy_o to deassert");
      end
    end
  endtask

  //--------------------------------------------------------------------------
  // CTRL_SHADOWED helpers
  // Shadowed registers require two identical writes to latch.
  //--------------------------------------------------------------------------
  function automatic [31:0] ctrl_word(
    input [1:0]  op,
    input [5:0]  mode,
    input [2:0]  key_len,
    input        manual_op   // 1 = manual, 0 = auto
  );
    // [1:0]=op, [7:2]=mode, [10:8]=key_len, [11]=sideload=0,
    // [14:12]=prng_reseed_rate=PRNG_PER_1=001, [15]=manual_op
    ctrl_word = {manual_op, PRNG_PER_1, 1'b0 /*sideload*/, key_len, mode, op};
  endfunction

  task write_ctrl(input [1:0] op, input [5:0] mode, input [2:0] key_len);
    logic [31:0] w;
    begin
      w = ctrl_word(op, mode, key_len, 1'b1);
      $display("[TB] Writing CTRL_SHADOWED = 0x%08h (op=%0d mode=%06b key_len=%03b)",
               w, op, mode, key_len);
      write_single_word(AES_CTRL_SHADOWED, w);  // first write
      write_single_word(AES_CTRL_SHADOWED, w);  // confirm write (shadowed protocol)
    end
  endtask

  task write_gcm_ctrl(input [5:0] phase, input [4:0] num_valid_bytes);
    logic [31:0] w;
    begin
      w = {21'b0, num_valid_bytes, phase};
      $display("[TB] Writing CTRL_GCM_SHADOWED = 0x%08h (phase=%06b nvb=%0d)",
               w, phase, num_valid_bytes);
      write_single_word(AES_CTRL_GCM_SHADOWED, w);  // first write
      write_single_word(AES_CTRL_GCM_SHADOWED, w);  // confirm write
    end
  endtask

  //--------------------------------------------------------------------------
  // Key write (software key - share0 = key, share1 = 0)
  // AES key words are written MSW-first and Byte reorder to LE: 
  // KEY_SHARE0_0 = key[255:224] becomes
  // KEY_SHARE0_0 = {key[231:224], key[239:232], key[247:240], key[255:248]}
  //--------------------------------------------------------------------------
  task write_key(input [255:0] key);
    begin
      write_single_word(AES_KEY_SHARE0_0, {key[231:224], key[239:232], key[247:240], key[255:248]});
      write_single_word(AES_KEY_SHARE0_1, {key[199:192], key[207:200], key[215:208], key[223:216]});
      write_single_word(AES_KEY_SHARE0_2, {key[167:160], key[175:168], key[183:176], key[191:184]});
      write_single_word(AES_KEY_SHARE0_3, {key[135:128], key[143:136], key[151:144], key[159:152]});
      write_single_word(AES_KEY_SHARE0_4, {key[103: 96], key[111:104], key[119:112], key[127:120]});
      write_single_word(AES_KEY_SHARE0_5, {key[ 71: 64], key[ 79: 72], key[ 87: 80], key[ 95: 88]});
      write_single_word(AES_KEY_SHARE0_6, {key[ 39: 32], key[ 47: 40], key[ 55: 48], key[ 63: 56]});
      write_single_word(AES_KEY_SHARE0_7, {key[  7:  0], key[ 15:  8], key[ 23: 16], key[ 31: 24]});
      // Share1 = 0 (no masking in this TB)
      write_single_word(AES_KEY_SHARE1_0, 32'h0);
      write_single_word(AES_KEY_SHARE1_1, 32'h0);
      write_single_word(AES_KEY_SHARE1_2, 32'h0);
      write_single_word(AES_KEY_SHARE1_3, 32'h0);
      write_single_word(AES_KEY_SHARE1_4, 32'h0);
      write_single_word(AES_KEY_SHARE1_5, 32'h0);
      write_single_word(AES_KEY_SHARE1_6, 32'h0);
      write_single_word(AES_KEY_SHARE1_7, 32'h0);
    end
  endtask

  //--------------------------------------------------------------------------
  // IV write (128-bit, MSW-first)
  //--------------------------------------------------------------------------
  task write_iv(input [127:0] iv);
    begin
      write_single_word(AES_IV_0, {iv[103:96], iv[111:104], iv[119:112], iv[127:120]});
      write_single_word(AES_IV_1, {iv[ 71:64], iv[ 79: 72], iv[ 87: 80], iv[ 95: 88]});
      write_single_word(AES_IV_2, {iv[ 39:32], iv[ 47: 40], iv[ 55: 48], iv[ 63: 56]});
      write_single_word(AES_IV_3, {iv[  7: 0], iv[ 15:  8], iv[ 23: 16], iv[ 31: 24]});
    end
  endtask

  //--------------------------------------------------------------------------
  // Data IN write (128-bit block, MSW-first)
  //--------------------------------------------------------------------------
  task write_data_in(input [127:0] data);
    begin
      write_single_word(AES_DATA_IN_0, {data[103:96], data[111:104], data[119:112], data[127:120]});
      write_single_word(AES_DATA_IN_1, {data[ 71:64], data[ 79: 72], data[ 87: 80], data[ 95: 88]});
      write_single_word(AES_DATA_IN_2, {data[ 39:32], data[ 47: 40], data[ 55: 48], data[ 63: 56]});
      write_single_word(AES_DATA_IN_3, {data[  7: 0], data[ 15:  8], data[ 23: 16], data[ 31: 24]});
    end
  endtask

  //--------------------------------------------------------------------------
  // Data OUT read (128-bit block, reads in MSW-first order)
  //--------------------------------------------------------------------------
  task read_data_out(output [127:0] data);
    begin
      read_single_word(AES_DATA_OUT_0); data[127:96] = {read_data[ 7: 0], read_data[15: 8], read_data[23:16], read_data[31:24]};
      read_single_word(AES_DATA_OUT_1); data[ 95:64] = {read_data[ 7: 0], read_data[15: 8], read_data[23:16], read_data[31:24]};
      read_single_word(AES_DATA_OUT_2); data[ 63:32] = {read_data[ 7: 0], read_data[15: 8], read_data[23:16], read_data[31:24]};
      read_single_word(AES_DATA_OUT_3); data[ 31: 0] = {read_data[ 7: 0], read_data[15: 8], read_data[23:16], read_data[31:24]};
    end
  endtask

  //--------------------------------------------------------------------------
  // Trigger start pulse
  //--------------------------------------------------------------------------
  task trigger_start;
    write_single_word(AES_TRIGGER, 32'h1);  // bit[0] = start
  endtask

  //--------------------------------------------------------------------------
  // aes_run - mid-level ECB/CBC/CTR encrypt or decrypt
  // Handles N 128-bit blocks using the programmer's guide sequence.
  //
  // Parameters:
  //   op       : AES_OP_ENC or AES_OP_DEC
  //   mode     : AES_MODE_ECB / AES_MODE_CBC / AES_MODE_CTR
  //   key_len  : AES_KEY_128 / AES_KEY_192 / AES_KEY_256
  //   key      : 256-bit key (padded with zeros for 128/192-bit keys)
  //   iv       : 128-bit IV (ignored for ECB)
  //   data_in  : input block array
  //   data_out : output block array (allocated by caller, same size)
  //   N        : number of blocks
  //--------------------------------------------------------------------------
  task automatic aes_run(
    input  [1:0]  op,
    input  [5:0]  mode,
    input  [2:0]  key_len,
    input  [255:0] key,
    input  [127:0] iv,
    input  [127:0] data_in  [],
    inout  [127:0] data_out [],
    input  int     N
  );
    int blk;
    logic [127:0] block_out;
    begin
      $display("[TB] aes_run: op=%0d mode=%06b key_len=%03b N=%0d", op, mode, key_len, N);

      // Step 1: Wait IDLE, write CTRL (shadowed), write key, write IV
      wait_idle();
      write_ctrl(op, mode, key_len);
      wait_idle();
      write_key(key);
      if (mode != AES_MODE_ECB)
      begin
        wait_idle();
        write_iv(iv);
      end

      // Step 2: For each block
      for (blk = 0; blk < N; blk++) begin
        $display("[TB] aes_run: starting block %0d", blk);

        // Wait INPUT_READY, write data, trigger start
        wait_input_ready();
        write_data_in(data_in[blk]);
        trigger_start();

        // Wait OUTPUT_VALID, read result
        wait_output_valid();
        read_data_out(block_out);
        data_out[blk] = block_out;
        $display("[TB] Block %0d out: %032h", blk, data_out[blk]);
      end

      $display("[TB] aes_run: complete.");
    end
  endtask

  //--------------------------------------------------------------------------
  // Result check helper
  //--------------------------------------------------------------------------
  task check_result(
    input [127:0] got,
    input [127:0] expected,
    input string  test_name
  );
    if (got === expected) begin
      $display("[TB] PASS: %s", test_name);
      $display("[TB]   got      = %032h", got);
    end else begin
      $display("[TB] FAIL: %s", test_name);
      $display("[TB]   got      = %032h", got);
      $display("[TB]   expected = %032h", expected);
      $fatal(1, "[TB] Test FAILED: %s", test_name);      
    end
  endtask

  //==========================================================================
  // ACVP helper functions
  //==========================================================================

  // Convert 8-char hex substring at offset into a 32-bit value
  function automatic [31:0] hexstr_to_32(input string s, input int offset);
    string slice;
    slice = s.substr(offset, offset + 7);
    return slice.atohex();
  endfunction

  // Convert a 32-char hex string into a 128-bit value (MSB-first)
  function automatic [127:0] hexstr_to_128(input string s);
    hexstr_to_128[127:96] = hexstr_to_32(s,  0);
    hexstr_to_128[ 95:64] = hexstr_to_32(s,  8);
    hexstr_to_128[ 63:32] = hexstr_to_32(s, 16);
    hexstr_to_128[ 31: 0] = hexstr_to_32(s, 24);
  endfunction

  // Convert a hex string into a 256-bit value; nwords = 4/6/8 for 128/192/256-bit key
  // Upper bits hold the key; lower bits zero for shorter keys.
  function automatic [255:0] hexstr_to_256(input string s, input int nwords);
    logic [255:0] result;
    result = '0;
    for (int i = 0; i < nwords; i++) begin
      result[255 - i*32 -: 32] = hexstr_to_32(s, i*8);
    end
    return result;
  endfunction

  // Map key-length integer to AES_KEY_* parameter
  function automatic [2:0] keylen_int_to_param(input int klen);
    case (klen)
      128:     return AES_KEY_128;
      192:     return AES_KEY_192;
      256:     return AES_KEY_256;
      default: return AES_KEY_128;
    endcase
  endfunction

  // Map direction string to AES_OP_* parameter
  function automatic [1:0] dir_to_op(input string d);
    if (d == "encrypt") return AES_OP_ENC;
    else                return AES_OP_DEC;
  endfunction

  // Derive response filename: insert "_resp" before the last '.' extension.
  // e.g. "../stimulus/acvp/ACVP-AES-ECB.txt" -> "../stimulus/acvp/ACVP-AES-ECB_resp.txt"
  function automatic string make_resp_filename(input string fname);
    int dot_pos;
    dot_pos = -1;
    for (int i = fname.len() - 1; i >= 0; i--) begin
      if (fname.substr(i, i) == ".") begin
        dot_pos = i;
        break;
      end
    end
    if (dot_pos < 0)
      return {fname, "_resp"};
    else
      return {fname.substr(0, dot_pos - 1), "_resp", fname.substr(dot_pos, fname.len() - 1)};
  endfunction

  //==========================================================================
  // aes_run_one_block
  // Lightweight single-block helper for MCT inner loops.
  //==========================================================================
  task automatic aes_run_one_block(
    input  [1:0]   op,
    input  [5:0]   mode,
    input  [2:0]   key_len,
    input  [255:0] key,
    input  [127:0] iv,
    input  [127:0] pt,
    output [127:0] ct,
    output [127:0] iv_out
  );
    begin
      wait_idle();
      write_ctrl(op, mode, key_len);
      wait_idle();
      write_key(key);
      if (mode != AES_MODE_ECB) begin
        wait_idle();
        write_iv(iv);
      end
      wait_input_ready();
      write_data_in(pt);
      trigger_start();
      wait_output_valid();
      read_data_out(ct);
      if (mode != AES_MODE_ECB) begin
        // Read back IV register to get DUT's updated IV
        // For CBC/CFB/OFB: DUT manages IV internally; we derive it in caller
        iv_out = '0;
      end else begin
        iv_out = '0;
      end
    end
  endtask

  //==========================================================================
  // aes_run_gcm
  // GCM encrypt via AHB. IV field in ACVP is a 96-bit nonce.
  //==========================================================================
  task automatic aes_run_gcm(
    input  [2:0]   key_len,
    input  [255:0] key,
    input  [95:0]  nonce,
    input  [127:0] aad [],
    input  [4:0]   aad_nvb,
    input  [127:0] pt [],
    input  [4:0]   text_nvb,
    output [127:0] ct [],
    output [127:0] tag
  );
    int n_aad, n_pt, i;
    begin
      n_aad = aad.size();
      n_pt  = pt.size();
      ct    = new[n_pt];

      // Step 1: wait idle
      wait_idle();

      // Step 2: write CTRL in automatic mode (manual_op=0) so INIT self-completes.
      // INIT runs two internal AES operations (H and S) that produce no DATA_OUT;
      // a manual trigger would persist and cause an infinite S-recomputation loop.
      begin
        logic [31:0] w;
        w = ctrl_word(AES_OP_ENC, AES_MODE_GCM, key_len, 1'b0);
        write_single_word(AES_CTRL_SHADOWED, w);
        write_single_word(AES_CTRL_SHADOWED, w);
      end

      // Step 3: GCM INIT — write key then IV; DUT auto-starts H then S derivation.
      // Counter advances from 0 -> 1 (H step) -> 2 = J0+1 (S step).
      write_gcm_ctrl(GCM_INIT, 5'd16);
      write_key(key);
      wait_idle();
      write_iv({nonce, 32'h0000_0000});
      wait_idle(); // blocks until both H and S are derived and core is idle

      // Step 4: process AAD blocks.
      // AAD is GHASH-only; the cipher core is not used and DATA_OUT is never written.
      // Poll input_ready (not output_valid) between blocks.
      for (i = 0; i < n_aad; i++) begin
        automatic logic [4:0] nvb;
        nvb = (i == n_aad - 1) ? aad_nvb : 5'd16;
        wait_input_ready();
        write_gcm_ctrl(GCM_AAD, nvb);
        write_data_in(aad[i]);
      end
      // Wait for the GHASH to fully complete the last AAD block before changing phase.
      // ctrl_gcm_we_o is only granted in CTRL_IDLE; wait_input_ready() returns while
      // the FSM is still in CTRL_GHASH_READY (GHASH multiply in progress), causing
      // the GCM_TEXT write to be silently dropped. wait_idle() blocks until
      // ghash_in_ready_i=1 (GHASH back in GHASH_IDLE) AND FSM is in CTRL_IDLE.
      if (n_aad > 0) wait_idle();

      // Step 5: process PT blocks.
      // Counter is already at J0+1 from INIT; do not re-write IV.
      // In auto mode each write_data_in triggers the operation.
      for (i = 0; i < n_pt; i++) begin
        automatic logic [4:0] nvb;
        nvb = (i == n_pt - 1) ? text_nvb : 5'd16;
        wait_input_ready();
        write_gcm_ctrl(GCM_TEXT, nvb);
        write_data_in(pt[i]);
        wait_output_valid();
        read_data_out(ct[i]);
      end

      // Step 6: write length block [len(AAD) in bits || len(CT) in bits], then read tag.
      // Must wait for full GHASH idle before writing GCM_TAG: the GHASH samples
      // gcm_phase_i in GHASH_MASKED_ADD_CORR to decide GHASH_IDLE vs GHASH_OUT.
      // If GCM_TAG is written while the last CT block's GHASH multiply is still
      // running, the GHASH prematurely takes the TAG path and deadlocks with the FSM.
      begin
        automatic logic [127:0] len_block;
        automatic int           aad_bytes, ct_bytes;
        aad_bytes = (n_aad == 0) ? 0 : (n_aad - 1) * 16 + int'(aad_nvb);
        ct_bytes  = (n_pt  == 0) ? 0 : (n_pt  - 1) * 16 + int'(text_nvb);
        len_block = {64'(aad_bytes * 8), 64'(ct_bytes * 8)};
        wait_idle();
        write_gcm_ctrl(GCM_TAG, 5'd16);
        write_data_in(len_block);
        wait_output_valid();
        read_data_out(tag);
      end
    end
  endtask

  //==========================================================================
  // MCT key-update helper
  // Returns new 256-bit key (upper bits used for shorter keys)
  //==========================================================================
  function automatic [255:0] update_key(
    input [255:0] key,
    input [127:0] ct,
    input [127:0] ct_prev,
    input int     key_len
  );
    case (key_len)
      128: begin
        // 128-bit key lives in key[255:128]; XOR with last CT
        update_key[255:128] = key[255:128] ^ ct;
        update_key[127:  0] = key[127:  0];
      end
      192: begin
        // NIST: new_key = old_key XOR last-192-bits-of-{CT[j-1]||CT[j]}
        // Last 192 bits of the 256-bit concat = {CT[j-1][63:0], CT[j]}
        // key is stored in bits [255:64] of the 256-bit container
        update_key[255:64] = key[255:64] ^ {ct_prev[63:0], ct};
        update_key[ 63: 0] = key[63:0];
      end
      256: begin
        update_key = key ^ {ct_prev, ct};
      end
      default: update_key = key ^ {128'h0, ct};
    endcase
  endfunction

  //==========================================================================
  // ACVP per-mode test tasks
  //==========================================================================

  //--------------------------------------------------------------------------
  // acvp_ecb_test
  //--------------------------------------------------------------------------
  task automatic acvp_ecb_test;
    integer fin, fout;
    integer result;
    string  in_fname, out_fname;
    string  mode_str, test_type, direction;
    int     key_len_int, tgid, tcid;
    string  data_str, key_str;
    logic [127:0] pt, ct, ct_prev, pt_prev;
    logic [255:0] key;
    logic [1:0]   op;
    logic [2:0]   key_len;
    logic [127:0] data_in  [];
    logic [127:0] data_out [];
    logic [127:0] iv_dummy;
    // MCT state
    logic [127:0] key_save, ct_save, pt_save;
    logic [255:0] key256_save;
    begin
      in_fname  = "../stimulus/acvp/ACVP-AES-ECB.txt";
      out_fname = make_resp_filename(in_fname);
      fin  = $fopen(in_fname, "r");
      if (fin == 0) begin
        $display("[TB] acvp_ecb_test: input file not found, skipping.");
        return;
      end
      fout = $fopen(out_fname, "w");
      if (fout == 0) begin
        $display("[TB] acvp_ecb_test: cannot open output file.");
        $fclose(fin);
        return;
      end

      while (1) begin
        result = $fscanf(fin, "%s %s %s %d %d %d %s %s",
                         mode_str, test_type, direction, key_len_int, tgid, tcid,
                         data_str, key_str);
        if (result != 8) break;

        op      = dir_to_op(direction);
        key_len = keylen_int_to_param(key_len_int);
        key     = hexstr_to_256(key_str, key_len_int / 32);

        if (test_type == "AFT") begin
          automatic int nblocks;
          nblocks  = data_str.len() / 32;
          data_in  = new[nblocks];
          data_out = new[nblocks];
          for (int b = 0; b < nblocks; b++) begin
            data_in[b][127:96] = hexstr_to_32(data_str, b*32 +  0);
            data_in[b][ 95:64] = hexstr_to_32(data_str, b*32 +  8);
            data_in[b][ 63:32] = hexstr_to_32(data_str, b*32 + 16);
            data_in[b][ 31: 0] = hexstr_to_32(data_str, b*32 + 24);
          end
          aes_run(op, AES_MODE_ECB, key_len, key, 128'h0, data_in, data_out, nblocks);
          $fwrite(fout, "AFT %0d ", tcid);
          for (int b = 0; b < nblocks; b++)
            $fwrite(fout, "%032h", data_out[b]);
          $fwrite(fout, "\n");
        end else if (test_type == "MCT") begin
          // ECB MCT encrypt: pt=data_str seed
          pt       = hexstr_to_128(data_str);
          ct_prev  = 128'h0;
          key256_save = key;
          pt_save  = pt;
          for (int i = 0; i < 100; i++) begin
            automatic string key_hex;
            key256_save = key;
            pt_save     = pt;
            for (int j = 0; j < 1000; j++) begin
              ct_prev = pt;  // CT[j-1] = PT[j] (since PT[j+1] = CT[j])
              aes_run_one_block(op, AES_MODE_ECB, key_len, key, 128'h0, pt, ct, iv_dummy);
              pt = ct;       // PT[j+1] = CT[j]
            end
            key = update_key(key, ct, ct_prev, key_len_int); // update once after j=999
            case (key_len_int)
              192:    key_hex = $sformatf("%048h", key256_save[255:64]);
              256:    key_hex = $sformatf("%064h", key256_save[255:0]);
              default:key_hex = $sformatf("%032h", key256_save[255:128]);
            endcase
            $fwrite(fout, "MCT %0d %s %032h %032h\n", tcid, key_hex, pt_save, ct);
          end
        end
      end

      $fclose(fin);
      $fclose(fout);
      $display("[TB] acvp_ecb_test complete.");
    end
  endtask

  //--------------------------------------------------------------------------
  // acvp_cbc_test
  //--------------------------------------------------------------------------
  task automatic acvp_cbc_test;
    integer fin, fout;
    integer result;
    string  in_fname, out_fname;
    string  mode_str, test_type, direction;
    int     key_len_int, tgid, tcid;
    string  iv_str, data_str, key_str;
    logic [127:0] pt, ct, ct_prev, iv, iv_prev;
    logic [255:0] key;
    logic [1:0]   op;
    logic [2:0]   key_len;
    logic [127:0] data_in  [];
    logic [127:0] data_out [];
    logic [127:0] iv_dummy;
    logic [127:0] iv_dec_dummy;
    logic [127:0] iv_save, pt_save, ct_save;
    logic [127:0] pt_prev;
    logic [255:0] key256_save;
    begin
      in_fname  = "../stimulus/acvp/ACVP-AES-CBC.txt";
      out_fname = make_resp_filename(in_fname);
      fin  = $fopen(in_fname, "r");
      if (fin == 0) begin
        $display("[TB] acvp_cbc_test: input file not found, skipping.");
        return;
      end
      fout = $fopen(out_fname, "w");
      if (fout == 0) begin
        $display("[TB] acvp_cbc_test: cannot open output file.");
        $fclose(fin);
        return;
      end

      while (1) begin
        result = $fscanf(fin, "%s %s %s %d %d %d %s %s %s",
                         mode_str, test_type, direction, key_len_int, tgid, tcid,
                         iv_str, data_str, key_str);
        if (result != 9) break;

        op      = dir_to_op(direction);
        key_len = keylen_int_to_param(key_len_int);
        key     = hexstr_to_256(key_str, key_len_int / 32);
        iv      = hexstr_to_128(iv_str);

        if (test_type == "AFT") begin
          begin
            int n_blk;
            string ct_hex;
            n_blk    = (data_str.len() + 31) / 32;
            data_in  = new[n_blk];
            data_out = new[n_blk];
            for (int b = 0; b < n_blk; b++) begin
              automatic int    bs = b * 32;
              automatic string blk;
              if (bs + 32 <= data_str.len())
                blk = data_str.substr(bs, bs + 31);
              else begin
                blk = data_str.substr(bs, data_str.len() - 1);
                while (blk.len() < 32) blk = {blk, "0"};
              end
              data_in[b] = hexstr_to_128(blk);
            end
            aes_run(op, AES_MODE_CBC, key_len, key, iv, data_in, data_out, n_blk);
            ct_hex = "";
            for (int b = 0; b < n_blk; b++)
              ct_hex = $sformatf("%s%032h", ct_hex, data_out[b]);
            $fwrite(fout, "AFT %0d %s\n", tcid, ct_hex);
          end
        end else if (test_type == "MCT") begin
          if (op == AES_OP_ENC) begin
            // CBC ENCRYPT MCT
            pt      = hexstr_to_128(data_str);
            ct      = 128'h0;
            ct_prev = 128'h0;
            for (int i = 0; i < 100; i++) begin
              automatic string key_hex;
              key256_save = key;
              iv_save     = iv;
              pt_save     = pt;
              wait_idle();
              write_ctrl(AES_OP_ENC, AES_MODE_CBC, key_len);
              wait_idle();
              write_key(key);
              wait_idle();
              write_iv(iv);
              for (int j = 0; j < 1000; j++) begin
                iv_prev = iv;
                wait_input_ready();
                write_data_in(pt);
                trigger_start();
                wait_output_valid();
                ct_prev = ct;
                read_data_out(ct);
                iv = ct;
                pt = iv_prev;
              end
              key = update_key(key, ct, ct_prev, key_len_int);
              case (key_len_int)
                192:    key_hex = $sformatf("%048h", key256_save[255:64]);
                256:    key_hex = $sformatf("%064h", key256_save[255:0]);
                default:key_hex = $sformatf("%032h", key256_save[255:128]);
              endcase
              $fwrite(fout, "MCT %0d %s %032h %032h %032h\n",
                      tcid, key_hex, iv_save, pt_save, ct);
              $fflush(fout);
            end
          end else begin
            // CBC DECRYPT MCT (NIST SP 800-38A)
            ct      = hexstr_to_128(data_str);
            pt      = 128'h0;
            pt_prev = 128'h0;
            for (int i = 0; i < 100; i++) begin
              automatic string key_hex;
              key256_save = key;
              iv_save     = iv;
              ct_save     = ct;
              for (int j = 0; j < 1000; j++) begin
                pt_prev = pt;
                aes_run_one_block(AES_OP_DEC, AES_MODE_CBC, key_len, key, iv, ct, pt, iv_dec_dummy);
                iv = ct;
                if (j == 0)
                  ct = iv_save;
                else
                  ct = pt_prev;
              end
              iv = pt;
              ct = pt_prev;
              key = update_key(key, pt, pt_prev, key_len_int);
              case (key_len_int)
                192:    key_hex = $sformatf("%048h", key256_save[255:64]);
                256:    key_hex = $sformatf("%064h", key256_save[255:0]);
                default:key_hex = $sformatf("%032h", key256_save[255:128]);
              endcase
              $fwrite(fout, "MCT %0d %s %032h %032h %032h\n",
                      tcid, key_hex, iv_save, pt, ct_save);
              $fflush(fout);
            end
          end
        end
      end

      $fclose(fin);
      $fclose(fout);
      $display("[TB] acvp_cbc_test complete.");
    end
  endtask

  //--------------------------------------------------------------------------
  // acvp_cfb128_test  (encrypt only)
  //--------------------------------------------------------------------------
  task automatic acvp_cfb128_test;
    integer fin, fout;
    integer result;
    string  in_fname, out_fname;
    string  mode_str, test_type, direction;
    int     key_len_int, tgid, tcid;
    string  iv_str, data_str, key_str;
    logic [127:0] pt, ct, ct_prev, iv, iv_prev;
    logic [255:0] key;
    logic [2:0]   key_len;
    logic [127:0] data_in  [];
    logic [127:0] data_out [];
    logic [127:0] iv_dummy;
    logic [127:0] iv_save, pt_save;
    logic [255:0] key256_save;
    begin
      in_fname  = "../stimulus/acvp/ACVP-AES-CFB128.txt";
      out_fname = make_resp_filename(in_fname);
      fin  = $fopen(in_fname, "r");
      if (fin == 0) begin
        $display("[TB] acvp_cfb128_test: input file not found, skipping.");
        return;
      end
      fout = $fopen(out_fname, "w");
      if (fout == 0) begin
        $display("[TB] acvp_cfb128_test: cannot open output file.");
        $fclose(fin);
        return;
      end

      while (1) begin
        result = $fscanf(fin, "%s %s %s %d %d %d %s %s %s",
                         mode_str, test_type, direction, key_len_int, tgid, tcid,
                         iv_str, data_str, key_str);
        if (result != 9) break;

        key_len = keylen_int_to_param(key_len_int);
        key     = hexstr_to_256(key_str, key_len_int / 32);
        iv      = hexstr_to_128(iv_str);

        if (test_type == "AFT") begin
          begin
            int n_blk;
            string ct_hex;
            n_blk    = (data_str.len() + 31) / 32;
            data_in  = new[n_blk];
            data_out = new[n_blk];
            for (int b = 0; b < n_blk; b++) begin
              automatic int    bs = b * 32;
              automatic string blk;
              if (bs + 32 <= data_str.len())
                blk = data_str.substr(bs, bs + 31);
              else begin
                blk = data_str.substr(bs, data_str.len() - 1);
                while (blk.len() < 32) blk = {blk, "0"};
              end
              data_in[b] = hexstr_to_128(blk);
            end
            aes_run(AES_OP_ENC, AES_MODE_CFB, key_len, key, iv, data_in, data_out, n_blk);
            ct_hex = "";
            for (int b = 0; b < n_blk; b++)
              ct_hex = $sformatf("%s%032h", ct_hex, data_out[b]);
            $fwrite(fout, "AFT %0d %s\n", tcid, ct_hex);
          end
        end else if (test_type == "MCT") begin
          pt      = hexstr_to_128(data_str);
          ct_prev = 128'h0;
          for (int i = 0; i < 100; i++) begin
            automatic string key_hex;
            key256_save = key;
            iv_save     = iv;
            pt_save     = pt;
            for (int j = 0; j < 1000; j++) begin
              iv_prev = iv;
              aes_run_one_block(AES_OP_ENC, AES_MODE_CFB, key_len, key, iv, pt, ct, iv_dummy);
              iv      = ct;      // IV[j+1] = CT[j] (CFB feedback)
              pt      = iv_prev; // PT[j+1] = IV[i] (j=0) or CT[j-1] (j>0)
            end
            // After j=999: ct=CT[999], pt=CT[998] (via iv_prev), iv=CT[999]
            key = update_key(key, ct, pt, key_len_int); // CT[999], CT[998]; once after j=999
            // iv = CT[999] and pt = CT[998] already set for next outer iteration
            case (key_len_int)
              192:    key_hex = $sformatf("%048h", key256_save[255:64]);
              256:    key_hex = $sformatf("%064h", key256_save[255:0]);
              default:key_hex = $sformatf("%032h", key256_save[255:128]);
            endcase
            $fwrite(fout, "MCT %0d %s %032h %032h %032h\n",
                    tcid, key_hex, iv_save, pt_save, ct);
          end
        end
      end

      $fclose(fin);
      $fclose(fout);
      $display("[TB] acvp_cfb128_test complete.");
    end
  endtask

  //--------------------------------------------------------------------------
  // acvp_ofb_test  (encrypt only)
  //--------------------------------------------------------------------------
  task automatic acvp_ofb_test;
    integer fin, fout;
    integer result;
    string  in_fname, out_fname;
    string  mode_str, test_type, direction;
    int     key_len_int, tgid, tcid;
    string  iv_str, data_str, key_str;
    logic [127:0] pt, ct, ct_prev, iv, o_blk;
    logic [255:0] key;
    logic [2:0]   key_len;
    logic [127:0] data_in  [];
    logic [127:0] data_out [];
    logic [127:0] iv_dummy;
    logic [127:0] iv_save, pt_save;
    logic [255:0] key256_save;
    begin
      in_fname  = "../stimulus/acvp/ACVP-AES-OFB.txt";
      out_fname = make_resp_filename(in_fname);
      fin  = $fopen(in_fname, "r");
      if (fin == 0) begin
        $display("[TB] acvp_ofb_test: input file not found, skipping.");
        return;
      end
      fout = $fopen(out_fname, "w");
      if (fout == 0) begin
        $display("[TB] acvp_ofb_test: cannot open output file.");
        $fclose(fin);
        return;
      end

      while (1) begin
        result = $fscanf(fin, "%s %s %s %d %d %d %s %s %s",
                         mode_str, test_type, direction, key_len_int, tgid, tcid,
                         iv_str, data_str, key_str);
        if (result != 9) break;

        key_len = keylen_int_to_param(key_len_int);
        key     = hexstr_to_256(key_str, key_len_int / 32);
        iv      = hexstr_to_128(iv_str);

        if (test_type == "AFT") begin
          begin
            int n_blk;
            string ct_hex;
            n_blk    = (data_str.len() + 31) / 32;
            data_in  = new[n_blk];
            data_out = new[n_blk];
            for (int b = 0; b < n_blk; b++) begin
              automatic int    bs = b * 32;
              automatic string blk;
              if (bs + 32 <= data_str.len())
                blk = data_str.substr(bs, bs + 31);
              else begin
                blk = data_str.substr(bs, data_str.len() - 1);
                while (blk.len() < 32) blk = {blk, "0"};
              end
              data_in[b] = hexstr_to_128(blk);
            end
            aes_run(AES_OP_ENC, AES_MODE_OFB, key_len, key, iv, data_in, data_out, n_blk);
            ct_hex = "";
            for (int b = 0; b < n_blk; b++)
              ct_hex = $sformatf("%s%032h", ct_hex, data_out[b]);
            $fwrite(fout, "AFT %0d %s\n", tcid, ct_hex);
          end
        end else if (test_type == "MCT") begin
          pt      = hexstr_to_128(data_str);
          ct_prev = 128'h0;
          for (int i = 0; i < 100; i++) begin
            automatic string key_hex;
            key256_save = key;
            iv_save     = iv;
            pt_save     = pt;
            for (int j = 0; j < 1000; j++) begin
              aes_run_one_block(AES_OP_ENC, AES_MODE_OFB, key_len, key, iv, pt, ct, iv_dummy);
              o_blk   = ct ^ pt;      // O[j] = keystream block
              iv      = o_blk;        // IV[j+1] = O[j]
              if (j == 0)
                pt = iv_save;         // PT[1] = IV[i] (NIST OFB MCT)
              else
                pt = ct_prev;         // PT[j+1] = CT[j-1] (NIST OFB MCT)
              ct_prev = ct;           // save CT[j] for next iteration
            end
            // After j=999: ct=CT[999], pt=CT[998], ct_prev=CT[999]
            key = update_key(key, ct, pt, key_len_int); // CT[999], CT[998]; once after j=999
            iv  = ct;                                    // IV[i+1] = CT[999]
            // pt = CT[998] already; serves as PT[0] for next outer iteration
            case (key_len_int)
              192:    key_hex = $sformatf("%048h", key256_save[255:64]);
              256:    key_hex = $sformatf("%064h", key256_save[255:0]);
              default:key_hex = $sformatf("%032h", key256_save[255:128]);
            endcase
            $fwrite(fout, "MCT %0d %s %032h %032h %032h\n",
                    tcid, key_hex, iv_save, pt_save, ct);
          end
        end
      end

      $fclose(fin);
      $fclose(fout);
      $display("[TB] acvp_ofb_test complete.");
    end
  endtask

  //--------------------------------------------------------------------------
  // acvp_ctr_test  (encrypt only, AFT only)
  //--------------------------------------------------------------------------
  task automatic acvp_ctr_test;
    integer fin, fout;
    string  in_fname, out_fname;
    integer result;
    string  mode_str, test_type, direction;
    int     key_len_int, tgid, tcid;
    string  iv_str, data_str, key_str;
    logic [127:0] iv;
    logic [255:0] key;
    logic [2:0]   key_len;
    logic [127:0] data_in  [];
    logic [127:0] data_out [];
    begin
      in_fname  = "../stimulus/acvp/ACVP-AES-CTR.txt";
      out_fname = make_resp_filename(in_fname);
      fin  = $fopen(in_fname, "r");
      if (fin == 0) begin
        $display("[TB] acvp_ctr_test: input file not found, skipping.");
        return;
      end
      fout = $fopen(out_fname, "w");
      if (fout == 0) begin
        $display("[TB] acvp_ctr_test: cannot open output file.");
        $fclose(fin);
        return;
      end

      while (1) begin
        result = $fscanf(fin, "%s %s %s %d %d %d %s %s %s",
                         mode_str, test_type, direction, key_len_int, tgid, tcid,
                         iv_str, data_str, key_str);
        if (result != 9) break;

        key_len  = keylen_int_to_param(key_len_int);
        key      = hexstr_to_256(key_str, key_len_int / 32);
        iv       = hexstr_to_128(iv_str);
        begin
          automatic int nblocks;
          automatic int data_len;
          automatic int last_nvb; // valid bytes in last block (1-16)
          data_len = data_str.len();
          nblocks  = (data_len + 31) / 32; // ceiling: partial last block counts
          last_nvb = (data_len % 32 == 0) ? 16 : (data_len % 32) / 2;
          data_in  = new[nblocks];
          data_out = new[nblocks];
          for (int b = 0; b < nblocks; b++) begin
            automatic string blk;
            automatic int    blk_start;
            blk_start = b * 32;
            if (blk_start + 32 <= data_len) begin
              data_in[b][127:96] = hexstr_to_32(data_str, blk_start +  0);
              data_in[b][ 95:64] = hexstr_to_32(data_str, blk_start +  8);
              data_in[b][ 63:32] = hexstr_to_32(data_str, blk_start + 16);
              data_in[b][ 31: 0] = hexstr_to_32(data_str, blk_start + 24);
            end else begin
              // Last partial block: pad hex string to 32 chars with trailing zeros
              blk = data_str.substr(blk_start, data_len - 1);
              while (blk.len() < 32) blk = {blk, "0"};
              data_in[b][127:96] = hexstr_to_32(blk,  0);
              data_in[b][ 95:64] = hexstr_to_32(blk,  8);
              data_in[b][ 63:32] = hexstr_to_32(blk, 16);
              data_in[b][ 31: 0] = hexstr_to_32(blk, 24);
            end
          end
          aes_run(AES_OP_ENC, AES_MODE_CTR, key_len, key, iv, data_in, data_out, nblocks);
          $fwrite(fout, "AFT %0d ", tcid);
          for (int b = 0; b < nblocks; b++) begin
            if (b == nblocks - 1 && last_nvb < 16) begin
              automatic string full_hex;
              full_hex = $sformatf("%032h", data_out[b]);
              $fwrite(fout, "%s", full_hex.substr(0, 2*last_nvb - 1));
            end else
              $fwrite(fout, "%032h", data_out[b]);
          end
          $fwrite(fout, "\n");
        end
      end

      $fclose(fin);
      $fclose(fout);
      $display("[TB] acvp_ctr_test complete.");
    end
  endtask

  //--------------------------------------------------------------------------
  // acvp_gcm_test  (encrypt only, AFT only)
  //--------------------------------------------------------------------------
  task automatic acvp_gcm_test;
    integer fin, fout;
    integer result;
    string  in_fname, out_fname;
    string  mode_str, test_type, direction;
    int     key_len_int, tgid, tcid;
    string  iv_str, aad_str, pt_str, key_str;
    logic [95:0]  nonce;
    logic [127:0] aad_blk, pt_blk;
    logic [127:0] aad_arr [], pt_arr [], ct_arr [];
    logic [127:0] tag;
    logic [255:0] key;
    logic [2:0]   key_len;
    int           n_aad, n_pt;
    int           aad_len, pt_len;
    begin
      in_fname  = "../stimulus/acvp/ACVP-AES-GCM.txt";
      out_fname = make_resp_filename(in_fname);
      fin  = $fopen(in_fname, "r");
      if (fin == 0) begin
        $display("[TB] acvp_gcm_test: input file not found, skipping.");
        return;
      end
      fout = $fopen(out_fname, "w");
      if (fout == 0) begin
        $display("[TB] acvp_gcm_test: cannot open output file.");
        $fclose(fin);
        return;
      end

      while (1) begin
        result = $fscanf(fin, "%s %s %s %d %d %d %s %s %s %s",
                         mode_str, test_type, direction, key_len_int, tgid, tcid,
                         iv_str, aad_str, pt_str, key_str);
        if (result != 10)
            break;

        key_len = keylen_int_to_param(key_len_int);
        key     = hexstr_to_256(key_str, key_len_int / 32);

        // Parse 96-bit nonce (24 hex chars)
        nonce = {hexstr_to_32(iv_str, 0), hexstr_to_32(iv_str, 8), hexstr_to_32(iv_str, 16)};

        // Parse AAD blocks. The keyword "empty" in the stimulus file signals no AAD.
        aad_len = (aad_str == "empty") ? 0 : aad_str.len();
        if (aad_len == 0) begin
          n_aad   = 0;
          aad_arr = new[0];
        end else begin
          n_aad   = (aad_len + 31) / 32; // ceil(chars / 32)
          aad_arr = new[n_aad];
          for (int i = 0; i < n_aad; i++) begin
            automatic string blk_str;
            automatic int    blk_start;
            blk_start = i * 32;
            if (blk_start + 32 <= aad_len)
              blk_str = aad_str.substr(blk_start, blk_start + 31);
            else begin
              // Last partial block: pad with zeros
              blk_str = aad_str.substr(blk_start, aad_len - 1);
              while (blk_str.len() < 32) blk_str = {blk_str, "0"};
            end
            aad_arr[i] = hexstr_to_128(blk_str);
          end
        end

        // Parse PT blocks. The keyword "empty" in the stimulus file signals no plaintext.
        pt_len = (pt_str == "empty") ? 0 : pt_str.len();
        if (pt_len == 0) begin
          n_pt   = 0;
          pt_arr = new[0];
        end else begin
          n_pt   = (pt_len + 31) / 32;
          pt_arr = new[n_pt];
          for (int i = 0; i < n_pt; i++) begin
            automatic string blk_str;
            automatic int    blk_start;
            blk_start = i * 32;
            if (blk_start + 32 <= pt_len)
              blk_str = pt_str.substr(blk_start, blk_start + 31);
            else begin
              blk_str = pt_str.substr(blk_start, pt_len - 1);
              while (blk_str.len() < 32) blk_str = {blk_str, "0"};
            end
            pt_arr[i] = hexstr_to_128(blk_str);
          end
        end

        // Run GCM encrypt then write response.
        // aad_len and pt_len are 0 for "empty" fields, so /2 gives correct byte counts.
        // The last CT block is trimmed to last_pt_bytes valid bytes: read_data_out()
        // always returns 16 bytes, but the bytes beyond last_pt_bytes are raw keystream
        // and must not appear in the response file.
        begin
          automatic int    last_aad_bytes, last_pt_bytes;
          automatic string ct_hex, full_hex;
          last_aad_bytes = (n_aad == 0) ? 0
                         : ((aad_len / 2) % 16 == 0) ? 16 : (aad_len / 2) % 16;
          last_pt_bytes  = (n_pt  == 0) ? 0
                         : ((pt_len  / 2) % 16 == 0) ? 16 : (pt_len  / 2) % 16;

          $display("[TB] acvp_gcm_test: tgId=%0d tcId=%0d keyLen=%0d aadBytes=%0d ptBytes=%0d",
                   tgid, tcid, key_len_int, aad_len / 2, pt_len / 2);

          aes_run_gcm(key_len, key, nonce,
                      aad_arr, 5'(last_aad_bytes),
                      pt_arr,  (n_pt > 0) ? 5'(last_pt_bytes) : 5'd0,
                      ct_arr, tag);

          $display("[TB]   tag = %032h", tag);

          // Build CT hex string: full blocks use all 32 chars; last partial block
          // is trimmed to last_pt_bytes*2 hex chars to match PT length exactly.
          ct_hex = "";
          for (int i = 0; i < n_pt; i++) begin
            full_hex = $sformatf("%032h", ct_arr[i]);
            if (i == n_pt - 1 && last_pt_bytes < 16)
              ct_hex = $sformatf("%s%s", ct_hex,
                                 full_hex.substr(0, last_pt_bytes * 2 - 1));
            else
              ct_hex = $sformatf("%s%s", ct_hex, full_hex);
          end
          if (ct_hex == "") ct_hex = "empty";
          $fwrite(fout, "AFT %0d %s %032h\n", tcid, ct_hex, tag);
        end
      end

      $fclose(fin);
      $fclose(fout);
      $display("[TB] acvp_gcm_test complete.");
    end
  endtask

  //--------------------------------------------------------------------------
  // Reset sequence
  //--------------------------------------------------------------------------
  task do_reset;
    begin
      $display("[TB] Asserting reset...");
      reset_n_tb       = 0;
      cptra_pwrgood_tb = 0;
      // initialize AHB signals to idle
      hsel_i_tb   = 0;
      hwrite_i_tb = 0;
      hready_i_tb = 1;
      htrans_i_tb = AHB_HTRANS_IDLE;
      haddr_i_tb  = '0;
      hwdata_i_tb = '0;
      hsize_i_tb  = 3'b010;
      debugUnlock_or_scan_mode_switch_tb = 0;
      repeat(10) @(posedge clk_tb);
      cptra_pwrgood_tb = 1;
      repeat(2)  @(posedge clk_tb);
      reset_n_tb = 1;
      $display("[TB] Reset released.");
      repeat(5)  @(posedge clk_tb);
    end
  endtask

  //==========================================================================
  // Test vectors
  //==========================================================================

  //--------------------------------------------------------------------------
  // Test 1: ECB-AES128 Encrypt - FIPS 197 Appendix B
  //   Key:       2b7e151628aed2a6abf7158809cf4f3c
  //   Plaintext: 3243f6a8885a308d313198a2e0370734
  //   Expected:  3925841d02dc09fbdc118597196a0b32
  //--------------------------------------------------------------------------
  task automatic test_ecb_enc_128;
    logic [127:0] data_in  [];
    logic [127:0] data_out [];
    logic [255:0] key;
    logic [127:0] iv;
    begin
      $display("\n[TB] ========== TEST 1: ECB-AES128 Encrypt (FIPS 197 App B) ==========");
      data_in  = new[1];
      data_out = new[1];
      key      = 256'h2b7e151628aed2a6abf7158809cf4f3c_00000000000000000000000000000000;
      iv       = 128'h0;
      data_in[0] = 128'h3243f6a8885a308d313198a2e0370734;

      aes_run(AES_OP_ENC, AES_MODE_ECB, AES_KEY_128, key, iv, data_in, data_out, 1);

      check_result(data_out[0], 128'h3925841d02dc09fbdc118597196a0b32, "ECB-AES128-ENC FIPS197-AppB");
    end
  endtask

  //--------------------------------------------------------------------------
  // Test 2: ECB-AES128 Decrypt - FIPS 197 Appendix B (inverse)
  //   Key:        2b7e151628aed2a6abf7158809cf4f3c
  //   Ciphertext: 3925841d02dc09fbdc118597196a0b32
  //   Expected:   3243f6a8885a308d313198a2e0370734
  //--------------------------------------------------------------------------
  task automatic test_ecb_dec_128;
    logic [127:0] data_in  [];
    logic [127:0] data_out [];
    logic [255:0] key;
    logic [127:0] iv;
    begin
      $display("\n[TB] ========== TEST 2: ECB-AES128 Decrypt (FIPS 197 App B inverse) ==========");
      data_in  = new[1];
      data_out = new[1];
      key      = 256'h2b7e151628aed2a6abf7158809cf4f3c_00000000000000000000000000000000;
      iv       = 128'h0;
      data_in[0] = 128'h3925841d02dc09fbdc118597196a0b32;

      aes_run(AES_OP_DEC, AES_MODE_ECB, AES_KEY_128, key, iv, data_in, data_out, 1);

      check_result(data_out[0], 128'h3243f6a8885a308d313198a2e0370734, "ECB-AES128-DEC FIPS197-AppB");
    end
  endtask

  //--------------------------------------------------------------------------
  // Test 3: CBC-AES128 Encrypt - NIST SP 800-38A §F.2.1 Block 1
  //   Key: 2b7e151628aed2a6abf7158809cf4f3c
  //   IV:  000102030405060708090a0b0c0d0e0f
  //   PT:  6bc1bee22e409f96e93d7e117393172a
  //   CT:  7649abac8119b246cee98e9b12e9197d
  //--------------------------------------------------------------------------
  task automatic test_cbc_enc_128;
    logic [127:0] data_in  [];
    logic [127:0] data_out [];
    logic [255:0] key;
    logic [127:0] iv;
    begin
      $display("\n[TB] ========== TEST 3: CBC-AES128 Encrypt (NIST SP800-38A F.2.1 Blk1) ==========");
      data_in  = new[1];
      data_out = new[1];
      key      = 256'h2b7e151628aed2a6abf7158809cf4f3c_00000000000000000000000000000000;
      iv       = 128'h000102030405060708090a0b0c0d0e0f;
      data_in[0] = 128'h6bc1bee22e409f96e93d7e117393172a;

      aes_run(AES_OP_ENC, AES_MODE_CBC, AES_KEY_128, key, iv, data_in, data_out, 1);

      check_result(data_out[0], 128'h7649abac8119b246cee98e9b12e9197d, "CBC-AES128-ENC NIST-F.2.1-Blk1");
    end
  endtask

  //--------------------------------------------------------------------------
  // Test 4: CBC-AES128 Decrypt - NIST SP 800-38A §F.2.2 Block 1
  //   Key: 2b7e151628aed2a6abf7158809cf4f3c
  //   IV:  000102030405060708090a0b0c0d0e0f
  //   CT:  7649abac8119b246cee98e9b12e9197d
  //   PT:  6bc1bee22e409f96e93d7e117393172a
  //--------------------------------------------------------------------------
  task automatic test_cbc_dec_128;
    logic [127:0] data_in  [];
    logic [127:0] data_out [];
    logic [255:0] key;
    logic [127:0] iv;
    begin
      $display("\n[TB] ========== TEST 4: CBC-AES128 Decrypt (NIST SP800-38A F.2.2 Blk1) ==========");
      data_in  = new[1];
      data_out = new[1];
      key      = 256'h2b7e151628aed2a6abf7158809cf4f3c_00000000000000000000000000000000;
      iv       = 128'h000102030405060708090a0b0c0d0e0f;
      data_in[0] = 128'h7649abac8119b246cee98e9b12e9197d;

      aes_run(AES_OP_DEC, AES_MODE_CBC, AES_KEY_128, key, iv, data_in, data_out, 1);

      check_result(data_out[0], 128'h6bc1bee22e409f96e93d7e117393172a, "CBC-AES128-DEC NIST-F.2.2-Blk1");
    end
  endtask

  //--------------------------------------------------------------------------
  // Test 5: CTR-AES128 Encrypt - NIST SP 800-38A §F.5.1 Block 1
  //   Key: 2b7e151628aed2a6abf7158809cf4f3c
  //   IC:  f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff  (initial counter block)
  //   PT:  6bc1bee22e409f96e93d7e117393172a
  //   CT:  874d6191b620e3261bef6864990db6ce
  //--------------------------------------------------------------------------
  task automatic test_ctr_enc_128;
    logic [127:0] data_in  [];
    logic [127:0] data_out [];
    logic [255:0] key;
    logic [127:0] iv;
    begin
      $display("\n[TB] ========== TEST 5: CTR-AES128 Encrypt (NIST SP800-38A F.5.1 Blk1) ==========");
      data_in  = new[1];
      data_out = new[1];
      key      = 256'h2b7e151628aed2a6abf7158809cf4f3c_00000000000000000000000000000000;
      iv       = 128'hf0f1f2f3f4f5f6f7f8f9fafbfcfdfeff;
      data_in[0] = 128'h6bc1bee22e409f96e93d7e117393172a;

      aes_run(AES_OP_ENC, AES_MODE_CTR, AES_KEY_128, key, iv, data_in, data_out, 1);

      check_result(data_out[0], 128'h874d6191b620e3261bef6864990db6ce, "CTR-AES128-ENC NIST-F.5.1-Blk1");
    end
  endtask

  //--------------------------------------------------------------------------
  // Test 6: CBC-AES128 Multi-block Encrypt - NIST SP 800-38A §F.2.1 (all 4 blocks)
  //   Key: 2b7e151628aed2a6abf7158809cf4f3c
  //   IV:  000102030405060708090a0b0c0d0e0f
  //   PT:  6bc1bee22e409f96e93d7e117393172a
  //         ae2d8a571e03ac9c9eb76fac45af8e51
  //         30c81c46a35ce411e5fbc1191a0a52ef
  //         f69f2445df4f9b17ad2b417be66c3710
  //   CT:  7649abac8119b246cee98e9b12e9197d
  //         5086cb9b507219ee95db113a917678b2
  //         73bed6b8e3c1743b7116e69e22229516
  //         3ff1caa1681fac09120eca307586e1a7
  //--------------------------------------------------------------------------
  task automatic test_cbc_enc_128_multiblock;
    logic [127:0] data_in  [];
    logic [127:0] data_out [];
    logic [255:0] key;
    logic [127:0] iv;
    begin
      $display("\n[TB] ========== TEST 6: CBC-AES128 Multi-block Encrypt (NIST SP800-38A F.2.1) ==========");
      data_in  = new[4];
      data_out = new[4];
      key        = 256'h2b7e151628aed2a6abf7158809cf4f3c_00000000000000000000000000000000;
      iv         = 128'h000102030405060708090a0b0c0d0e0f;
      data_in[0] = 128'h6bc1bee22e409f96e93d7e117393172a;
      data_in[1] = 128'hae2d8a571e03ac9c9eb76fac45af8e51;
      data_in[2] = 128'h30c81c46a35ce411e5fbc1191a0a52ef;
      data_in[3] = 128'hf69f2445df4f9b17ad2b417be66c3710;

      aes_run(AES_OP_ENC, AES_MODE_CBC, AES_KEY_128, key, iv, data_in, data_out, 4);

      check_result(data_out[0], 128'h7649abac8119b246cee98e9b12e9197d, "CBC-AES128-ENC-MB Blk0");
      check_result(data_out[1], 128'h5086cb9b507219ee95db113a917678b2, "CBC-AES128-ENC-MB Blk1");
      check_result(data_out[2], 128'h73bed6b8e3c1743b7116e69e22229516, "CBC-AES128-ENC-MB Blk2");
      check_result(data_out[3], 128'h3ff1caa1681fac09120eca307586e1a7, "CBC-AES128-ENC-MB Blk3");
    end
  endtask

  //--------------------------------------------------------------------------
  // Test 7: ECB-AES256 Encrypt - FIPS 197 Appendix C.3
  //   Key: 000102030405060708090a0b0c0d0e0f
  //         101112131415161718191a1b1c1d1e1f
  //   PT:  00112233445566778899aabbccddeeff
  //   CT:  8ea2b7ca516745bfeafc49904b496089
  //--------------------------------------------------------------------------
  task automatic test_ecb_enc_256;
    logic [127:0] data_in  [];
    logic [127:0] data_out [];
    logic [255:0] key;
    logic [127:0] iv;
    begin
      $display("\n[TB] ========== TEST 7: ECB-AES256 Encrypt (FIPS 197 App C.3) ==========");
      data_in  = new[1];
      data_out = new[1];
      key      = 256'h000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f;
      iv       = 128'h0;
      data_in[0] = 128'h00112233445566778899aabbccddeeff;

      aes_run(AES_OP_ENC, AES_MODE_ECB, AES_KEY_256, key, iv, data_in, data_out, 1);

      check_result(data_out[0], 128'h8ea2b7ca516745bfeafc49904b496089, "ECB-AES256-ENC FIPS197-AppC3");
    end
  endtask

  //==========================================================================
  // Main
  //==========================================================================
  initial begin
    $display("[TB] AES CLP Wrapper Testbench starting...");

    do_reset();
    seed_entropy();

    // Give a few cycles after seeding before the first operation
    repeat(20) @(posedge clk_tb);

    // Run all test vectors sequentially
    test_ecb_enc_128();
    test_ecb_dec_128();
    test_cbc_enc_128();
    test_cbc_dec_128();
    test_ctr_enc_128();
    test_cbc_enc_128_multiblock();
    test_ecb_enc_256();

    // ACVP file-driven tests (read from stimulus/acvp/, write *_resp.txt)
    acvp_ecb_test();
    acvp_cbc_test();
    acvp_cfb128_test();
    acvp_ofb_test();
    acvp_ctr_test();
    acvp_gcm_test();

    repeat(200) @(posedge clk_tb);
    $display("\n[TB] ========================================");
    $display("[TB] All tests PASSED.");
    $display("[TB] ========================================");
    $finish;
  end

endmodule
