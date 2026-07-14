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
// hmac256.sv
// ------
// HMAC-256/224 top-level wrapper with 32-bit data access.
//
//======================================================================
`include "caliptra_macros.svh"
`include "caliptra_prim_assert.sv"

module hmac256
       import hmac256_param_pkg::*;
       import hmac256_reg_pkg::*;
      #(
        ADDR_WIDTH = 32,
        DATA_WIDTH = 32
      )(
        // Clock and reset.
        input wire           clk,
        input wire           reset_n,
        input wire           cptra_pwrgood,

        // Control.
        input wire           cs,
        input wire           we,

        // Data ports.
        input wire  [ADDR_WIDTH - 1 : 0] address,
        input wire  [DATA_WIDTH - 1 : 0] write_data,
        output wire [DATA_WIDTH - 1 : 0] read_data,

        output logic busy_o,

        output wire error_intr,
        output wire notif_intr,
        input logic debugUnlock_or_scan_mode_switch
      );

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  reg init_reg;
  reg next_reg;
  reg last_reg;
  reg restore_reg;
  reg is_last_op_reg;

  reg mode_reg;

  reg ready_reg;
  reg tag_valid_reg;

  localparam BLOCK_NUM_DWORDS = BLOCK_SIZE / DATA_WIDTH;
  localparam KEY_NUM_DWORDS   = KEY_SIZE / DATA_WIDTH;
  localparam TAG_NUM_DWORDS   = TAG_SIZE / DATA_WIDTH;
  localparam SEED_NUM_DWORDS  = ((LFSR_SEED_SIZE - 1) / DATA_WIDTH) + 1;

  reg [KEY_NUM_DWORDS - 1   : 0][DATA_WIDTH - 1 : 0]    key_reg;
  reg [BLOCK_NUM_DWORDS - 1 : 0][DATA_WIDTH - 1 : 0]    block_reg;
  reg [SEED_NUM_DWORDS - 1  : 0][DATA_WIDTH - 1 : 0]    lfsr_seed_reg;

  logic zeroize_reg;

  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  wire [KEY_SIZE-1 : 0]         core_key;
  wire [BLOCK_SIZE-1 : 0]       core_block;
  wire                          core_ready;
  wire [TAG_SIZE-1 : 0]         core_tag;
  wire                          core_tag_valid;
  wire [TAG_SIZE-1 : 0]         core_restore_digest;
  wire [LFSR_SEED_SIZE-1 : 0]   core_lfsr_seed;
  reg  [TAG_NUM_DWORDS - 1 : 0][DATA_WIDTH - 1 : 0] tag_reg;
  wire [TAG_NUM_DWORDS - 1 : 0][DATA_WIDTH - 1 : 0] tag_next;

  reg [TAG_NUM_DWORDS - 1 : 0][DATA_WIDTH - 1 : 0] get_mask;

  hmac256_reg__in_t hwif_in;
  hmac256_reg__out_t hwif_out;

  logic invalid_cmd_error, invalid_cmd_error_reg, invalid_cmd_error_edge;

  logic core_tag_we;

  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  // Pack the dword-indexed key/block/tag arrays into the wide core
  // ports without an unrolled concatenation.
  generate
    for (genvar i = 0; i < BLOCK_NUM_DWORDS; i++) begin : gen_core_block
      assign core_block[(BLOCK_NUM_DWORDS-1-i)*DATA_WIDTH +: DATA_WIDTH] = block_reg[i];
    end
  endgenerate

  generate
    for (genvar i = 0; i < KEY_NUM_DWORDS; i++) begin : gen_core_key
      assign core_key[(KEY_NUM_DWORDS-1-i)*DATA_WIDTH +: DATA_WIDTH] = key_reg[i];
    end
  endgenerate

  generate
    for (genvar i = 0; i < SEED_NUM_DWORDS; i++) begin : gen_core_lfsr_seed
      assign core_lfsr_seed[(SEED_NUM_DWORDS-1-i)*DATA_WIDTH +: DATA_WIDTH] = lfsr_seed_reg[i];
    end
  endgenerate

  generate
    for (genvar i = 0; i < TAG_NUM_DWORDS; i++) begin : gen_restore_digest
      assign core_restore_digest[(TAG_NUM_DWORDS-1-i)*DATA_WIDTH +: DATA_WIDTH] =
             hwif_out.HMAC256_TAG[i].TAG.value;
    end
  endgenerate

  // Rising edge on core_tag_valid latches the result registers.
  assign core_tag_we = (core_tag_valid & ~tag_valid_reg);

  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  hmac256_core core(
                 .clk(clk),
                 .reset_n(reset_n),
                 .zeroize(zeroize_reg),

                 .init_cmd(init_reg),
                 .next_cmd(next_reg),
                 .last_cmd(last_reg),
                 .mode_cmd(mode_reg),

                 .lfsr_seed(core_lfsr_seed),

                 .key(core_key),

                 .block_msg(core_block),

                 .restore_cmd(restore_reg),
                 .restore_digest(core_restore_digest),

                 .ready(core_ready),
                 .tag(core_tag),
                 .tag_valid(core_tag_valid)
                );


  //----------------------------------------------------------------
  // reg_update
  //
  // Update functionality for all registers in the core.
  // All registers are positive edge triggered with asynchronous
  // active low reset. All registers have write enable.
  //----------------------------------------------------------------
  always @ (posedge clk or negedge reset_n)
    begin : reg_update
      if (!reset_n)
        begin
          tag_reg         <= '0;
          tag_valid_reg   <= '0;
          ready_reg       <= '0;
          is_last_op_reg  <= '0;
        end
      else if (zeroize_reg)
        begin
          tag_reg         <= '0;
          tag_valid_reg   <= '0;
          ready_reg       <= '0;
          is_last_op_reg  <= '0;
        end
      else
        begin
          tag_valid_reg <= core_tag_valid;
          ready_reg     <= core_ready;

          if (init_reg | next_reg | restore_reg)
            is_last_op_reg <= last_reg;

          if (core_tag_we)
            tag_reg <= tag_next;
        end
    end // reg_update

//HMAC register hardware interfaces
assign tag_next = is_last_op_reg ? (core_tag & get_mask) : core_tag;

always_comb begin
  //drive resets to register block
  hwif_in.error_reset_b = cptra_pwrgood;
  hwif_in.reset_b = reset_n;
  //drive hardware writeable registers from hmac core
  hwif_in.HMAC256_NAME[0].NAME.next = HMAC256_CORE_NAME[31:0];
  hwif_in.HMAC256_NAME[1].NAME.next = HMAC256_CORE_NAME[63:32];
  hwif_in.HMAC256_VERSION[0].VERSION.next = HMAC256_CORE_VERSION[31:0];
  hwif_in.HMAC256_VERSION[1].VERSION.next = HMAC256_CORE_VERSION[63:32];
  //Gate CTRL writes while the engine is busy
  hwif_in.HMAC256_CTRL.INIT.swwe = ready_reg;
  hwif_in.HMAC256_CTRL.NEXT.swwe = ready_reg;
  hwif_in.HMAC256_CTRL.LAST.swwe = ready_reg;
  hwif_in.HMAC256_CTRL.MODE.swwe = ready_reg;
  hwif_in.HMAC256_CTRL.RESTORE.swwe = ready_reg;

  //assign hardware readable registers to drive hmac core
  init_reg    = hwif_out.HMAC256_CTRL.INIT.value;
  next_reg    = hwif_out.HMAC256_CTRL.NEXT.value;
  last_reg    = hwif_out.HMAC256_CTRL.LAST.value;
  restore_reg = hwif_out.HMAC256_CTRL.RESTORE.value &
                (hwif_out.HMAC256_CTRL.NEXT.value | hwif_out.HMAC256_CTRL.LAST.value);
  zeroize_reg = hwif_out.HMAC256_CTRL.ZEROIZE.value || debugUnlock_or_scan_mode_switch;
  mode_reg    = hwif_out.HMAC256_CTRL.MODE.value;

  //drive hardware writeable registers from hmac core
  hwif_in.HMAC256_STATUS.READY.next = ready_reg;
  hwif_in.HMAC256_STATUS.VALID.next = tag_valid_reg;
  for (int dword=0; dword < TAG_NUM_DWORDS; dword++) begin
    hwif_in.HMAC256_TAG[dword].TAG.next  = tag_next[(TAG_NUM_DWORDS - 1)-dword];
    hwif_in.HMAC256_TAG[dword].TAG.we    = core_tag_we;
    hwif_in.HMAC256_TAG[dword].TAG.hwclr = zeroize_reg;
  end

  for (int dword=0; dword < KEY_NUM_DWORDS; dword++) begin
    key_reg[dword] = hwif_out.HMAC256_KEY[dword].KEY.value;
    hwif_in.HMAC256_KEY[dword].KEY.we    = 1'b0;
    hwif_in.HMAC256_KEY[dword].KEY.next  = '0;
    hwif_in.HMAC256_KEY[dword].KEY.hwclr = zeroize_reg;
  end
  for (int dword=0; dword < BLOCK_NUM_DWORDS; dword++) begin
    block_reg[dword] = hwif_out.HMAC256_BLOCK[dword].BLOCK.value;
    hwif_in.HMAC256_BLOCK[dword].BLOCK.we    = 1'b0;
    hwif_in.HMAC256_BLOCK[dword].BLOCK.next  = '0;
    hwif_in.HMAC256_BLOCK[dword].BLOCK.hwclr = zeroize_reg;
  end

  for (int dword=0; dword < SEED_NUM_DWORDS; dword++) begin
    lfsr_seed_reg[dword] = hwif_out.HMAC256_LFSR_SEED[dword].LFSR_SEED.value;
  end
end

always_comb begin
  unique case (mode_reg)
    HMAC224_MODE: get_mask = {{(HMAC224_TAG_SIZE/DATA_WIDTH){ {DATA_WIDTH{1'b1}} }},
                              {(HMAC224_TAG_PAD /DATA_WIDTH){ {DATA_WIDTH{1'b0}} }}};
    default:      get_mask = {TAG_NUM_DWORDS{ {DATA_WIDTH{1'b1}} }};
  endcase
end

// Register block
hmac256_reg i_hmac256_reg (
    .clk(clk),
    .rst(1'b0),

    .s_cpuif_req         (cs),
    .s_cpuif_req_is_wr   (we),
    .s_cpuif_addr        (address[HMAC256_REG_ADDR_WIDTH-1:0]),
    .s_cpuif_wr_data     (write_data),
    .s_cpuif_wr_biten    ('1),
    .s_cpuif_req_stall_wr(),
    .s_cpuif_req_stall_rd(),
    .s_cpuif_rd_ack      (),
    .s_cpuif_rd_err      (),
    .s_cpuif_rd_data     (read_data),
    .s_cpuif_wr_ack      (),
    .s_cpuif_wr_err      (),

    .hwif_in (hwif_in),
    .hwif_out(hwif_out)
);

always_comb invalid_cmd_error = (hwif_out.HMAC256_CTRL.LAST.value    & ~hwif_out.HMAC256_CTRL.INIT.value & ~hwif_out.HMAC256_CTRL.NEXT.value & ~hwif_out.HMAC256_CTRL.RESTORE.value)
                              | (hwif_out.HMAC256_CTRL.RESTORE.value & ~hwif_out.HMAC256_CTRL.NEXT.value & ~hwif_out.HMAC256_CTRL.LAST.value);

always_ff @(posedge clk or negedge reset_n)
begin : error_detection
    if(!reset_n) begin
      invalid_cmd_error_reg <= 1'b0;
    end
    else if(zeroize_reg) begin
      invalid_cmd_error_reg <= 1'b0;
    end
    else begin
      invalid_cmd_error_reg <= invalid_cmd_error;
    end
end // error_detection

always_comb invalid_cmd_error_edge = invalid_cmd_error & (!invalid_cmd_error_reg);

//Interrupts hardware interface
assign hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = core_tag_we;

assign hwif_in.intr_block_rf.error_internal_intr_r.error0_sts.hwset = invalid_cmd_error_edge;
assign hwif_in.intr_block_rf.error_internal_intr_r.error1_sts.hwset = 1'b0;
assign hwif_in.intr_block_rf.error_internal_intr_r.error2_sts.hwset = 1'b0;
assign hwif_in.intr_block_rf.error_internal_intr_r.error3_sts.hwset = 1'b0;

assign error_intr = hwif_out.intr_block_rf.error_global_intr_r.intr;
assign notif_intr = hwif_out.intr_block_rf.notif_global_intr_r.intr;

assign busy_o = ~core_ready;

endmodule // hmac256

//======================================================================
// EOF hmac256.sv
//======================================================================
