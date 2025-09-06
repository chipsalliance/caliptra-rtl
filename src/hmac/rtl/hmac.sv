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
// hmac.sv
// ------
// HMAC-512/384 top-level wrapper with 32 bit data access.
//
//======================================================================
//`include "kv_defines.svh"
`include "kv_macros.svh"

module hmac 
       import hmac_param_pkg::*;
       import hmac_reg_pkg::*;
       import kv_defines_pkg::*;      
      #(
        ADDR_WIDTH = 32,
        DATA_WIDTH = 32
      )(
        // Clock and reset.
        input wire           clk,
        input wire           reset_n,
        input wire           cptra_pwrgood,

        //csr key
        input logic [`CLP_CSR_HMAC_KEY_DWORDS-1:0][31:0] cptra_csr_hmac_key,

        // Control.
        input wire           cs,
        input wire           we,

        // Data ports.
        input wire  [ADDR_WIDTH - 1 : 0] address,
        input wire  [DATA_WIDTH - 1 : 0] write_data,
        output wire [DATA_WIDTH - 1 : 0] read_data,

        // KV interface
        output kv_read_t [1:0] kv_read,
        output kv_write_t kv_write,
        input kv_rd_resp_t [1:0] kv_rd_resp,
        input kv_wr_resp_t kv_wr_resp,

        output logic busy_o,

        output wire error_intr,
        output wire notif_intr,
        input logic ocp_lock_in_progress,
        input logic debugUnlock_or_scan_mode_switch
      );

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  reg init_reg;
  reg init_new;

  reg next_reg;
  reg next_new;

  reg mode_reg;
  
  reg ready_reg;
  reg tag_valid_reg;

  localparam BLOCK_SIZE       = 1024;
  localparam KEY_SIZE         = 512;
  localparam TAG_SIZE         = KEY_SIZE;
  localparam LFSR_SEED_SIZE   = 384;
  localparam BLOCK_NUM_DWORDS = BLOCK_SIZE / DATA_WIDTH;
  localparam KEY_NUM_DWORDS   = KEY_SIZE / DATA_WIDTH;
  localparam TAG_NUM_DWORDS   = TAG_SIZE / DATA_WIDTH;
  localparam SEED_NUM_DWORDS  = ((LFSR_SEED_SIZE - 1) / DATA_WIDTH) + 1; 

  reg [KEY_NUM_DWORDS - 1   : 0][DATA_WIDTH - 1 : 0]    key_reg;
  reg [BLOCK_NUM_DWORDS - 1 : 0][DATA_WIDTH - 1 : 0]    block_reg;
  reg [SEED_NUM_DWORDS- 1   : 0][DATA_WIDTH - 1 : 0]    lfsr_seed_reg;

  logic zeroize_reg;

  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  wire [KEY_SIZE-1 : 0]         core_key;
  wire [BLOCK_SIZE-1 : 0]       core_block;
  wire                          core_ready;
  wire [TAG_SIZE-1 : 0]         core_tag;
  wire                          core_tag_valid;
  wire [LFSR_SEED_SIZE-1 : 0]   core_lfsr_seed;
  reg [TAG_NUM_DWORDS - 1 : 0][DATA_WIDTH - 1 : 0] tag_reg;
  reg [TAG_NUM_DWORDS - 1 : 0][DATA_WIDTH - 1 : 0] kv_reg;

  reg [TAG_NUM_DWORDS - 1 : 0][DATA_WIDTH - 1 : 0] get_mask;

  hmac_reg__in_t hwif_in;
  hmac_reg__out_t hwif_out;

  //interface with kv client
  logic kv_key_write_en;
  logic [3:0] kv_key_write_offset;
  logic [31:0] kv_key_write_data;
  logic kv_block_write_en;
  logic [4:0] kv_block_write_offset;
  logic [31:0] kv_block_write_data;
  //KV Read Data Present
  logic kv_key_data_present, kv_key_data_present_set;
  logic [BLOCK_NUM_DWORDS-1:0] block_reg_lock, block_reg_lock_nxt;
  logic kv_block_data_present, kv_block_data_present_set;
  logic kv_data_present, kv_data_present_reset;

  logic dest_keyvault;
  kv_error_code_e kv_key_error, kv_block_error, kv_write_error;
  logic kv_key_ready, kv_key_done;
  logic kv_block_ready, kv_block_done;
  logic kv_write_ready, kv_write_done;

  kv_read_ctrl_reg_t kv_key_read_ctrl_reg;
  kv_read_ctrl_reg_t kv_block_read_ctrl_reg;
  kv_write_ctrl_reg_t kv_write_ctrl_reg;
  kv_read_filter_metrics_t  kv_key_read_metrics;
  kv_read_filter_metrics_t  kv_block_read_metrics;
  kv_write_filter_metrics_t kv_write_metrics;
  logic core_tag_we;

  logic key_zero_error, key_zero_error_reg, key_zero_error_edge;
  logic key_mode_error, key_mode_error_reg, key_mode_error_edge;

  logic error_flag;
  logic error_flag_reg;
  logic error_flag_edge;
  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign core_block = {block_reg[00], block_reg[01], block_reg[02], block_reg[03],
                       block_reg[04], block_reg[05], block_reg[06], block_reg[07],
                       block_reg[08], block_reg[09], block_reg[10], block_reg[11],
                       block_reg[12], block_reg[13], block_reg[14], block_reg[15],
                       block_reg[16], block_reg[17], block_reg[18], block_reg[19],
                       block_reg[20], block_reg[21], block_reg[22], block_reg[23],
                       block_reg[24], block_reg[25], block_reg[26], block_reg[27],
                       block_reg[28], block_reg[29], block_reg[30], block_reg[31]};

  assign core_key = {key_reg[00], key_reg[01], key_reg[02], key_reg[03], key_reg[04], key_reg[05],
                     key_reg[06], key_reg[07], key_reg[08], key_reg[09], key_reg[10], key_reg[11],
                     key_reg[12], key_reg[13], key_reg[14], key_reg[15]} & get_mask;

  assign core_lfsr_seed = {lfsr_seed_reg[00], lfsr_seed_reg[01], lfsr_seed_reg[02], lfsr_seed_reg[03], lfsr_seed_reg[04], lfsr_seed_reg[05],
                           lfsr_seed_reg[06], lfsr_seed_reg[07], lfsr_seed_reg[08], lfsr_seed_reg[09], lfsr_seed_reg[10], lfsr_seed_reg[11]};
  
  //rising edge detect on core tag valid
  assign core_tag_we = (core_tag_valid & ~tag_valid_reg) & ~error_flag_reg;

  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  hmac_core core(
                 .clk(clk),
                 .reset_n(reset_n),
                 .zeroize(zeroize_reg),

                 .init_cmd(init_reg),
                 .next_cmd(next_reg),
                 .mode_cmd(mode_reg),

                 .lfsr_seed(core_lfsr_seed),

                 .key(core_key),

                 .block_msg(core_block),

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
      integer ii;

      if (!reset_n)
        begin
          kv_reg          <= '0;
          tag_reg         <= '0;
          tag_valid_reg   <= '0;
          ready_reg       <= '0;
          block_reg_lock  <= '0;
          kv_key_data_present <= '0;
          kv_block_data_present <= '0;
        end
      else if (zeroize_reg)
        begin
          kv_reg          <= '0;
          tag_reg         <= '0;
          tag_valid_reg   <= '0;
          ready_reg       <= '0;
          block_reg_lock  <= '0;
          kv_key_data_present <= '0;
          kv_block_data_present <= '0;
        end
      else
        begin
          tag_valid_reg <= core_tag_valid & ~error_flag_reg;
          ready_reg     <= core_ready; 

          //write to sw register
          if (core_tag_we & ~(dest_keyvault | kv_data_present))
            tag_reg <= core_tag & get_mask;
          if (core_tag_we & (dest_keyvault | kv_data_present))
            kv_reg <= core_tag & get_mask;

          block_reg_lock <= block_reg_lock_nxt;
          kv_key_data_present <= kv_key_data_present_set ? '1 :
                                 kv_data_present_reset ? '0 : kv_key_data_present;
          kv_block_data_present <= kv_block_data_present_set ? '1 :
                                   kv_data_present_reset ? '0 : kv_block_data_present;
        end
    end // reg_update

//HMAC register hardware interfaces
always_comb begin
  //drive resets to register block
  hwif_in.error_reset_b = cptra_pwrgood;
  hwif_in.reset_b = reset_n;
  //drive hardware writeable registers from hmac core
  hwif_in.HMAC512_NAME[0].NAME.next = HMAC_CORE_NAME[31:0];
  hwif_in.HMAC512_NAME[1].NAME.next = HMAC_CORE_NAME[63:32];
  hwif_in.HMAC512_VERSION[0].VERSION.next = HMAC_CORE_VERSION[31:0];
  hwif_in.HMAC512_VERSION[1].VERSION.next = HMAC_CORE_VERSION[63:32];
  //Only allow setting CSR MODE when ready is set
  hwif_in.HMAC512_CTRL.CSR_MODE.swwe = ready_reg;
  hwif_in.HMAC512_CTRL.INIT.swwe = ready_reg;
  hwif_in.HMAC512_CTRL.NEXT.swwe = ready_reg;
  hwif_in.HMAC512_CTRL.MODE.swwe = ready_reg;

  //assign hardware readable registers to drive hmac core
  //mask the command until kv clients are idle
  init_reg = hwif_out.HMAC512_CTRL.INIT.value & kv_key_ready & kv_block_ready;
  next_reg = hwif_out.HMAC512_CTRL.NEXT.value & kv_key_ready & kv_block_ready;
  zeroize_reg = hwif_out.HMAC512_CTRL.ZEROIZE.value || debugUnlock_or_scan_mode_switch;
  mode_reg = hwif_out.HMAC512_CTRL.MODE.value;

  //drive hardware writeable registers from hmac core
  hwif_in.HMAC512_STATUS.READY.next = ready_reg;
  hwif_in.HMAC512_STATUS.VALID.next = tag_valid_reg;
  for (int dword=0; dword < TAG_NUM_DWORDS; dword++) begin
    hwif_in.HMAC512_TAG[dword].TAG.next = tag_reg[(TAG_NUM_DWORDS - 1)-dword];
    hwif_in.HMAC512_TAG[dword].TAG.hwclr = zeroize_reg;
  end
  //drive hardware writable registers from key vault
  for (int dword=0; dword < BLOCK_NUM_DWORDS; dword++)begin
    hwif_in.HMAC512_BLOCK[dword].BLOCK.we = (kv_block_write_en & (kv_block_write_offset == dword)) & !(zeroize_reg | kv_data_present_reset);
    hwif_in.HMAC512_BLOCK[dword].BLOCK.next = kv_block_write_data;
    hwif_in.HMAC512_BLOCK[dword].BLOCK.hwclr = zeroize_reg | kv_data_present_reset | (kv_block_error == KV_READ_FAIL);
    hwif_in.HMAC512_BLOCK[dword].BLOCK.swwel = block_reg_lock[dword];
  end
  for (int dword=0; dword < KEY_NUM_DWORDS; dword++)begin
    hwif_in.HMAC512_KEY[dword].KEY.we = (kv_key_write_en & (kv_key_write_offset == dword)) & !(zeroize_reg | kv_data_present_reset);
    hwif_in.HMAC512_KEY[dword].KEY.next = kv_key_write_data;
    hwif_in.HMAC512_KEY[dword].KEY.hwclr = zeroize_reg | kv_data_present_reset | (kv_key_error == KV_READ_FAIL);
    hwif_in.HMAC512_KEY[dword].KEY.swwel = kv_key_data_present;
  end
  //set ready when keyvault isn't busy
  hwif_in.HMAC512_KV_RD_KEY_STATUS.READY.next = kv_key_ready;
  hwif_in.HMAC512_KV_RD_BLOCK_STATUS.READY.next = kv_block_ready;
  hwif_in.HMAC512_KV_WR_STATUS.READY.next = kv_write_ready;
  //set error code
  hwif_in.HMAC512_KV_RD_KEY_STATUS.ERROR.next = kv_key_error;
  hwif_in.HMAC512_KV_RD_BLOCK_STATUS.ERROR.next = kv_block_error;
  hwif_in.HMAC512_KV_WR_STATUS.ERROR.next = kv_write_error;
  //set valid when fsm is done
  hwif_in.HMAC512_KV_RD_KEY_STATUS.VALID.hwset = kv_key_done;
  hwif_in.HMAC512_KV_RD_BLOCK_STATUS.VALID.hwset = kv_block_done;
  hwif_in.HMAC512_KV_WR_STATUS.VALID.hwset = kv_write_done;
  //clear valid when new request is made
  hwif_in.HMAC512_KV_RD_KEY_STATUS.VALID.hwclr = kv_key_read_ctrl_reg.read_en;
  hwif_in.HMAC512_KV_RD_BLOCK_STATUS.VALID.hwclr = kv_block_read_ctrl_reg.read_en;
  hwif_in.HMAC512_KV_WR_STATUS.VALID.hwclr = kv_write_ctrl_reg.write_en;
  //clear enable when busy
  hwif_in.HMAC512_KV_RD_KEY_CTRL.read_en.hwclr = ~kv_key_ready;
  hwif_in.HMAC512_KV_RD_BLOCK_CTRL.read_en.hwclr = ~kv_block_ready;
  hwif_in.HMAC512_KV_WR_CTRL.write_en.hwclr = ~kv_write_ready;
  //assign hardware readable registers to drive hmac core
  for (int dword=0; dword < KEY_NUM_DWORDS; dword++) begin
    key_reg[dword] = hwif_out.HMAC512_CTRL.CSR_MODE.value ? cptra_csr_hmac_key[dword] : hwif_out.HMAC512_KEY[dword].KEY.value;
  end
  for (int dword=0; dword < BLOCK_NUM_DWORDS; dword++)begin
    block_reg[dword] = hwif_out.HMAC512_BLOCK[dword].BLOCK.value;
  end

  for (int dword=0; dword < SEED_NUM_DWORDS; dword++)begin
    lfsr_seed_reg[dword] = hwif_out.HMAC512_LFSR_SEED[dword].LFSR_SEED.value;
  end
end

always_comb begin
  unique case (mode_reg)
    1'b0 :     get_mask = {{12{32'hffffffff}}, {4{32'h00000000}}};  //HMAC384
    default :  get_mask = {16{32'hffffffff}};                       //HMAC512
  endcase
end

//set the lock for the part of the block being written by KV logic
//release the lock once init has been seen
always_comb begin
  for (int dword=0; dword< BLOCK_NUM_DWORDS; dword++) begin
    if (init_reg | next_reg) begin
      block_reg_lock_nxt[dword] = '0;
    end
    else begin
      block_reg_lock_nxt[dword] = (kv_block_write_en & (kv_block_write_offset == dword)) ? '1 : block_reg_lock[dword];
    end
  end
end

// Software write-enables to prevent KV reg manipulation mid-operation
always_comb hwif_in.HMAC512_KV_RD_KEY_CTRL.read_en.swwe         = !kv_key_data_present && core_ready;
always_comb hwif_in.HMAC512_KV_RD_KEY_CTRL.read_entry.swwe      = !kv_key_data_present && core_ready;
always_comb hwif_in.HMAC512_KV_RD_KEY_CTRL.pcr_hash_extend.swwe = !kv_key_data_present && core_ready;
always_comb hwif_in.HMAC512_KV_RD_KEY_CTRL.rsvd.swwe            = !kv_key_data_present && core_ready;

always_comb hwif_in.HMAC512_KV_RD_BLOCK_CTRL.read_en.swwe         = !kv_block_data_present && core_ready;
always_comb hwif_in.HMAC512_KV_RD_BLOCK_CTRL.read_entry.swwe      = !kv_block_data_present && core_ready;
always_comb hwif_in.HMAC512_KV_RD_BLOCK_CTRL.pcr_hash_extend.swwe = !kv_block_data_present && core_ready;
always_comb hwif_in.HMAC512_KV_RD_BLOCK_CTRL.rsvd.swwe            = !kv_block_data_present && core_ready;

// KV write control must be written before HMAC core operation begins, even though
// output isn't written to KV until the end of the operation.
// Prevent partial-key attacks by blocking register modifications during core execution.
always_comb hwif_in.HMAC512_KV_WR_CTRL.write_en.swwe              = core_ready;
always_comb hwif_in.HMAC512_KV_WR_CTRL.write_entry.swwe           = core_ready;
always_comb hwif_in.HMAC512_KV_WR_CTRL.hmac_key_dest_valid.swwe   = core_ready;
always_comb hwif_in.HMAC512_KV_WR_CTRL.hmac_block_dest_valid.swwe = core_ready;
always_comb hwif_in.HMAC512_KV_WR_CTRL.mldsa_seed_dest_valid.swwe = core_ready;
always_comb hwif_in.HMAC512_KV_WR_CTRL.ecc_pkey_dest_valid.swwe   = core_ready;
always_comb hwif_in.HMAC512_KV_WR_CTRL.ecc_seed_dest_valid.swwe   = core_ready;
always_comb hwif_in.HMAC512_KV_WR_CTRL.aes_key_dest_valid.swwe    = core_ready;
always_comb hwif_in.HMAC512_KV_WR_CTRL.mlkem_seed_dest_valid.swwe = core_ready;
always_comb hwif_in.HMAC512_KV_WR_CTRL.mlkem_msg_dest_valid.swwe  = core_ready;
always_comb hwif_in.HMAC512_KV_WR_CTRL.dma_data_dest_valid.swwe   = core_ready;
always_comb hwif_in.HMAC512_KV_WR_CTRL.rsvd.swwe                  = core_ready;

//keyvault control reg macros for assigning to struct
`CALIPTRA_KV_READ_CTRL_REG2STRUCT(kv_key_read_ctrl_reg, HMAC512_KV_RD_KEY_CTRL)
`CALIPTRA_KV_READ_CTRL_REG2STRUCT(kv_block_read_ctrl_reg, HMAC512_KV_RD_BLOCK_CTRL)
`CALIPTRA_KV_WRITE_CTRL_REG2STRUCT(kv_write_ctrl_reg, HMAC512_KV_WR_CTRL)

//Force result into KV reg whenever source came from KV
always_comb kv_key_data_present_set = kv_key_read_ctrl_reg.read_en;
always_comb kv_block_data_present_set = kv_block_read_ctrl_reg.read_en;
always_comb kv_data_present = kv_key_data_present | kv_block_data_present;
always_comb kv_data_present_reset = kv_data_present & core_tag_we;

// Register block
hmac_reg i_hmac_reg (
    .clk(clk),
    .rst(1'b0),

    .s_cpuif_req         (cs),
    .s_cpuif_req_is_wr   (we),
    .s_cpuif_addr        (address[HMAC_REG_ADDR_WIDTH-1:0]),
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

always_comb key_mode_error = kv_key_data_present & (init_reg | next_reg) & (mode_reg == HMAC512_MODE) & (key_reg[15:12] == 128'b0);
always_comb key_zero_error = kv_key_data_present & (init_reg | next_reg) & (key_reg == 512'b0);

always_comb error_flag = key_zero_error | key_mode_error;

always_ff @(posedge clk or negedge reset_n) 
begin : error_detection
    if(!reset_n) begin
      error_flag_reg <= 1'b0;
      key_mode_error_reg <= 1'b0;
      key_zero_error_reg <= 1'b0;
    end
    else if(zeroize_reg) begin
      error_flag_reg <= 1'b0;
      key_mode_error_reg <= 1'b0;
      key_zero_error_reg <= 1'b0;
    end
    else begin
      if (error_flag)
        error_flag_reg <= 1'b1;
      key_mode_error_reg <= key_mode_error;
      key_zero_error_reg <= key_zero_error;
    end
end // error_detection

always_comb error_flag_edge = error_flag & (!error_flag_reg);
always_comb key_mode_error_edge = key_mode_error & (!key_mode_error_reg);
always_comb key_zero_error_edge = key_zero_error & (!key_zero_error_reg);

//Interrupts hardware interface
assign hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = core_tag_we;
assign hwif_in.intr_block_rf.error_internal_intr_r.key_mode_error_sts.hwset = key_mode_error_edge;
assign hwif_in.intr_block_rf.error_internal_intr_r.key_zero_error_sts.hwset = key_zero_error_edge;
assign hwif_in.intr_block_rf.error_internal_intr_r.error2_sts.hwset = 1'b0; // TODO
assign hwif_in.intr_block_rf.error_internal_intr_r.error3_sts.hwset = 1'b0; // TODO

assign error_intr = hwif_out.intr_block_rf.error_global_intr_r.intr;
assign notif_intr = hwif_out.intr_block_rf.notif_global_intr_r.intr;

//Key Vault Control Modules
always_comb begin
    kv_key_read_metrics.ocp_lock_in_progress = ocp_lock_in_progress;
    kv_key_read_metrics.kv_read_dest         = KV_NUM_READ'(1<<KV_DEST_IDX_HMAC_KEY);
    kv_key_read_metrics.kv_key_entry         = kv_key_read_ctrl_reg.read_entry;
end

//Read Key
kv_read_client #(
  .DATA_WIDTH(KEY_SIZE),
  .PAD(0)
)
hmac_key_kv_read
(
    .clk(clk),
    .rst_b(reset_n),
    .zeroize(zeroize_reg),

    //client control register
    .read_ctrl_reg(kv_key_read_ctrl_reg),
    .read_metrics (kv_key_read_metrics ),

    //interface with kv
    .kv_read(kv_read[0]),
    .kv_resp(kv_rd_resp[0]),

    //interface with client
    .write_en(kv_key_write_en),
    .write_offset(kv_key_write_offset),
    .write_data(kv_key_write_data),

    .error_code(kv_key_error),
    .kv_ready(kv_key_ready),
    .read_done(kv_key_done)
);

//Key Vault Control Modules
always_comb begin
    kv_block_read_metrics.ocp_lock_in_progress = ocp_lock_in_progress;
    kv_block_read_metrics.kv_read_dest         = KV_NUM_READ'(1<<KV_DEST_IDX_HMAC_BLOCK);
    kv_block_read_metrics.kv_key_entry         = kv_block_read_ctrl_reg.read_entry;
end

//Read Block
kv_read_client #(
  .DATA_WIDTH(BLOCK_SIZE),
  .HMAC(1),
  .PAD(1)
)
hmac_block_kv_read
(
    .clk(clk),
    .rst_b(reset_n),
    .zeroize(zeroize_reg),

    //client control register
    .read_ctrl_reg(kv_block_read_ctrl_reg),
    .read_metrics(kv_block_read_metrics),

    //interface with kv
    .kv_read(kv_read[1]),
    .kv_resp(kv_rd_resp[1]),

    //interface with client
    .write_en(kv_block_write_en),
    .write_offset(kv_block_write_offset),
    .write_data(kv_block_write_data),

    .error_code(kv_block_error),
    .kv_ready(kv_block_ready),
    .read_done(kv_block_done)
);

//write 512 or 384 result based on mode bit
logic [$clog2(TAG_SIZE/32):0] num_dwords;
always_comb num_dwords = mode_reg ? 'd16 : 'd12;

//Write to keyvault
always_comb begin
    kv_write_metrics.ocp_lock_in_progress = ocp_lock_in_progress;
    kv_write_metrics.kv_data0_present     = kv_key_data_present;
    kv_write_metrics.kv_data0_entry       = kv_key_read_ctrl_reg.read_entry; // Stable after start-time due to SWWE
    kv_write_metrics.kv_data1_present     = kv_block_data_present;
    kv_write_metrics.kv_data1_entry       = kv_block_read_ctrl_reg.read_entry; // Stable after start-time due to SWWE
    kv_write_metrics.kv_write_src         = KV_NUM_WRITE'(1 << KV_WRITE_IDX_HMAC);
    kv_write_metrics.kv_write_entry       = kv_write_ctrl_reg.write_entry;
    kv_write_metrics.aes_decrypt_ecb_op   = 1'b0;
end

kv_write_client #(
  .DATA_WIDTH(TAG_SIZE)
)
hmac_result_kv_write
(
  .clk(clk),
  .rst_b(reset_n),
  .zeroize(zeroize_reg),

  //client control register
  .write_ctrl_reg(kv_write_ctrl_reg),
  .write_metrics(kv_write_metrics),
  .num_dwords(num_dwords), 

  //interface with kv
  .kv_write(kv_write),
  .kv_resp(kv_wr_resp),

  //interface with client
  .dest_keyvault(dest_keyvault),
  .dest_data_avail(core_tag_we),
  .dest_data(kv_reg),

  .error_code(kv_write_error),
  .kv_ready(kv_write_ready),
  .dest_done(kv_write_done)
);

always_comb busy_o = ~kv_write_ready | ~kv_block_ready | ~kv_key_ready | ~core_ready;

`CALIPTRA_ASSERT_STABLE(ERR_HMAC_KEY_RD_CTRL_NOT_STABLE, kv_key_read_ctrl_reg, clk, (!reset_n || core_ready) )
`CALIPTRA_ASSERT_STABLE(ERR_HMAC_BLOCK_RD_CTRL_NOT_STABLE, kv_block_read_ctrl_reg, clk, (!reset_n || core_ready) )
`CALIPTRA_ASSERT_STABLE(ERR_HMAC_WR_CTRL_NOT_STABLE, kv_write_ctrl_reg, clk, (!reset_n || core_ready) )
`CALIPTRA_ASSERT_STABLE(ERR_HMAC_KEY_NOT_STABLE, key_reg, clk, (!reset_n || core_ready) )
`CALIPTRA_ASSERT_STABLE(ERR_HMAC_BLOCK_NOT_STABLE, block_reg, clk, (!reset_n || core_ready) )

endmodule // hmac

//======================================================================
// EOF hmac.sv
//======================================================================
