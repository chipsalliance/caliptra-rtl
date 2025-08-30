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
//==============================================================================
//
// doe_cbc.v
// --------
// The module supports DOE_CBC and it is the modified version of doe.v file. 
// In the hierarcy, one level up module is the doe_ctrl_32.sv or doe_ctrl_64.sv  
// This module receives the data from AHB just before decoding it into block, 
// key, and IV.
//
// The "IV XOR Plaintext" operation is just added into the DOE first Key XOR path.
// The combinational logical path is ((IV XOR Plaintext) XOR Key). The lower
// hierarcy, doe core, has not been changed. Instead, doe_core_cbc was created.
// The created design differs from the original one only with an XOR operation. 
//
// DOE CBC mode is tested with doe_cbc_tb.sv
// 
// 
//==============================================================================

module doe_cbc 
  import doe_defines_pkg::*;
  import kv_defines_pkg::*;
  import doe_reg_pkg::*;
 #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
  )
  (
   // Clock and reset.
   input wire           clk,
   input wire           reset_n,
   input wire           cptra_pwrgood,

   input wire [`CLP_OBF_KEY_DWORDS-1:0][31:0] cptra_obf_key,

   //Obfuscated UDS and FE
   input wire [`CLP_OBF_FE_DWORDS-1 :0][31:0] obf_field_entropy,
   input wire [`CLP_OBF_UDS_DWORDS-1:0][31:0] obf_uds_seed,
   input wire [OCP_LOCK_HEK_NUM_DWORDS-1:0][31:0] obf_hek_seed,

   // Control.
   input wire           cs,
   input wire           we,

   // Data ports.
   input wire  [ADDR_WIDTH-1 : 0] address,
   input wire  [DATA_WIDTH-1 : 0] write_data,
   output wire [DATA_WIDTH-1 : 0] read_data,

   // Interrupt Outputs
   output logic error_intr,
   output logic notif_intr,

   output logic clear_obf_secrets,

  output logic busy_o,

   //interface with kv
   output kv_write_t kv_write,
   input  logic ocp_lock_en, // Synth-time constant strap input instead of ocp_lock_in_progress
   input  logic debugUnlock_or_scan_mode_switch
  );

  //----------------------------------------------------------------
  // Registers including update variables and write enable.
  //----------------------------------------------------------------
  localparam BLOCK_NO = 128 / DATA_WIDTH;
  localparam IV_NO = 128 / DATA_WIDTH;

  logic [BLOCK_NO-1:0][DATA_WIDTH-1:0] block_reg;
  logic [IV_NO-1:0][DATA_WIDTH-1:0] IV_reg;
  reg [127 : 0] kv_result_reg;
  reg           ready_reg;

  //----------------------------------------------------------------
  // Wires.
  //----------------------------------------------------------------
  wire           core_encdec;
  wire           core_init;
  wire           core_next;
  wire           core_ready;
  wire [255 : 0] core_key;
  wire           core_keylen;
  wire [127 : 0] core_block;
  wire [127 : 0] core_IV;
  wire [127 : 0] core_result;
  wire           core_valid;

  //client control register
  doe_cmd_reg_t doe_cmd_reg;

  logic IV_updated;

  //interface with client
  logic doe_block_write_en;
  logic [127:0] doe_block_write_data;

  logic doe_init;
  logic doe_next;
  logic zeroize;

  logic flow_done;
  logic flow_error;
  logic flow_in_progress, lock_fe_flow, lock_uds_flow, lock_hek_flow;

  doe_reg__in_t  hwif_in;
  doe_reg__out_t hwif_out;


  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign core_key     = {cptra_obf_key[0], cptra_obf_key[1], cptra_obf_key[2], cptra_obf_key[3], cptra_obf_key[4], cptra_obf_key[5], cptra_obf_key[6], cptra_obf_key[7]};
  assign core_block   = {block_reg[0], block_reg[1], block_reg[2], block_reg[3]};
  assign core_IV      = {IV_reg[0], IV_reg[1], IV_reg[2], IV_reg[3]};

  assign core_init   = doe_init;
  assign core_next   = doe_next;
  assign core_encdec = '0; //force decypher for DOE
  assign core_keylen = '1; //force 256b KEY for DOE


  //----------------------------------------------------------------
  // core instantiation.
  //----------------------------------------------------------------
  doe_core_cbc i_doe_core_cbc(
                .clk(clk),
                .reset_n(reset_n),
                .zeroize(zeroize),

                .encdec(core_encdec),
                .init_cmd(core_init),
                .next_cmd(core_next),
                .ready(core_ready),

                .key(core_key),
                .keylen(core_keylen),

                .IV(core_IV),
                .IV_updated(IV_updated),

                .block_msg(core_block),
                .result(core_result),
                .result_valid(core_valid)
               );


  //----------------------------------------------------------------
  // reg_update
  // Update functionality for all registers in the core.
  // All registers are positive edge triggered with asynchronous
  // active low reset.
  //----------------------------------------------------------------
  always @ (posedge clk or negedge reset_n) begin : reg_update
      if (!reset_n) begin
          block_reg <= '0;
          ready_reg <= '0;
          kv_result_reg <= '0;
      end
      else if (zeroize) begin
          block_reg <= '0;
          ready_reg <= '0;
          kv_result_reg <= '0;
      end
      else begin
          ready_reg  <= core_ready;
          kv_result_reg <= core_result;
          block_reg <= doe_block_write_en ? doe_block_write_data : block_reg;
        end
  end// reg_update

//DOE Register Hardware Interface


// Lock the UDS_FLOW_DONE & FE_FLOW_DONE status once the flow is done. Bit is reset only on cold reset on '1. FIXME: add an assertion
assign hwif_in.DOE_STATUS.UDS_FLOW_DONE.next = lock_uds_flow;
assign hwif_in.DOE_STATUS.FE_FLOW_DONE.next  = lock_fe_flow;
assign hwif_in.DOE_STATUS.HEK_FLOW_DONE.next = lock_hek_flow;

assign hwif_in.DOE_STATUS.DEOBF_SECRETS_CLEARED.hwset = clear_obf_secrets;

assign hwif_in.DOE_STATUS.READY.hwset = ready_reg & ~(flow_in_progress);
assign hwif_in.DOE_STATUS.READY.hwclr = ~ready_reg;
assign hwif_in.DOE_STATUS.VALID.hwset = flow_done | clear_obf_secrets;
assign hwif_in.DOE_STATUS.VALID.hwclr = hwif_out.DOE_CTRL.CMD.swmod || hwif_out.DOE_CTRL.CMD_EXT.swmod;
assign hwif_in.DOE_STATUS.ERROR.hwset = flow_error;
assign hwif_in.DOE_STATUS.ERROR.hwclr = clear_obf_secrets || hwif_out.DOE_CTRL.CMD.swmod || hwif_out.DOE_CTRL.CMD_EXT.swmod;

assign hwif_in.DOE_CTRL.CMD.hwclr     = flow_done | clear_obf_secrets;
assign hwif_in.DOE_CTRL.CMD_EXT.hwclr = flow_done | clear_obf_secrets;

assign doe_cmd_reg.cmd = doe_cmd_e'({hwif_out.DOE_CTRL.CMD_EXT.value,hwif_out.DOE_CTRL.CMD.value});
// OCP LOCK flow for HEK deobf requires output be stored in a predetermined slot.
// ROM is responsible for configuring this properly.
assign doe_cmd_reg.dest_sel = hwif_out.DOE_CTRL.DEST.value;

//FW can do this to clear the obfuscation related secrets
//the Obfuscated UDS, FE, and OBF KEY
always_comb clear_obf_secrets = (doe_cmd_reg.cmd == DOE_CLEAR) || debugUnlock_or_scan_mode_switch;
always_comb zeroize = clear_obf_secrets;

always_comb begin
  IV_updated = '0;
  for (int dword = 0; dword < IV_NO; dword++) begin
    IV_reg[dword] = hwif_out.DOE_IV[dword].IV.value;
    IV_updated |= hwif_out.DOE_IV[dword].IV.swmod;
  end
end

//TODO: flow_done also?
always_comb begin
  for (int dword = 0; dword < IV_NO; dword++) begin
    hwif_in.DOE_IV[dword].IV.hwclr = zeroize;
  end
end

doe_fsm
doe_fsm1 
(
  .clk(clk),
  .rst_b(reset_n),
  .hard_rst_b(cptra_pwrgood),
  //Obfuscated UDS and FE
  .obf_field_entropy(obf_field_entropy),
  .obf_uds_seed(obf_uds_seed),
  .obf_hek_seed(obf_hek_seed),

  //client control register
  .doe_cmd_reg(doe_cmd_reg),
  .ocp_lock_en(ocp_lock_en),

  //interface with kv
  .kv_write(kv_write),

  //interface with client
  .src_write_en(doe_block_write_en),
  .src_write_data(doe_block_write_data),

  .doe_init(doe_init),
  .doe_next(doe_next),

  .init_done(core_ready),
  .dest_data_avail(core_valid),
  .dest_data(kv_result_reg),

  .flow_done(flow_done),
  .flow_error(flow_error),
  .flow_in_progress(flow_in_progress),
  .lock_uds_flow(lock_uds_flow),
  .lock_fe_flow (lock_fe_flow ),
  .lock_hek_flow(lock_hek_flow),
  .zeroize(zeroize)

);

always_comb hwif_in.reset_b = reset_n;
always_comb hwif_in.cptra_pwrgood = cptra_pwrgood;

// Pulse input to intr_regs to set the interrupt status bit and generate interrupt output (if enabled)
always_comb hwif_in.intr_block_rf.error_internal_intr_r.error0_sts.hwset  = 1'b0; // TODO please assign
always_comb hwif_in.intr_block_rf.error_internal_intr_r.error1_sts.hwset  = 1'b0; // TODO please assign
always_comb hwif_in.intr_block_rf.error_internal_intr_r.error2_sts.hwset  = 1'b0; // TODO please assign
always_comb hwif_in.intr_block_rf.error_internal_intr_r.error3_sts.hwset  = 1'b0; // TODO please assign
always_comb hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = flow_done;

doe_reg i_doe_reg (
        .clk(clk),
        .rst(reset_n),

        .s_cpuif_req         (cs),
        .s_cpuif_req_is_wr   (we),
        .s_cpuif_addr        (address[DOE_REG_ADDR_WIDTH-1:0]),
        .s_cpuif_wr_data     (write_data[31:0]),
        .s_cpuif_wr_biten    ('1),

        .s_cpuif_req_stall_wr(),
        .s_cpuif_req_stall_rd(),
        .s_cpuif_rd_ack      (),
        .s_cpuif_rd_err      (/*TODO*/),
        .s_cpuif_rd_data     (read_data     ),
        .s_cpuif_wr_ack      (),
        .s_cpuif_wr_err      (/*TODO*/),

        .hwif_in             (hwif_in ),
        .hwif_out            (hwif_out)
    );

assign error_intr = hwif_out.intr_block_rf.error_global_intr_r.intr;
assign notif_intr = hwif_out.intr_block_rf.notif_global_intr_r.intr;

always_comb busy_o = flow_in_progress | ~core_ready;

endmodule // doe

//======================================================================
// EOF doe.v
//======================================================================
