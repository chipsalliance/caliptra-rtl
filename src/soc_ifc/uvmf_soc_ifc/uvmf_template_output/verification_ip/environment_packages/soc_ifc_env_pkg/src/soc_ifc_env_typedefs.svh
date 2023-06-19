//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
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

// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// DESCRIPTION: 
// This file contains defines and typedefs to be compiled for use in
// the environment package.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//


  // pragma uvmf custom additional begin
  typedef enum logic [4:0] {
    CPTRA_SUCCESS = 5'b00000,
    CPTRA_TIMEOUT = 5'b00001,
    CPTRA_INVALID = 5'b00010,
    CPTRA_X_VAL   = 5'b00100,
    CPTRA_FAIL    = 5'b11111
  } op_sts_e;

  /**
   * Decode:
   *   [31]: Firmware command
   *   [30]: Response required (if set)
   *   [29]: uC->SoC command
   */
  typedef enum logic [31:0] {
      MBOX_CMD_UC_BASIC   = 32'h20000000,
      MBOX_CMD_UC_OVERRUN = 32'h20000001,
      MBOX_CMD_RESP_BASIC = 32'h40000000,
      MBOX_CMD_REG_ACCESS = 32'h40000001,
      MBOX_CMD_OOB_ACCESS = 32'h40000002,
      MBOX_CMD_FMC_UPDATE = 32'hba5eba11,
      MBOX_CMD_RT_UPDATE  = 32'hbabecafe,
      MBOX_CMD_SHA384_REQ = 32'h40C0FFEE,
      MBOX_CMD_SHA512_REQ = 32'h41C0FFEE,
      MBOX_CMD_ROM_FW_UPD = 32'h46574C44
  } mbox_cmd_e;
  
  typedef union packed {
      mbox_cmd_e cmd_e;
      struct packed {
          logic fw;
          logic resp_reqd;
          logic uc_to_soc;
          logic [28:0] rsvd;
      } cmd_s;
  } mbox_cmd_u;

  typedef struct packed {
    logic [31:0] dlen;
    mbox_cmd_u   cmd;
  } mbox_op_s;

  typedef struct packed {
    logic mailbox_mode;
    logic sha512_mode;
  } sha_accel_op_s;

  typedef struct packed {
      bit null_action; /* no-effect reads or writes to mbox regs, or resets when mbox is idle */
      bit lock_acquire;
      bit cmd_wr;
      bit dlen_wr;
      bit datain_wr;
      bit exec_set;
      bit cmd_rd;
      bit dlen_rd;
      bit dataout_rd;
      bit resp_datain_wr;
      bit resp_dlen_wr;
      bit resp_dlen_rd;
      bit resp_dataout_rd;
      bit status_wr;
      bit status_rd;
      bit exec_clr;
      bit force_unlock;
      bit reset; /* should be triggered by a soc_ifc_ctrl transaction to indicate that an _active_ mailbox flow was interrupted by reset */
  } mbox_steps_s;
  localparam mbox_steps_s MBOX_STEP_NULL_ACTION     = '{null_action    : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_LOCK_ACQUIRE    = '{lock_acquire   : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_CMD_WR          = '{cmd_wr         : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_DLEN_WR         = '{dlen_wr        : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_DATAIN_WR       = '{datain_wr      : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_EXEC_SET        = '{exec_set       : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_CMD_RD          = '{cmd_rd         : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_DLEN_RD         = '{dlen_rd        : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_DATAOUT_RD      = '{dataout_rd     : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_RESP_DATAIN_WR  = '{resp_datain_wr : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_RESP_DLEN_WR    = '{resp_dlen_wr   : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_RESP_DLEN_RD    = '{resp_dlen_rd   : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_RESP_DATAOUT_RD = '{resp_dataout_rd: 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_STATUS_WR       = '{status_wr      : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_STATUS_RD       = '{status_rd      : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_EXEC_CLR        = '{exec_clr       : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_FORCE_UNLOCK    = '{force_unlock   : 1'b1, default: 1'b0};
  localparam mbox_steps_s MBOX_STEP_RESET           = '{reset          : 1'b1, default: 1'b0};

  localparam bit     AHB_REQ = 1'b1;
  localparam bit NOT_AHB_REQ = 1'b0;
  typedef struct packed {
    bit          is_ahb;
    mbox_steps_s step;
  } mbox_steps_by_if_s;
  // pragma uvmf custom additional end

