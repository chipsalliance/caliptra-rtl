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
   */
  typedef enum logic [31:0] {
      MBOX_CMD_RESP_BASIC = 32'h40000000,
      MBOX_CMD_REG_ACCESS = 32'h40000001,
      MBOX_CMD_OOB_ACCESS = 32'h40000002,
      MBOX_CMD_FMC_UPDATE = 32'hba5eba11,
      MBOX_CMD_RT_UPDATE  = 32'hbabecafe,
      MBOX_CMD_SHA384_REQ = 32'h40C0FFEE,
      MBOX_CMD_SHA512_REQ = 32'h41C0FFEE
  } mbox_cmd_e;
  
  typedef union packed {
      mbox_cmd_e cmd_e;
      struct packed {
          logic fw;
          logic resp_reqd;
          logic [29:0] rsvd;
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

  // pragma uvmf custom additional end

