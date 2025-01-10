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

`include "config_defines.svh"

package mbox_pkg;

  //Match the mailbox client interface
  parameter MBOX_IFC_DATA_W = 32;
  parameter MBOX_IFC_USER_W = 32;
  parameter MBOX_IFC_ADDR_W = 19;
  parameter MBOX_IFC_ID_W   = `CALIPTRA_AXI_ID_WIDTH;

  //Mailbox size configuration
  parameter MBOX_SIZE_KB = 256;
  parameter MBOX_SIZE_BYTES = MBOX_SIZE_KB * 1024;
  parameter MBOX_SIZE_DWORDS = MBOX_SIZE_BYTES/4;
  parameter MBOX_DATA_W = 32;
  parameter MBOX_ECC_DATA_W = 7;
  parameter MBOX_DATA_AND_ECC_W = MBOX_DATA_W + MBOX_ECC_DATA_W;
  parameter MBOX_DEPTH = (MBOX_SIZE_KB * 1024 * 8) / MBOX_DATA_W;
  parameter MBOX_ADDR_W = $clog2(MBOX_DEPTH);
  parameter MBOX_DEPTH_LOG2 = $clog2(MBOX_DEPTH);

  //MAILBOX FSM
  typedef enum logic [2:0] {
    MBOX_IDLE         = 3'b000,
    MBOX_RDY_FOR_CMD  = 3'b001,
    MBOX_RDY_FOR_DLEN = 3'b011,
    MBOX_RDY_FOR_DATA = 3'b010,
    MBOX_EXECUTE_UC   = 3'b110,
    MBOX_EXECUTE_SOC  = 3'b100,
    MBOX_EXECUTE_TAP  = 3'b101,
    MBOX_ERROR        = 3'b111
  } mbox_fsm_state_e;

  //MAILBOX Status
  typedef enum logic [3:0] {
    CMD_BUSY      = 4'd0,
    DATA_READY    = 4'd1,
    CMD_COMPLETE  = 4'd2,
    CMD_FAILURE   = 4'd3
  } mbox_status_e;

  //Any request into mbox
  typedef struct packed {
    logic   [MBOX_IFC_ADDR_W-1:0]   addr;
    logic   [MBOX_IFC_DATA_W-1:0]   wdata;
    logic   [MBOX_IFC_DATA_W/8-1:0] wstrb;
    logic   [MBOX_IFC_USER_W-1:0]   user;
    logic   [MBOX_IFC_ID_W  -1:0]   id;
    logic                          write;
    logic                          soc_req;
  } mbox_req_t;

  // ECC protected data
  typedef struct packed {
    logic [MBOX_ECC_DATA_W-1:0] ecc;
    logic [MBOX_DATA_W-1:0]     data;
  } mbox_sram_data_t;

  //Request to mbox sram
  typedef struct packed {
    logic cs;
    logic we;
    logic [MBOX_ADDR_W-1:0] addr;
    mbox_sram_data_t wdata;
  } mbox_sram_req_t;

  //Response from mbox sram
  typedef struct packed {
    mbox_sram_data_t rdata;
  } mbox_sram_resp_t;


  typedef struct packed {
    logic axs_without_lock;
    logic axs_incorrect_order;
  } mbox_protocol_error_t;

  typedef struct packed {
    logic [31:0] MBOX_DLEN;
    logic [31:0] MBOX_DOUT;
    logic [31:0] MBOX_STATUS;
  } mbox_dmi_reg_t;

endpackage