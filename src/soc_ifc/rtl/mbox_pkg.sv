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

package mbox_pkg;

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

  typedef struct packed {
    logic axs_without_lock;
    logic axs_incorrect_order;
  } mbox_protocol_error_t;

  typedef struct packed {
    logic [31:0] MBOX_LOCK;
    logic [31:0] MBOX_CMD;
    logic [31:0] MBOX_DLEN;
    logic [31:0] MBOX_DOUT;
    logic [31:0] MBOX_STATUS;
  } mbox_dmi_reg_t;

endpackage