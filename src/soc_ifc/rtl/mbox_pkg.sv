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
  // Encoding generated with
  // $ python3 sparse_fsm_encode.py -d 5 -m 8 -n 10 -s 23571113
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  //
  localparam int MboxStateWidth = 10;
  typedef enum logic [MboxStateWidth-1:0] {
    MBOX_IDLE_SPARSE         = 10'b0111010111,
    MBOX_RDY_FOR_CMD_SPARSE  = 10'b0111101001,
    MBOX_RDY_FOR_DLEN_SPARSE = 10'b0010111100,
    MBOX_RDY_FOR_DATA_SPARSE = 10'b1110011010,
    MBOX_EXECUTE_UC_SPARSE   = 10'b1101101110,
    MBOX_EXECUTE_SOC_SPARSE  = 10'b1010100011,
    MBOX_EXECUTE_TAP_SPARSE  = 10'b1100110101,
    MBOX_ERROR_SPARSE        = 10'b1001011001
  } mbox_fsm_state_sparse_e;

  localparam int MboxStateWidthLogic = 3;
  typedef enum logic [MboxStateWidthLogic-1:0] {
    MBOX_IDLE         = 3'b000,
    MBOX_RDY_FOR_CMD  = 3'b001,
    MBOX_RDY_FOR_DLEN = 3'b011,
    MBOX_RDY_FOR_DATA = 3'b010,
    MBOX_EXECUTE_UC   = 3'b110,
    MBOX_EXECUTE_SOC  = 3'b100,
    MBOX_EXECUTE_TAP  = 3'b101,
    MBOX_ERROR        = 3'b111
  } mbox_fsm_state_e;


// Encode sparse mbox FSM state to 3-bit value matching mbox_csr.rdl enum (mbox_fsm_e)
  function automatic logic [MboxStateWidthLogic-1:0] mboxsparse2logic(mbox_fsm_state_sparse_e st);
    unique case (st)
      MBOX_IDLE_SPARSE         : return MBOX_IDLE;
      MBOX_RDY_FOR_CMD_SPARSE  : return MBOX_RDY_FOR_CMD;
      MBOX_RDY_FOR_DLEN_SPARSE : return MBOX_RDY_FOR_DLEN;
      MBOX_RDY_FOR_DATA_SPARSE : return MBOX_RDY_FOR_DATA;
      MBOX_EXECUTE_UC_SPARSE   : return MBOX_EXECUTE_UC;
      MBOX_EXECUTE_SOC_SPARSE  : return MBOX_EXECUTE_SOC;
      MBOX_EXECUTE_TAP_SPARSE  : return MBOX_EXECUTE_TAP;
      MBOX_ERROR_SPARSE        : return MBOX_ERROR;
      default            : return MBOX_ERROR;
    endcase
  endfunction : mboxsparse2logic

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