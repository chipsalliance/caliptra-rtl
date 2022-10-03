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

`ifndef MBOX_DEFINES
`define MBOX_DEFINES

`include "caliptra_sva.svh"
`include "mbox_params.svh"

//BOOT FSM
typedef enum logic [1:0] {
    BOOT_IDLE   = 2'b00,
    BOOT_FUSE   = 2'b01,
    BOOT_DONE   = 2'b11
} boot_fsm_state_e;

//MAILBOX FSM
typedef enum logic [2:0] {
    MBOX_IDLE         = 3'b000,
    MBOX_RDY_FOR_CMD  = 3'b001,
    MBOX_RDY_FOR_DLEN = 3'b011,
    MBOX_RDY_FOR_DATA = 3'b010,
    MBOX_EXECUTE_UC   = 3'b110,
    MBOX_EXECUTE_SOC  = 3'b100
} mbox_fsm_state_e;

//MAILBOX REQ
typedef struct packed {
    logic   [MBOX_INF_ADDR_W-1:0] addr;
    logic   [MBOX_DATA_W-1:0]     wdata;
    logic   [MBOX_USER_W-1:0]     user;
    logic                         write;
    logic                         soc_req;
} mbox_req_t;

typedef struct packed {
    logic   [MBOX_INF_ADDR_W-1:0] addr;
    logic   [MBOX_DATA_W-1:0]     wdata;
    logic                         write;
    logic                         soc_req;
} mbox_reg_req_t;

typedef struct packed {
    logic cs;
    logic we;
    logic [MBOX_ADDR_W-1:0] addr;
    logic [MBOX_DATA_W-1:0] wdata;
} mbox_sram_req_t;

typedef struct packed {
    logic [MBOX_DATA_W-1:0] rdata;
} mbox_sram_resp_t;

`endif