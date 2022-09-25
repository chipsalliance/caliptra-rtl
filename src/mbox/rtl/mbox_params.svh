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

`ifndef MBOX_PARAMS
`define MBOX_PARAMS

parameter MBOX_INF_ADDR_W = 18;
parameter MBOX_DATA_W = 32;
parameter MBOX_USER_W = 32;

parameter MBOX_SIZE_KB = 128;
parameter MBOX_DEPTH = (MBOX_SIZE_KB * 1024 * 8) / MBOX_DATA_W;
parameter MBOX_ADDR_W = $clog2(MBOX_DEPTH);

//memory map
parameter MBOX_DIR_START_ADDR     = 18'h0_0000;
parameter MBOX_DIR_END_ADDR       = 18'h1_FFFF;
parameter MBOX_MEM_START_ADDR     = 18'h2_0000;
parameter MBOX_MEM_END_ADDR       = 18'h2_FFFF;
parameter MBOX_REG_MEM_START_ADDR = 18'h3_0000;
parameter MBOX_REG_MEM_END_ADDR   = 18'h3_FFFF;

`endif
