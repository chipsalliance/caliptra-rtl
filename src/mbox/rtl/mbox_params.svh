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

parameter MBOX_ADDR_W = 32;
parameter MBOX_DATA_W = 32;
parameter MBOX_USER_W = 32;

//memory map
parameter MBOX_MEM_START_ADDR = 32'h3000_0000;
parameter MBOX_MEM_END_ADDR = 32'h3002_00FF;
parameter FUNC_REG_MEM_START_ADDR = 32'h3002_0100;
parameter FUNC_REG_MEM_END_ADDR = 32'h3002_01FF;
parameter FUSE_REG_MEM_START_ADDR = 32'h3002_0200;
parameter FUSE_REG_MEM_END_ADDR = 32'h3002_02FF;

`endif