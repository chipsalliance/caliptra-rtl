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
  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam SHA256_ADDR_NAME0       = 32'h00000000;
  localparam SHA256_ADDR_NAME1       = 32'h00000004;
  localparam SHA256_ADDR_VERSION0    = 32'h00000008;
  localparam SHA256_ADDR_VERSION1    = 32'h0000000c;

  localparam SHA256_ADDR_CTRL        = 32'h00000010;
  localparam SHA256_CTRL_INIT_BIT    = 0;
  localparam SHA256_CTRL_NEXT_BIT    = 1;
  localparam SHA256_CTRL_MODE_BIT    = 2;

  localparam SHA256_ADDR_STATUS      = 32'h00000018;
  //localparam STATUS_READY_BIT = 0;
  //localparam STATUS_VALID_BIT = 1;

  localparam SHA256_ADDR_BLOCK_START     = 32'h00000080;
  localparam SHA256_ADDR_BLOCK_END       = 32'h000000bf;

  localparam SHA256_ADDR_DIGEST_START    = 32'h00000100;
  localparam SHA256_ADDR_DIGEST_END      = 32'h0000011f;

  localparam SHA256_ADDR_INTR_START    = 32'h00000800;
  localparam SHA256_ADDR_INTR_END      = 32'h00000BFC;

  localparam SHA256_CORE_NAME0        = 32'h61327368; // "sha2"
  localparam SHA256_CORE_NAME1        = 32'h35362d32; // "-256"
  localparam SHA256_CORE_VERSION0     = 32'h3830312e; // "1.80"
  localparam SHA256_CORE_VERSION1     = 32'h00000000; // "0"

  localparam SHA256_MODE_SHA_224     = 1'h0;
  localparam SHA256_MODE_SHA_256     = 1'h1;

//======================================================================
// EOF sha256_param.sv
//======================================================================
