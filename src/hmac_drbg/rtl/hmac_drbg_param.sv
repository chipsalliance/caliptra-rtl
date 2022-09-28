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
//======================================================================
//
// hmac_drbg_param.sv
// --------
// HMAC384-DRBG parameters
//
// 
// 
//======================================================================
  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam HMAC_DRBG_SEED_LENGTH        = 32'd384;
  localparam HMAC_DRBG_GARBAGE_LENGTH     = 32'd1024 -32'd384- HMAC_DRBG_SEED_LENGTH - 32'd8 - 32'd1 - 32'd12; // 1 for header and 12 bit for message length

  localparam HMAC_DRBG_KEYGEN             = 0;
  localparam HMAC_DRBG_SIGNING            = 1;

  localparam HMAC_DRBG_PRIME              = 384'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973;
  
