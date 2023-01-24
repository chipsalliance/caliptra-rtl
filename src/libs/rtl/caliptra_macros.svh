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

`ifndef CALIPTRA_MACROS
`define CALIPTRA_MACROS

  //Debug values for obfuscated secrets when we unlock debug mode through security state
  `define DEBUG_MODE_OBF_KEY {256{1'b1}}
  `define DEBUG_MODE_UDS_SEED {384{1'b1}}
  `define DEBUG_MODE_FIELD_ENTROPY {1024{1'b1}}
  //Dword values to write into all KV entries during debug mode
  `define DEBUG_MODE_KV_0 {32'hAAAA_AAAA}
  `define DEBUG_MODE_KV_1 {32'h5555_5555}
`endif
