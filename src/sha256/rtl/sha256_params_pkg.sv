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
//

package sha256_params_pkg;

  localparam SHA256_CORE_NAME0        = 32'h61327368; // "sha2"
  localparam SHA256_CORE_NAME1        = 32'h35362d32; // "-256"
  localparam SHA256_CORE_VERSION0     = 32'h3830312e; // "1.80"
  localparam SHA256_CORE_VERSION1     = 32'h00000000; // "0"

  localparam SHA256_MODE_SHA_224     = 1'h0;
  localparam SHA256_MODE_SHA_256     = 1'h1;

endpackage
//======================================================================
// EOF sha256_params_pkg.sv
//======================================================================
