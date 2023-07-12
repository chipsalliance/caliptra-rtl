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
package sha512_params_pkg;

  localparam SHA512_CORE_NAME0           = 32'h61327368; // "sha2"
  localparam SHA512_CORE_NAME1           = 32'h31322d35; // "-512"
  localparam SHA512_CORE_VERSION0        = 32'h3830302e; // "0.80"
  localparam SHA512_CORE_VERSION1        = 32'h00000000; // "0"

  localparam MODE_SHA_512_224     = 2'h0;
  localparam MODE_SHA_512_256     = 2'h1;
  localparam MODE_SHA_384         = 2'h2;
  localparam MODE_SHA_512         = 2'h3;

endpackage
//======================================================================
// EOF sha512_params_pkg.sv
//======================================================================
