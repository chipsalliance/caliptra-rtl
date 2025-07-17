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

`ifndef OCP_LOCK_PKG
`define OCP_LOCK_PKG

package soc_ifc_pkg;

    import kv_defines_pkg::*;

    localparam OCP_LOCK_RT_OBF_KEY_KV_SLOT  = 16; // Stores the runtime MEK obf key (derived from devid chain)
    localparam OCP_LOCK_HEK_SEED_KV_SLOT    = 22; // Destination for deobf HEK seed, also for derived HEK
                                                  // TODO -- do we need to be prescriptive about this, now that RT_OBF_KEY is used for MEK decryption instead of HEK?
    localparam OCP_LOCK_KEY_RELEASE_KV_SLOT = 23; // Stores the fully decrypted MEK
    localparam OCP_LOCK_HEK_NUM_DWORDS      = 8;  // 256b HEK Seed

    // FIXME is this the correct set of KV permissions?
    localparam OCP_LOCK_HEK_SEED_DEST_VALID = (1 << KV_DEST_IDX_HMAC_KEY) |
                                              (1 << KV_DEST_IDX_HMAC_BLOCK) |
                                              (1 << KV_DEST_IDX_AES_KEY);

endpackage

`endif
