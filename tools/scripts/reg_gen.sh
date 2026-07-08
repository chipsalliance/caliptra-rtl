# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

# Shared kv_def.rdl is referenced by several blocks (aes_clp, hmac, sha512, ecc).
# It is preloaded into the compiler on those blocks via --preload so that its
# types are visible in the shared root scope during elaboration; consumer RDLs
# do NOT `include it (see reg_gen.py header comment for rationale).
KV_DEF=$CALIPTRA_ROOT/src/keyvault/rtl/kv_def.rdl

# Jinja2 template dirs for the DV outputs; reg_gen.py is project-agnostic
# and takes them explicitly.
UVM_TPL=$CALIPTRA_ROOT/tools/templates/rdl/uvm

REG_GEN="python3 tools/scripts/reg_gen.py --uvm-template-dir $UVM_TPL"

$REG_GEN $CALIPTRA_ROOT/src/keyvault/rtl/kv_reg.rdl                     --emit-rtl --emit-dv
$REG_GEN $CALIPTRA_ROOT/src/pcrvault/rtl/pv_reg.rdl                     --emit-rtl --emit-dv
$REG_GEN $CALIPTRA_ROOT/src/datavault/rtl/dv_reg.rdl                    --emit-rtl --emit-dv
$REG_GEN --preload $KV_DEF $CALIPTRA_ROOT/src/ecc/rtl/ecc_reg.rdl       --emit-rtl --emit-dv
$REG_GEN --preload $KV_DEF $CALIPTRA_ROOT/src/sha512/rtl/sha512_reg.rdl --emit-rtl --emit-dv
$REG_GEN $CALIPTRA_ROOT/src/sha256/rtl/sha256_reg.rdl                   --emit-rtl --emit-dv
$REG_GEN $CALIPTRA_ROOT/src/sha3/rtl/sha3_reg.rdl                       --emit-rtl --emit-dv
$REG_GEN $CALIPTRA_ROOT/src/soc_ifc/rtl/mbox_csr.rdl                    --emit-rtl --emit-dv
$REG_GEN $CALIPTRA_ROOT/src/soc_ifc/rtl/sha512_acc_csr.rdl              --emit-rtl --emit-dv
$REG_GEN $CALIPTRA_ROOT/src/soc_ifc/rtl/soc_ifc_reg.rdl                 --emit-rtl --emit-dv
$REG_GEN --preload $KV_DEF $CALIPTRA_ROOT/src/hmac/rtl/hmac_reg.rdl     --emit-rtl --emit-dv
$REG_GEN $CALIPTRA_ROOT/src/doe/rtl/doe_reg.rdl                         --emit-rtl --emit-dv
$REG_GEN $CALIPTRA_ROOT/src/axi/rtl/axi_dma_reg.rdl                     --emit-rtl --emit-dv
$REG_GEN --preload $KV_DEF $CALIPTRA_ROOT/src/aes/rtl/aes_clp_reg.rdl   --emit-rtl --emit-dv
