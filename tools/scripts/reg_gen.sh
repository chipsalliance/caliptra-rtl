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
KV_DEF=$CALIPTRA_ROOT/src/keyvault/rdl/kv_def.rdl

# Jinja2 template dirs for the DV outputs; reg_gen.py is project-agnostic
# and takes them explicitly.
UVM_TPL=$CALIPTRA_ROOT/tools/templates/rdl/uvm

REG_GEN="python3 tools/scripts/reg_gen.py --uvm-template-dir $UVM_TPL"

$REG_GEN $CALIPTRA_ROOT/src/keyvault/rdl/kv_reg.rdl                   \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/keyvault/rtl/generated  \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/keyvault/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/pcrvault/rdl/pv_reg.rdl                   \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/pcrvault/rtl/generated  \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/pcrvault/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/datavault/rdl/dv_reg.rdl                  \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/datavault/rtl/generated \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/datavault/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/ecc/rdl/ecc_reg.rdl                       \
    --preload $KV_DEF                                                  \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/ecc/rtl/generated       \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/ecc/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/sha512/rdl/sha512_reg.rdl                 \
    --preload $KV_DEF                                                  \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/sha512/rtl/generated    \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/sha512/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/sha256/rdl/sha256_reg.rdl                 \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/sha256/rtl/generated    \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/sha256/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/sha3/rdl/sha3_reg.rdl                     \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/sha3/rtl/generated      \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/sha3/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/entropy_combiner/rdl/entropy_combiner_reg.rdl \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/entropy_combiner/rtl/generated \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/entropy_combiner/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/soc_ifc/rdl/mbox_csr.rdl                  \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/soc_ifc/rtl/generated   \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/soc_ifc/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/soc_ifc/rdl/sha512_acc_csr.rdl            \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/soc_ifc/rtl/generated   \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/soc_ifc/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/soc_ifc/rdl/soc_ifc_reg.rdl               \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/soc_ifc/rtl/generated   \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/soc_ifc/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/hmac/rdl/hmac_reg.rdl                     \
    --preload $KV_DEF                                                  \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/hmac/rtl/generated      \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/hmac/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/doe/rdl/doe_reg.rdl                       \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/doe/rtl/generated       \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/doe/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/axi/rdl/axi_dma_reg.rdl                   \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/axi/rtl/generated       \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/axi/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/aes/rdl/aes_clp_reg.rdl                   \
    --preload $KV_DEF                                                  \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/aes/rtl/generated       \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/aes/dv/generated

$REG_GEN $CALIPTRA_ROOT/src/libs/rdl/interrupt_regs.rdl               \
    --emit-rtl --rtl-output $CALIPTRA_ROOT/src/libs/rtl/generated      \
    --emit-dv  --dv-output  $CALIPTRA_ROOT/src/libs/dv/generated
