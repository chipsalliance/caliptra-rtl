# SPDX-License-Identifier: Apache-2.0
#
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

python3 tools/scripts/reg_doc_gen.py \
$CALIPTRA_ROOT/src/integration/rtl/caliptra_reg.rdl \
$CALIPTRA_ROOT/src/keyvault/rtl/kv_reg.rdl \
$CALIPTRA_ROOT/src/pcrvault/rtl/pv_reg.rdl \
$CALIPTRA_ROOT/src/datavault/rtl/dv_reg.rdl \
$CALIPTRA_ROOT/src/ecc/rtl/ecc_reg.rdl \
$ADAMSBRIDGE_ROOT/src/mldsa_top/rtl/mldsa_reg.rdl \
$CALIPTRA_ROOT/src/sha512/rtl/sha512_reg.rdl \
$CALIPTRA_ROOT/src/sha256/rtl/sha256_reg.rdl \
$CALIPTRA_ROOT/src/soc_ifc/rtl/mbox_csr.rdl \
$CALIPTRA_ROOT/src/soc_ifc/rtl/sha512_acc_csr.rdl \
$CALIPTRA_ROOT/src/axi/rtl/axi_dma_reg.rdl \
$CALIPTRA_ROOT/src/soc_ifc/rtl/soc_ifc_reg.rdl \
$CALIPTRA_ROOT/src/hmac/rtl/hmac_reg.rdl \
$CALIPTRA_ROOT/src/doe/rtl/doe_reg.rdl \
$CALIPTRA_ROOT/src/keyvault/rtl/kv_def.rdl \
$CALIPTRA_ROOT/src/entropy_src/data/entropy_src.rdl \
$CALIPTRA_ROOT/src/csrng/data/csrng.rdl \
$CALIPTRA_ROOT/src/spi_host/data/spi_host.rdl \
$CALIPTRA_ROOT/src/uart/data/uart.rdl

python3 tools/scripts/reg_doc_gen.py \
$CALIPTRA_ROOT/src/soc_ifc/rtl/caliptra_top_reg.rdl \
$CALIPTRA_ROOT/src/soc_ifc/rtl/soc_ifc_doc.rdl \
$CALIPTRA_ROOT/src/soc_ifc/rtl/mbox_csr.rdl \
$CALIPTRA_ROOT/src/soc_ifc/rtl/sha512_acc_csr_doc.rdl
