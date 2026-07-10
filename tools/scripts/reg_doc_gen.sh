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
src/integration/data/caliptra_reg.rdl \
src/keyvault/data/kv_reg.rdl \
src/pcrvault/data/pv_reg.rdl \
src/datavault/data/dv_reg.rdl \
src/ecc/data/ecc_reg.rdl \
submodules/adams-bridge/src/abr_top/rtl/abr_reg.rdl \
src/sha512/data/sha512_reg.rdl \
src/sha256/data/sha256_reg.rdl \
src/sha3/data/kmac_reg.rdl \
src/sha3/data/sha3_reg.rdl \
src/soc_ifc/data/mbox_csr.rdl \
src/soc_ifc/data/sha512_acc_csr.rdl \
src/axi/data/axi_dma_reg.rdl \
src/soc_ifc/data/soc_ifc_reg.rdl \
src/hmac/data/hmac_reg.rdl \
src/doe/data/doe_reg.rdl \
src/entropy_src/data/entropy_src.rdl \
src/csrng/data/csrng.rdl \
src/spi_host/data/spi_host.rdl \
src/uart/data/uart.rdl \
src/aes/data/aes.rdl \
src/aes/data/aes_clp_reg.rdl \
src/keyvault/data/kv_def.rdl

python3 tools/scripts/reg_doc_gen.py --param CALIPTRA_SS_MODE=true \
src/integration/data/caliptra_reg.rdl \
src/keyvault/data/kv_reg.rdl \
src/pcrvault/data/pv_reg.rdl \
src/datavault/data/dv_reg.rdl \
src/ecc/data/ecc_reg.rdl \
submodules/adams-bridge/src/abr_top/rtl/abr_reg.rdl \
src/sha512/data/sha512_reg.rdl \
src/sha256/data/sha256_reg.rdl \
src/sha3/data/kmac_reg.rdl \
src/sha3/data/sha3_reg.rdl \
src/soc_ifc/data/mbox_csr.rdl \
src/soc_ifc/data/sha512_acc_csr.rdl \
src/axi/data/axi_dma_reg.rdl \
src/soc_ifc/data/soc_ifc_reg.rdl \
src/hmac/data/hmac_reg.rdl \
src/doe/data/doe_reg.rdl \
src/entropy_src/data/entropy_src.rdl \
src/csrng/data/csrng.rdl \
src/spi_host/data/spi_host.rdl \
src/uart/data/uart.rdl \
src/aes/data/aes.rdl \
src/aes/data/aes_clp_reg.rdl \
src/keyvault/data/kv_def.rdl

python3 tools/scripts/reg_doc_gen.py \
src/soc_ifc/data/caliptra_top_reg.rdl \
src/soc_ifc/data/soc_ifc_doc.rdl \
src/soc_ifc/data/mbox_csr.rdl
