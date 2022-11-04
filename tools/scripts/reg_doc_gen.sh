# SPDX-License-Identifier: Apache-2.0
# Copyright 2022 Microsoft Corporation or its affiliates.
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

python tools/scripts/reg_doc_gen.py \
src/integration/rtl/caliptra_reg.rdl \
src/keyvault/rtl/kv_reg.rdl \
src/ecc/rtl/ecc_reg.rdl \
src/sha512/rtl/sha512_reg.rdl \
src/mbox/rtl/mbox_reg.rdl \
src/mbox/rtl/mbox_csr.rdl \
src/hmac/rtl/hmac_reg.rdl \
src/doe/rtl/doe_reg.rdl \
src/keyvault/rtl/kv_def.rdl
