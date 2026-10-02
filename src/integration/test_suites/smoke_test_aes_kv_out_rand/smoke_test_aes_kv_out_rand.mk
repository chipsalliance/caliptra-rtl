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
# aes is not in the global COMP_LIB_NAMES (keeps aes.o out of every test's image
# to save ROM). This test calls the aes.c API, so opt the object + header back in
# here only.
OFILES += aes.o
AUX_LIB_DIR += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/aes
AUX_HEADER_FILES += $(CALIPTRA_ROOT)/src/integration/test_suites/libs/aes/aes.h
