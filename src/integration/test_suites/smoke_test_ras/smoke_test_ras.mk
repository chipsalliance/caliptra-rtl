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
# smoke_test_ras exercises RISC-V exception capture (ICCM/DCCM uncorrectable ECC
# faults), so it opts into the shared trap handler's exception bookkeeping. This
# define reaches both smoke_test_ras.c and the shared caliptra_isr.c compile,
# enabling rv_exception_struct_s + the exc_flag recording path.
TEST_CFLAGS += -DRV_EXCEPTION_STRUCT
