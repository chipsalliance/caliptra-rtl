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

#ifndef RISCV_HW_IF_H
    #define RISCV_HW_IF_H

#include <stdint.h>

inline void lsu_write_32 (volatile uint32_t* ptr, uint32_t data) {
    *ptr = data;
}

inline uint32_t lsu_read_32 (volatile uint32_t* ptr) {
    return *ptr;
}

#endif /* RISCV_HW_IF_H */
