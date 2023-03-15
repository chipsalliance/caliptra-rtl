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

// lsu_write_32 writes data to a given address pointer.  The uintptr_t is tied
// to the address width of the architeture and defines an appropriately sized
// value that can be cast to a void* and back indefinitely without losing
// information.  We cast to uint32_t since the value pointed to is definitively
// coded as a 32-bit register (uint32_t).
inline void lsu_write_32(uintptr_t addr, uint32_t data) {
  volatile uint32_t *ptr = (volatile uint32_t *)addr;
  *ptr = data;
}

// lsu_read_32 returns data from a given a address pointer.
inline uint32_t lsu_read_32(uintptr_t addr) {
  return *(volatile uint32_t *)addr;
}

#endif /* RISCV_HW_IF_H */
