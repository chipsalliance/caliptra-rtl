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
// STDOUT 0xc4 starts the SoC BFM checks.
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "printf.h"
#include <stdint.h>

volatile uint32_t *stdout = (uint32_t *)STDOUT;
volatile uint32_t intr_count = 0;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};
enum printf_verbosity verbosity_g = LOW;

void main(void) {
    uint32_t config = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
#ifdef CALIPTRA_HWCONFIG_SUBSYSTEM_MODE
    if (!(config & SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK)) {
#else
    if (config & SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK) {
#endif
        SEND_STDOUT_CTRL(0x01);
        while (1);
    }
    // Discard x20 reads so register-file faults leave retired trace unchanged.
    __asm__ volatile (
        "li s4, 0xdca15afe\n"
        "li t0, %0\n"
        "li t1, 0xc4\n"
        "sw t1, 0(t0)\n"
        "1: add zero, s4, zero\n"
        "add zero, s4, zero\n"
        "j 1b\n"
        : : "i" (STDOUT) : "s4", "t0", "t1", "memory");
    __builtin_unreachable();
}
