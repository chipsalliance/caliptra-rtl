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
#include "ifc_reg.h"
#include "soc_access.h"
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "printf.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>

volatile char* stdout = (char *)STDOUT;
volatile uint32_t  intr_count = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define TB_CMD_TEST_PASS 0xFF
#define TB_CMD_TEST_FAIL 0x01

int check_if_soc_write_ignored(uintptr_t reg_addr) {
    uint32_t initial_value = lsu_read_32(reg_addr);
    uint32_t rand_value = xorshift32();

    VPRINTF_LOW("Testing SoC write to 0x%x\n", reg_addr);
    if(soc_write_32(reg_addr, rand_value)) {
        VPRINTF_LOW("Can't access register from SoC, addr: 0x%x\n", reg_addr);
        return 1;
    }

    uint32_t new_value = lsu_read_32(reg_addr);

    if(new_value != initial_value) {
        VPRINTF_LOW("Register value changed after SoC write, written: 0x%x to 0x%x, expected (initial): 0x%x\n", rand_value, reg_addr, initial_value);
        return 1;
    }
    return 0;
}

void main(void) {
    int error_count = 0;
    VPRINTF_LOW("==================\nDMA Registers SoC Access\n==================\n\n");

    uintptr_t soc_ro_regs[] = {
        CLP_AXI_DMA_REG_CTRL,
        CLP_AXI_DMA_REG_SRC_ADDR_L,
        CLP_AXI_DMA_REG_SRC_ADDR_H,
        CLP_AXI_DMA_REG_DST_ADDR_L,
        CLP_AXI_DMA_REG_DST_ADDR_H,
        CLP_AXI_DMA_REG_BYTE_COUNT,
        CLP_AXI_DMA_REG_BLOCK_SIZE
    };
    const int soc_ro_reg_count =  sizeof(soc_ro_regs) / sizeof(soc_ro_regs[0]);

    for(int i = 0; i < soc_ro_reg_count; i++) {
        error_count += check_if_soc_write_ignored(soc_ro_regs[i]);
    }

    if (error_count == 0 ) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
}
