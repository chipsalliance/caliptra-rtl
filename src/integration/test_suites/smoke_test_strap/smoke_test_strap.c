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

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include "riscv_hw_if.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"

volatile uint32_t* stdout           = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {
    
    uint64_t strap_reg;

    VPRINTF(LOW,"---------------------------\n");
    VPRINTF(LOW," Smoke test strap !!\n");
    VPRINTF(LOW,"---------------------------\n");

    //Call interrupt init
    init_interrupts();

    strap_reg = ((lsu_read_32(CLP_SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_H) << 32) |
                 (lsu_read_32(CLP_SOC_IFC_REG_SS_CALIPTRA_BASE_ADDR_L)      ));

    if (strap_reg != 0xba5eba11) {
        VPRINTF(FATAL, "Strap value 0x%x mismatch. Expected: 0x%x\n", strap_reg, 0xba5eba11);
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}
