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
#include "riscv_hw_if.h"
#include <stdint.h>
#include "printf.h"

volatile uint32_t intr_count = 0;
volatile uint32_t *stdout = (uint32_t *)STDOUT;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = HIGH;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

// Value the SoC BFM writes to CPTRA_FW_EXTENDED_ERROR_INFO_0 while the core is
// held in reset (see caliptra_top_tb_soc_bfm.sv, +SOC_WRITE_RST). The register
// is reset only on cptra_pwrgood, so the value survives the noncore reset
// deassertion and is observable here in firmware.
#define SOC_WR_RST_EXPECTED 0xBAADB000

void main(void) {
    VPRINTF(LOW, "----------------------------------\nSoC Write Under Reset Test  !!\n----------------------------------\n");

    uint32_t rdata = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_FW_EXTENDED_ERROR_INFO_0);
    if (rdata != SOC_WR_RST_EXPECTED) {
        VPRINTF(FATAL, "[FAIL] SoC write-under-reset value not observed by FW: expected=0x%08x got=0x%08x\n",
                (uint32_t)SOC_WR_RST_EXPECTED, rdata);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    VPRINTF(LOW, "FW observed SoC write-under-reset value 0x%08x\n", rdata);
    SEND_STDOUT_CTRL(0xff); // PASS
    while (1);
}
