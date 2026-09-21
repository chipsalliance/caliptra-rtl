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
// Smoke test: confirm DCLS (Dual-Core Lockstep) corruption detection is DISABLED.
//
// The SW-writable disable-corruption register was removed from the Caliptra core.
// Corruption detection is now controlled by the subsystem (MCU / ss_dcls_en strap)
// and is reflected read-only in CPTRA_HW_CONFIG.DCLS_en (1=enabled, 0=disabled).
// Detection is disabled whenever:
//   - the core is in passive (non-subsystem) mode -- DCLS is ALWAYS disabled, or
//   - the subsystem drives ss_dcls_en=0 (this test uses +CLP_DCLS_DIS).
// This test reads CPTRA_HW_CONFIG and confirms DCLS_en == 0 in both situations.
// The enabled path is covered by smoke_test_dcls_inject (+CLP_DCLS_EN).

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include <stdint.h>
#include "printf.h"
#include "riscv_hw_if.h"

volatile uint32_t* stdout     = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {
    uint32_t hw_config;
    uint32_t ss_mode;
    uint32_t dcls_en;

    VPRINTF(LOW, "---------------------------\n");
    VPRINTF(LOW, " DCLS Disabled Smoke Test\n");
    VPRINTF(LOW, "---------------------------\n");

    init_interrupts();

    hw_config = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
    ss_mode   = (hw_config & SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK) ? 1u : 0u;
    dcls_en   = (hw_config & SOC_IFC_REG_CPTRA_HW_CONFIG_DCLS_EN_MASK)           ? 1u : 0u;

    VPRINTF(LOW, "CPTRA_HW_CONFIG=0x%x subsystem_mode=%u DCLS_en=%u\n",
            hw_config, ss_mode, dcls_en);

    // Confirm DCLS corruption detection is disabled:
    //   - passive (non-subsystem) mode: always disabled, or
    //   - subsystem mode with +CLP_DCLS_DIS: ss_dcls_en=0 -> DCLS_en=0.
    if (dcls_en != 0u) {
        VPRINTF(FATAL, "ERROR: DCLS_en=%u but expected 0 (disabled). subsystem_mode=%u\n",
                dcls_en, ss_mode);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    VPRINTF(LOW, "DCLS corruption detection disabled as expected (subsystem_mode=%u)\n", ss_mode);
    VPRINTF(LOW, "DCLS disabled smoke test PASSED\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
