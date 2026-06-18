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
// Smoke test for the DCLS (Dual-Core Lockstep) control register.
//
// Verifies that Caliptra firmware can read and write the
// internal_dcls_ctrl.disable_corruption_detection field, which uses
// MuBi4 encoding:
//   MuBi4True  (0x6) = corruption detection disabled  (reset value)
//   MuBi4False (0x9) = corruption detection enabled

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include <stdint.h>
#include "printf.h"
#include "riscv_hw_if.h"

// MuBi4 encoding used by the lockstep unit
#define MUBI4_TRUE  (0x6u)  // detection disabled
#define MUBI4_FALSE (0x9u)  // detection enabled

volatile uint32_t* stdout     = (uint32_t *)STDOUT;
volatile uint32_t  intr_count = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main() {
    uint32_t val;

    VPRINTF(LOW, "---------------------------\n");
    VPRINTF(LOW, " DCLS Ctrl Smoke Test\n");
    VPRINTF(LOW, "---------------------------\n");

    init_interrupts();

    // Step 1: Verify reset value is MuBi4True (detection disabled)
    val = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_DCLS_CTRL);
    val &= SOC_IFC_REG_INTERNAL_DCLS_CTRL_DISABLE_CORRUPTION_DETECTION_MASK;
    VPRINTF(LOW, "DCLS ctrl reset value: 0x%x (expect 0x%x)\n", val, MUBI4_TRUE);
    if (val != MUBI4_TRUE) {
        VPRINTF(FATAL, "ERROR: unexpected reset value 0x%x, expected MuBi4True (0x%x)\n",
                val, MUBI4_TRUE);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    // Step 2: Enable detection by writing MuBi4False
    VPRINTF(LOW, "Enabling DCLS corruption detection (MuBi4False = 0x%x)\n", MUBI4_FALSE);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_DCLS_CTRL, MUBI4_FALSE);

    val = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_DCLS_CTRL);
    val &= SOC_IFC_REG_INTERNAL_DCLS_CTRL_DISABLE_CORRUPTION_DETECTION_MASK;
    VPRINTF(LOW, "DCLS ctrl readback: 0x%x (expect 0x%x)\n", val, MUBI4_FALSE);
    if (val != MUBI4_FALSE) {
        VPRINTF(FATAL, "ERROR: readback 0x%x after write, expected MuBi4False (0x%x)\n",
                val, MUBI4_FALSE);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    // Step 3: Disable detection again by writing MuBi4True
    VPRINTF(LOW, "Disabling DCLS corruption detection (MuBi4True = 0x%x)\n", MUBI4_TRUE);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_DCLS_CTRL, MUBI4_TRUE);

    val = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_DCLS_CTRL);
    val &= SOC_IFC_REG_INTERNAL_DCLS_CTRL_DISABLE_CORRUPTION_DETECTION_MASK;
    VPRINTF(LOW, "DCLS ctrl readback: 0x%x (expect 0x%x)\n", val, MUBI4_TRUE);
    if (val != MUBI4_TRUE) {
        VPRINTF(FATAL, "ERROR: readback 0x%x after write, expected MuBi4True (0x%x)\n",
                val, MUBI4_TRUE);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    VPRINTF(LOW, "DCLS ctrl smoke test PASSED\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
