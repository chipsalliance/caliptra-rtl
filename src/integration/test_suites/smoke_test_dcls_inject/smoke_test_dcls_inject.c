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
// DCLS (Dual-Core Lockstep) corruption-injection test.
//
// Check if DCLS corruption detection is enabled, then asks the testbench to inject a
// lockstep mismatch (TB control code 0xbf forces lockstep_err_injection_en_i =
// El2MuBiTrue). The corruption asserts cptra_error_fatal and latches
// CPTRA_HW_ERROR_FATAL.rv_dcls_err =1.
//
// Because cptra_error_fatal disrupts firmware execution, this test does NOT
// signal pass/fail itself — the testbench self-check (in caliptra_top_tb_services.sv)
// verifies the latched error and ends the simulation.

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv-csr.h"
#include <stdint.h>
#include "printf.h"
#include "riscv_hw_if.h"

// Testbench control code that triggers the DCLS lockstep corruption injection
#define TB_CTRL_DCLS_INJECT (0xbfu)

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
    VPRINTF(LOW, " DCLS Corruption Inject Test\n");
    VPRINTF(LOW, "---------------------------\n");

    init_interrupts();

    // Step 1: Confirm the precondition for a meaningful injection. 
    //   (a) DCLS_en == 1 (detection enabled)      -> proceed to inject, or
    //   (b) we are NOT in subsystem mode (passive) -> DCLS is always disabled here,
    //       so injection is not applicable; skip and pass.
    hw_config = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_CONFIG);
    ss_mode   = (hw_config & SOC_IFC_REG_CPTRA_HW_CONFIG_SUBSYSTEM_MODE_EN_MASK) ? 1u : 0u;
    dcls_en   = (hw_config & SOC_IFC_REG_CPTRA_HW_CONFIG_DCLS_EN_MASK)           ? 1u : 0u;
    VPRINTF(LOW, "CPTRA_HW_CONFIG=0x%x subsystem_mode=%u DCLS_en=%u\n",
            hw_config, ss_mode, dcls_en);

    if (!dcls_en) {
        if (!ss_mode) {
            // Passive (non-subsystem) mode: DCLS is always disabled; injection is
            // not applicable. Skip and pass.
            VPRINTF(LOW, "Non-subsystem mode: DCLS disabled; skipping injection.\n");
            VPRINTF(LOW, "DCLS corruption inject test PASSED (detection not applicable)\n");
            SEND_STDOUT_CTRL(0xff);
            while (1);
        }
        // Subsystem mode but detection disabled: the test expects detection enabled
        // here (run with +CLP_DCLS_EN). Injecting now would never latch the error,
        // so flag the unexpected state instead of silently passing.
        VPRINTF(FATAL, "ERROR: subsystem mode but DCLS_en=0 (expected enabled via +CLP_DCLS_EN)\n");
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    // Step 2: Detection confirmed enabled -- ask the TB to inject a lockstep
    // corruption. From here the TB takes over: corruption_detected_o asserts,
    // rv_dcls_err latches, cptra_error_fatal fires, and the TB self-check ends the
    // simulation with PASS/FAIL.
    VPRINTF(LOW, "DCLS enabled; requesting TB lockstep corruption injection (ctrl 0x%x)\n",
            TB_CTRL_DCLS_INJECT);
    SEND_STDOUT_CTRL(TB_CTRL_DCLS_INJECT);

    // Spin -- the fatal error disrupts FW; the TB self-check terminates the sim.
    while (1);
}
