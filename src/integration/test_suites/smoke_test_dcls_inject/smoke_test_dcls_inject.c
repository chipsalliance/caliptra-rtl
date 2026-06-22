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
// Enables DCLS corruption detection, then asks the testbench to inject a
// lockstep mismatch (TB control code 0xbd forces lockstep_err_injection_en_i =
// El2MuBiTrue). The corruption asserts cptra_error_fatal and latches
// CPTRA_HW_ERROR_FATAL.rv_dcls_err = El2MuBiTrue (0x6).
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

// MuBi4 encoding used by the lockstep unit
#define MUBI4_TRUE  (0x6u)  // detection disabled
#define MUBI4_FALSE (0x9u)  // detection enabled

// Testbench control code that triggers the DCLS lockstep corruption injection
#define TB_CTRL_DCLS_INJECT (0xbdu)

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
    VPRINTF(LOW, " DCLS Corruption Inject Test\n");
    VPRINTF(LOW, "---------------------------\n");

    init_interrupts();

    // Step 1: Enable DCLS corruption detection (MuBi4False = detection enabled).
    // Reset value is MuBi4True (disabled), so this is required for the injected
    // corruption to propagate to corruption_detected_o.
    VPRINTF(LOW, "Enabling DCLS corruption detection (MuBi4False = 0x%x)\n", MUBI4_FALSE);
    lsu_write_32(CLP_SOC_IFC_REG_INTERNAL_DCLS_CTRL, MUBI4_FALSE);

    val = lsu_read_32(CLP_SOC_IFC_REG_INTERNAL_DCLS_CTRL);
    val &= SOC_IFC_REG_INTERNAL_DCLS_CTRL_DISABLE_CORRUPTION_DETECTION_MASK;
    if (val != MUBI4_FALSE) {
        VPRINTF(FATAL, "ERROR: detection not enabled, read 0x%x (expected 0x%x)\n", val, MUBI4_FALSE);
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    // Step 2: Ask the TB to inject a lockstep corruption. From here the TB takes
    // over: corruption_detected_o asserts, rv_dcls_err latches, cptra_error_fatal
    // fires, and the TB self-check ends the simulation with PASS/FAIL.
    VPRINTF(LOW, "Requesting TB lockstep corruption injection (ctrl 0x%x)\n", TB_CTRL_DCLS_INJECT);
    SEND_STDOUT_CTRL(TB_CTRL_DCLS_INJECT);

    // Spin — the fatal error disrupts FW; the TB self-check terminates the sim.
    while (1);
}
