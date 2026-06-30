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
volatile int error_count __attribute__((section(".dccm.persistent"))) = 0;
volatile int rst_count __attribute__((section(".dccm.persistent"))) = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define TB_CMD_WARM_RESET 0xF6
#define TB_CMD_COLD_RESET 0xF5
#define TB_CMD_TEST_PASS 0xFF
#define TB_CMD_TEST_FAIL 0x01

void main(void) {

    rst_count++;
    VPRINTF_LOW("----------------\nrst count = %d\n----------------\n", rst_count);

    VPRINTF_LOW("==================\nIFC RO Registers Test\n==================\n\n");

    ifc_register_group_t ro_reg_groups[] = {
        REG_GROUP_STRAPS_RO,
        REG_GROUP_STRAPS_RO_RO,
        REG_GROUP_STATUS_RO,
        REG_GROUP_SECURITY_RO,
        REG_GROUP_WATCHDOG_RO,
        REG_GROUP_CONTROL_RO,
        REG_GROUP_GENERIC_WIRES_RO,
        REG_GROUP_FUSE_RO,
        REG_GROUP_OWNER_PK_HASH_RO,
        REG_GROUP_INTERRUPT_GLOBAL_STATUS_RO,
        REG_GROUP_INTERRUPT_ERROR_COUNTERS_INCR_RO,
        REG_GROUP_INTERRUPT_NOTIF_COUNTERS_INCR_RO
    };

    const int num_groups =  sizeof(ro_reg_groups) / sizeof(ro_reg_groups[0]);

    if (rst_count == 1) {
        ifc_init();
        exclude_register(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0);

        // Loop through all RO register groups
        for (int i = 0; i < num_groups; i++) {
            ifc_register_group_t group = ro_reg_groups[i];

            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET, false);
        }

        // Loop through all RO register groups
        for (int i = 0; i < num_groups; i++) {
            ifc_register_group_t group = ro_reg_groups[i];
            // Write random values to all registers in this group
            write_random_to_register_group_and_track(group, &g_expected_data_dict);
            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET, false);
        }

        // Issue warm reset
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);

        // Halt the MCU
        while(1);

    } else if (rst_count == 2) {
        // Read all registers, expect register values to be retained for sticky registers
        for (int i = 0; i < num_groups; i++) {
            ifc_register_group_t group = ro_reg_groups[i];

            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, true, WARM_RESET, false);
        }

        // Issue cold reset
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);

        // Halt the MCU
        while(1);

    } else if (rst_count == 3) {
        // Read all registers, expect register values to be reset
        for (int i = 0; i < num_groups; i++) {
            ifc_register_group_t group = ro_reg_groups[i];

            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, true, COLD_RESET, false);
        }
    }

    VPRINTF_LOW("\nIFC Read-Only Register Access Tests Completed\n");

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (error_count == 0 ) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
}
