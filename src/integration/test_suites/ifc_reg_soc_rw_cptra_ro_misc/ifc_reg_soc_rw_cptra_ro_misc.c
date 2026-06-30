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

void soc_write_random_to_register_group_and_track(ifc_register_group_t group, ifc_reg_exp_dict_t *dict) {
    int count = get_register_count(group);
    VPRINTF_LOW( "Writing random values to all %s registers (%d total):\n", get_group_name(group), count);

    bool ro_reg = false;

    for (int i = 0; i < count; i++) {
        const ifc_register_info_t *reg = get_register_info(group, i);

        if (reg) {
            // Check if this register should be excluded using our efficient method
            if (!is_register_excluded(reg->address)) {
                // Generate a unique value for each register
                uint32_t rand_value = xorshift32();

                /* Get mask for this register */
                uint32_t mask = get_register_mask(reg->address);

                // Store in dictionary
                if (!ro_reg) {
                    if (set_reg_exp_data(dict, reg->address, rand_value, mask, true, group, true) != 0) {
                        VPRINTF_MEDIUM("  WARNING: Could not store expected data for %s[%d]\n", get_group_name(group), i);
                    }
                }

                VPRINTF_MEDIUM("  Writing 0x%08x to %s[%d] (0x%08x)\n", rand_value, get_group_name(group), i, reg->address);
                soc_write_32(reg->address, rand_value);
            } else {
                VPRINTF_MEDIUM("  Skipping excluded register %s[%d] (0x%08x)\n", get_group_name(group), i, reg->address);
            }
        }
    }
}

void soc_write_to_register_group_and_track(ifc_register_group_t group, uint32_t write_data, ifc_reg_exp_dict_t *dict) {
    int count = get_register_count(group);
    VPRINTF_LOW( "Writing fixed value to all %s registers (%d total):\n", get_group_name(group), count);

    for (int i = 0; i < count; i++) {
        const ifc_register_info_t *reg = get_register_info(group, i);

        if (reg) {
            // Check if this register should be excluded using our efficient method
            if (!is_register_excluded(reg->address)) {

                /* Get mask for this register */
                uint32_t mask = get_register_mask(reg->address);

                // Store in dictionary
                if (set_reg_exp_data(dict, reg->address, write_data, mask, true, group, true) != 0) {
                    VPRINTF_MEDIUM("  WARNING: Could not store expected data for %s[%d]\n", get_group_name(group), i);
                }

                VPRINTF_MEDIUM("  Writing 0x%08x to %s[%d] (0x%08x)\n", write_data, get_group_name(group), i, reg->address);
                soc_write_32(reg->address, write_data);
            } else {
                VPRINTF_MEDIUM("  Skipping excluded register %s[%d] (0x%08x)\n", get_group_name(group), i, reg->address);
            }
        }
    }
}

void main(void) {

    rst_count++;
    VPRINTF_LOW( "----------------\nrst count = %d\n----------------\n", rst_count);

    VPRINTF_LOW( "==================\nIFC SoC RW, Caliptra RO Registers Test: SVN, Manuf DBG Unlock\n==================\n\n");

    ifc_register_group_t ro_reg_groups[] = {
        REG_GROUP_SVN_RO,
        REG_GROUP_MANUF_DBG_UNLOCK_RO
    };

    const int num_groups =  sizeof(ro_reg_groups) / sizeof(ro_reg_groups[0]);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x1A7F);

    if (rst_count == 1) {
        ifc_init();

        // Loop through all RW register groups
        for (int i = 0; i < num_groups; i++) {
            ifc_register_group_t group = ro_reg_groups[i];

            // Write random values to all registers in this group
            soc_write_random_to_register_group_and_track(group, &g_expected_data_dict);

            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET, false);
        }

        soc_write_to_register_group_and_track(REG_GROUP_FUSE_RO, 0x1, &g_expected_data_dict);

        read_register_group_and_verify(REG_GROUP_FUSE_RO, &g_expected_data_dict, false, COLD_RESET, false);

        for (int i = 0; i < num_groups; i++) {
            ifc_register_group_t group = ro_reg_groups[i];

            // Write random values to all registers in this group
            write_random_to_register_group_and_track(group, &g_expected_data_dict);

            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET, false);
        }

        // Write 0 to CPTRA_FUSE_WR_DONE register, make sure it remains 1
        soc_write_to_register_group_and_track(REG_GROUP_FUSE_RO, 0x1, &g_expected_data_dict);

        read_register_group_and_verify(REG_GROUP_FUSE_RO, &g_expected_data_dict, false, COLD_RESET, false);

        // Issue warm reset
        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);

        while(1);

    } else if (rst_count == 2) {

        // Read all registers, expect register values to be retained fr sticky registers
        for (int i = 0; i < num_groups; i++) {
            ifc_register_group_t group = ro_reg_groups[i];

            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, true, WARM_RESET, false);

            // Write random values to all registers in this group
            soc_write_random_to_register_group_and_track(group, &g_expected_data_dict);

            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, WARM_RESET, false);
        }

        // Issue cold reset
        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);

        while(1);

    } else if (rst_count == 3) {
        // Loop through all RW register groups
        for (int i = 0; i < num_groups; i++) {
            ifc_register_group_t group = ro_reg_groups[i];

            // Write random values to all registers in this group
            soc_write_random_to_register_group_and_track(group, &g_expected_data_dict);

            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET, false);
        }

        // Write 0 to CPTRA_FUSE_WR_DONE register, make sure it's not locked
        soc_write_to_register_group_and_track(REG_GROUP_FUSE_RO, 0x0, &g_expected_data_dict);
        read_register_group_and_verify(REG_GROUP_FUSE_RO, &g_expected_data_dict, false, COLD_RESET, false);

        // Loop through all RW register groups -- all registers should be unlocked
        for (int i = 0; i < num_groups; i++) {
            ifc_register_group_t group = ro_reg_groups[i];

            // Write random values to all registers in this group
            soc_write_random_to_register_group_and_track(group, &g_expected_data_dict);

            // Read registers and verify data matches
            error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, COLD_RESET, false);
        }
    }

    // Test multiple inflight SoC AXI transactions
    uint32_t w1_data = xorshift32(), w2_data = xorshift32();
    axi_req_t w1, w2, r1, r2;
    w1 = (axi_req_t) {
        .addr = CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0,
        .axuser = 0,
        .burst = AXI_BURST_INCR,
        .len = 1,
        .write = true,
        .read  = false,
        .use_id = true,
        .id    = 1,
        .wuser = (uint32_t[]){0},
        .wdata = (uint32_t[]){w1_data},
        .wstrb = (uint8_t[]){0xf}
    };
    w2 = (axi_req_t) {
        .addr = CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1,
        .axuser = 0,
        .burst = AXI_BURST_INCR,
        .len = 1,
        .write = true,
        .read  = false,
        .use_id = true,
        .id    = 2,
        .wuser = (uint32_t[]){0},
        .wdata = (uint32_t[]){w2_data},
        .wstrb = (uint8_t[]){0xf}
    };
    r1 = (axi_req_t) {
        .addr = CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2,
        .axuser = 0,
        .burst = AXI_BURST_INCR,
        .len = 1,
        .write = false,
        .read = true,
        .use_id = true,
        .id    = 3,
    };
    r2 = (axi_req_t) {
        .addr = CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3,
        .axuser = 0,
        .burst = AXI_BURST_INCR,
        .len = 1,
        .write = false,
        .read = true,
        .use_id = true,
        .id    = 4,
    };

    // Send address and simulate data delay
    soc_write_addr(w1);
    soc_write_addr(w2);
    // Send address and simulate stall
    soc_read_addr(r1);
    soc_read_addr(r2);

    soc_write_data(w1);
    soc_write_data(w2);

    // Get responses
    axi_resp_t resp;
    uint32_t value = lsu_read_32(w1.addr);
    resp = soc_write_resp(w1);
    if (resp.resp != 0 || value != w1_data) {
        VPRINTF_LOW( "Write to 0x%x failed, expected: %x, got %x!\n", w1.addr, w1_data, value);
        error_count++;
    }
    value = lsu_read_32(w2.addr);
    resp = soc_write_resp(w2);
    if (resp.resp != 0 || value != w2_data) {
        VPRINTF_LOW( "Write to 0x%x failed, expected: %x, got %x!\n", w2.addr, w2_data, value);
        error_count++;
    }
    value = lsu_read_32(r1.addr);
    resp = soc_read_resp(r1);
    if (resp.resp != 0 || value != resp.rdata) {
        VPRINTF_LOW( "Read from 0x%x failed, expected: %x, got %x!\n", r1.addr, value, resp.rdata);
        error_count++;
    }
    value = lsu_read_32(r2.addr);
    resp = soc_read_resp(r2);
    if (resp.resp != 0 || value != resp.rdata) {
        VPRINTF_LOW( "Read from 0x%x failed, expected: %x, got %x!\n", r2.addr, value, resp.rdata);
        error_count++;
    }

    VPRINTF_LOW( "\nIFC SoC Read-Write, Caliptra Read-Only Register Access Tests Completed\n");

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (error_count == 0 ) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
}
