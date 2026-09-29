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

static void soc_write_register_group_and_track(ifc_register_group_t group, ifc_reg_exp_dict_t *dict,
                                               bool randomize, uint32_t write_data) {
    int count = get_register_count(group);

    for (int i = 0; i < count; i++) {
        const ifc_register_info_t *reg = get_register_info(group, i);

        if (!reg || is_register_excluded(reg->address)) continue;

        uint32_t value = randomize ? xorshift32() : write_data;
        uint32_t mask = get_register_mask(reg->address);

        if (set_reg_exp_data(dict, reg->address, value, mask, true, group, true) != 0) {
            VPRINTF(ERROR, "Dictionary full\n");
            SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
            while(1);
        }
        soc_write_32(reg->address, value);
    }
}

static void write_and_verify_groups(const ifc_register_group_t groups[], int num_groups,
                                    bool use_soc_access, int reset_type) {
    for (int i = 0; i < num_groups; i++) {
        ifc_register_group_t group = groups[i];

        if (use_soc_access) soc_write_register_group_and_track(group, &g_expected_data_dict, true, 0);
        else write_random_to_register_group_and_track(group, &g_expected_data_dict);
        error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, reset_type, false);
    }
}

static void verify_retained_then_write_groups(const ifc_register_group_t groups[],
                                              int num_groups) {
    for (int i = 0; i < num_groups; i++) {
        ifc_register_group_t group = groups[i];

        error_count += read_register_group_and_verify(group, &g_expected_data_dict, true, WARM_RESET, false);
        soc_write_register_group_and_track(group, &g_expected_data_dict, true, 0);
        error_count += read_register_group_and_verify(group, &g_expected_data_dict, false, WARM_RESET, false);
    }
}

static void write_and_verify_fuse(uint32_t value) {
    soc_write_register_group_and_track(REG_GROUP_FUSE_RO, &g_expected_data_dict, false, value);
    read_register_group_and_verify(REG_GROUP_FUSE_RO, &g_expected_data_dict, false, COLD_RESET, false);
}

void main(void) {

    rst_count++;
    VPRINTF(LOW,  "= (rst count: %d) IFC SoC RW, Caliptra RO Registers Test: SVN, Manuf DBG Unlock =\n\n", rst_count);

    ifc_register_group_t ro_reg_groups[] = {
        REG_GROUP_SVN_RO,
        REG_GROUP_MANUF_DBG_UNLOCK_RO
    };

    const int num_groups = sizeof(ro_reg_groups) / sizeof(ro_reg_groups[0]);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x1AA2);

    if (rst_count == 1) {
        ifc_init();

        write_and_verify_groups(ro_reg_groups, num_groups, true, COLD_RESET);
        write_and_verify_fuse(1);
        write_and_verify_groups(ro_reg_groups, num_groups, false, COLD_RESET);

        // CPTRA_FUSE_WR_DONE must remain set once written.
        write_and_verify_fuse(1);

        SEND_STDOUT_CTRL(TB_CMD_WARM_RESET);
        while(1);

    } else if (rst_count == 2) {
        // Sticky registers must retain their values across warm reset.
        verify_retained_then_write_groups(ro_reg_groups, num_groups);

        SEND_STDOUT_CTRL(TB_CMD_COLD_RESET);
        while(1);

    } else if (rst_count == 3) {
        write_and_verify_groups(ro_reg_groups, num_groups, true, COLD_RESET);

        // Write 0 to CPTRA_FUSE_WR_DONE register, make sure it's not locked
        write_and_verify_fuse(0);

        // All registers should be unlocked following cold reset.
        write_and_verify_groups(ro_reg_groups, num_groups, true, COLD_RESET);
    }

    // Test multiple inflight SoC AXI transactions
    enum { NUM_INFLIGHT = 2 };
    const uint32_t write_addrs[] = {
        CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_0,
        CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_1,
    };
    const uint32_t read_addrs[] = {
        CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_2,
        CLP_SOC_IFC_REG_FUSE_MANUF_DBG_UNLOCK_TOKEN_3,
    };
    uint32_t write_data[] = {xorshift32(), xorshift32()};
    uint32_t write_user[NUM_INFLIGHT][1] = {{0}, {0}};
    uint8_t write_strb[NUM_INFLIGHT][1] = {{0xf}, {0xf}};
    axi_req_t writes[NUM_INFLIGHT];
    axi_req_t reads[NUM_INFLIGHT];

    for (int i = 0; i < NUM_INFLIGHT; i++) {
        writes[i] = (axi_req_t) {
            .addr = write_addrs[i],
            .axuser = 0,
            .burst = AXI_BURST_INCR,
            .len = 1,
            .write = true,
            .read = false,
            .use_id = true,
            .id = i + 1,
            .wuser = write_user[i],
            .wdata = &write_data[i],
            .wstrb = write_strb[i],
        };
        reads[i] = (axi_req_t) {
            .addr = read_addrs[i],
            .axuser = 0,
            .burst = AXI_BURST_INCR,
            .len = 1,
            .write = false,
            .read = true,
            .use_id = true,
            .id = i + 3,
        };
    }

    // Send address and simulate data delay
    for (int i = 0; i < NUM_INFLIGHT; i++) soc_write_addr(writes[i]);

    // Send address and simulate stall
    for (int i = 0; i < NUM_INFLIGHT; i++) soc_read_addr(reads[i]);

    for (int i = 0; i < NUM_INFLIGHT; i++) soc_write_data(writes[i]);

    // Get responses
    axi_resp_t resp;
    for (int i = 0; i < NUM_INFLIGHT; i++) {
        uint32_t value = lsu_read_32(writes[i].addr);
        resp = soc_write_resp(writes[i]);
        if (resp.resp != 0 || value != write_data[i]) {
            VPRINTF(LOW, "(0x%x): write failed, expected: %x, got %x!\n", writes[i].addr, write_data[i], value);
            error_count++;
        }
    }

    for (int i = 0; i < NUM_INFLIGHT; i++) {
        uint32_t value = lsu_read_32(reads[i].addr);
        resp = soc_read_resp(reads[i]);
        if (resp.resp != 0 || value != resp.rdata) {
            VPRINTF(LOW, "(0x%x): read failed, expected: %x, got %x!\n", reads[i].addr, value, resp.rdata);
            error_count++;
        }
    }

    for (uint8_t ii = 0; ii < 160; ii++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }

    if (error_count == 0 ) {
        SEND_STDOUT_CTRL(TB_CMD_TEST_PASS);
    } else {
        SEND_STDOUT_CTRL(TB_CMD_TEST_FAIL);
    }
}
