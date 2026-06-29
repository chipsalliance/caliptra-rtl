// SPDX-License-Identifier: Apache-2.0
// //
// // Licensed under the Apache License, Version 2.0 (the "License");
// // you may not use this file except in compliance with the License.
// // You may obtain a copy of the License at
// //
// // http://www.apache.org/licenses/LICENSE-2.0
// //
// // Unless required by applicable law or agreed to in writing, software
// // distributed under the License is distributed on an "AS IS" BASIS,
// // WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// // See the License for the specific language governing permissions and
// // limitations under the License.

#include <stddef.h>
#include "soc_access.h"
#include "caliptra_defines.h"
#include "riscv_hw_if.h"

#define AXI_WRITE      0x1
#define AXI_READ       0x2
#define AXI_WRITE_ADDR 0x4
#define AXI_WRITE_DATA 0x8
#define AXI_WRITE_RESP 0x10
#define AXI_READ_ADDR  0x20
#define AXI_READ_RESP  0x40
#define AXI_USE_ID     0x80
#define AXI_DEFAULT_MASK 0xF
#define AXI_DEFAULT_USER 0


axi_resp_t soc_access_32(axi_req_t req) {
    axi_resp_t axi_resp;
    // Set AXI address
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.addr);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x017F);

    // Set AXI burst
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.burst);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x087F);

    // Set AXI aXuser
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.axuser);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x077F);

    if (req.write) {
        // Clear SoC access queues
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x0A7F);

        for (int i = 0; i < req.len; i++) {
            // Push AXI wdata
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.wdata ? req.wdata[i] : 0);
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x027F);
            // Push AXI wuser
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.wuser ? req.wuser[i] : AXI_DEFAULT_USER);
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x067F);
            // Push AXI wstrb
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.wstrb ? (req.wstrb[i] & 0xF) : 0xF);
            lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x097F);
        }
    }

    uint32_t execute = (req.write ? AXI_WRITE : 0) | (req.read ? AXI_READ : 0) | (req.use_id ? AXI_USE_ID : 0) |
            ((req.len - 1) << 8) | (req.id << 16);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, execute);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x037F);

    if (req.ignore_resp)
        return (axi_resp_t){ .resp = 0, .rdata = 0 };

    while (1) {
        axi_resp_t axi_resp;

        // Check if AXI has finished
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x047F);
        axi_resp.resp = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);

        if(axi_resp.resp & 1) {
            axi_resp.resp = (axi_resp.resp >> 1) & 0b11;

            if (req.read) {
                for (int i = 0; i < req.len; i++) {
                    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x057F);
                    uint32_t rdata = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
                    if (i == 0) axi_resp.rdata = rdata;
                    if (req.rdata) req.rdata[i] = rdata;
                }
            }
            return axi_resp;
        }
    }
}

// intended to be used only after soc_access_32 with .ignore_resp = true
uint8_t soc_access_await_done() {
    while(1) {
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x047F);
        uint8_t resp = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
        if (resp & 1)
            return (resp >> 1) & 0b11; 
    }
}

uint8_t soc_masked_write_32(uint32_t reg_addr, uint32_t value, uint32_t mask) {
    axi_resp_t axi_resp;

    axi_resp = soc_access_32((axi_req_t){
        .addr = reg_addr,
        .axuser = AXI_DEFAULT_USER,
        .burst = AXI_BURST_INCR,
        .len = 1,
        .write = true,
        .read = false,
        .wuser = (uint32_t[]){AXI_DEFAULT_USER},
        .wdata = (uint32_t[]){value},
        .wstrb = (uint8_t[]){mask}
    });

    return axi_resp.resp;
}

uint8_t soc_write_user_32(uint32_t reg_addr, uint32_t value, uint32_t user) {
    axi_resp_t axi_resp;

    axi_resp = soc_access_32((axi_req_t){
        .addr = reg_addr,
        .axuser = user,
        .burst = AXI_BURST_INCR,
        .len = 1,
        .write = true,
        .read = false,
        .wuser = (uint32_t[]){user},
        .wdata = (uint32_t[]){value},
        .wstrb = (uint8_t[]){AXI_DEFAULT_MASK}
    });

    return axi_resp.resp;
}

uint8_t soc_write_32(uint32_t reg_addr, uint32_t value) {
    return soc_write_user_32(reg_addr, value, AXI_DEFAULT_USER);
}

axi_resp_t soc_read_user_32(uint32_t reg_addr, uint32_t user) {
    axi_resp_t axi_resp;

    axi_resp = soc_access_32((axi_req_t){
        .addr = reg_addr,
        .axuser = user,
        .burst = AXI_BURST_INCR,
        .len = 1,
        .write = false,
        .read = true
    });

    return axi_resp;
}

axi_resp_t soc_read_32(uint32_t reg_addr) {
    return soc_read_user_32(reg_addr, AXI_DEFAULT_USER);
}

void soc_write_addr(axi_req_t req) {
    if (!req.write) return;
    // Set AXI address
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.addr);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x017F);

    // Set AXI burst
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.burst);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x087F);

    // Set AXI aXuser
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.axuser);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x077F);

    // Send on AW channel
    uint32_t execute = AXI_WRITE_ADDR | AXI_USE_ID | ((req.len - 1) << 8) | (req.id << 16);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, execute);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x037F);
}

void soc_write_data(axi_req_t req) {
    if (!req.write) return;
    // Clear SoC access queues
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x0A7F);

    for (int i = 0; i < req.len; i++) {
        // Push AXI wdata
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.wdata ? req.wdata[i] : 0);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x027F);
        // Push AXI wuser
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.wuser ? req.wuser[i] : AXI_DEFAULT_USER);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x067F);
        // Push AXI wstrb
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.wstrb ? (req.wstrb[i] & 0xF) : 0xF);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x097F);
    }

    // Send on W channel
    uint32_t execute = AXI_WRITE_DATA | ((req.len - 1) << 8);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, execute);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x037F);
}

axi_resp_t soc_write_resp(axi_req_t req) {
    if (!req.write)
        return (axi_resp_t){ .resp = 0, .rdata = 0 };
    // Receive from B channel
    uint32_t execute = AXI_WRITE_RESP | AXI_USE_ID | (req.id << 16);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, execute);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x037F);
    while (1) {
        axi_resp_t axi_resp;

        // Check if AXI has finished
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x047F);
        axi_resp.resp = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);

        if(axi_resp.resp & 1) {
            axi_resp.resp = (axi_resp.resp >> 1) & 0b11;
            return axi_resp;
        }
    }
}

void soc_read_addr(axi_req_t req) {
    if (!req.read) return;
    // Set AXI address
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.addr);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x017F);

    // Set AXI burst
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.burst);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x087F);

    // Set AXI aXuser
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, req.axuser);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x077F);

    // Send on AR channel
    uint32_t execute = AXI_READ_ADDR | AXI_USE_ID | ((req.len - 1) << 8) | (req.id << 16);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, execute);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x037F);

}

axi_resp_t soc_read_resp(axi_req_t req) {
    if (!req.read)
        return (axi_resp_t){ .resp = 0, .rdata = 0 };
    // Receive from R channel
    uint32_t execute = AXI_READ_RESP | AXI_USE_ID | ((req.len - 1) << 8) |(req.id << 16);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_1, execute);
    lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x037F);

    while (1) {
        axi_resp_t axi_resp;

        // Check if AXI has finished
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x047F);
        axi_resp.resp = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);

        if(axi_resp.resp & 1) {
            axi_resp.resp = (axi_resp.resp >> 1) & 0b11;
            for (int i = 0; i < req.len; i++) {
                lsu_write_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_OUTPUT_WIRES_0, 0x057F);
                uint32_t rdata = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0);
                if (i == 0) axi_resp.rdata = rdata;
                if (req.rdata) req.rdata[i] = rdata;
            }
            return axi_resp;
        }
    }
}
