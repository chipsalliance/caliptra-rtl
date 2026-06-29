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

#ifndef SOC_ACCESS_LIB
#define SOC_ACCESS_LIB

#include <stdbool.h>
#include "stdint.h"

typedef enum {
    AXI_BURST_FIXED = 0,
    AXI_BURST_INCR = 1,
    AXI_BURST_WRAP = 2
} axi_burst_t;

typedef struct {
    uint32_t  rdata;
    uint8_t   resp;
} axi_resp_t;

typedef struct {
    uint32_t addr, axuser;
    axi_burst_t burst;
    uint32_t *wdata, *wuser, *rdata;
    uint8_t *wstrb;
    uint8_t len;
    uint8_t id;
    bool write, read, ignore_resp, use_id;
} axi_req_t;

axi_resp_t soc_access_32(axi_req_t req);
uint8_t soc_access_await_done();
uint8_t soc_masked_write_32(uint32_t reg_addr, uint32_t value, uint32_t mask);
uint8_t soc_write_user_32(uint32_t reg_addr, uint32_t value, uint32_t user);
uint8_t soc_write_32(uint32_t reg_addr, uint32_t value);
axi_resp_t soc_read_user_32(uint32_t reg_addr, uint32_t user);
axi_resp_t soc_read_32(uint32_t reg_addr);
void       soc_write_addr(axi_req_t req);
void       soc_write_data(axi_req_t req);
axi_resp_t soc_write_resp(axi_req_t req);
void       soc_read_addr(axi_req_t req);
axi_resp_t soc_read_resp(axi_req_t req);

#endif /* SOC_ACCESS_LIB */
