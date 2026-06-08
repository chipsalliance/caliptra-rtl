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
#include <string.h>
#include "soc_access.h"
#include "soc_ifc.h"
#include "printf.h"

volatile uint32_t intr_count = 0;
volatile uint32_t *stdout = (uint32_t *)STDOUT;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = HIGH;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define FAIL(...) do { VPRINTF(ERROR, __VA_ARGS__); SEND_STDOUT_CTRL(0x1); for(;;); } while(0);


static void soc_release_sha_lock() {
    soc_write_32(CLP_SHA512_ACC_CSR_LOCK, SHA512_ACC_CSR_LOCK_LOCK_MASK);
}

static void soc_get_sha_lock() {
    // Make sure uC is not holding it
    lsu_write_32(CLP_SHA512_ACC_CSR_LOCK, SHA512_ACC_CSR_LOCK_LOCK_MASK);
    soc_release_sha_lock();

    for (int i = 0; i < 1000; i++)
        if (soc_read_32(CLP_SHA512_ACC_CSR_LOCK).rdata & SHA512_ACC_CSR_LOCK_LOCK_MASK)
            return;

    FAIL("Failed to acquire SHA lock from SoC after 1000 iterations!\n");
}


void main(void) {
    VPRINTF(LOW, "---------------------------------------\n");
    VPRINTF(LOW, " uC + SoC intf access collision Test!!\n" );
    VPRINTF(LOW, "---------------------------------------\n");

    // Case 1: Simultaneous uC + SoC collision in SHA regs while the SHA block buffer is stalled
    soc_get_sha_lock();

    soc_write_32(CLP_SHA512_ACC_CSR_MODE, SHA_STREAM_512);
    soc_write_32(CLP_SHA512_ACC_CSR_DLEN, 10000); // just has to be huge enough
    
    // Do a long DATAIN burst to initiate write stall mixed with read accesses
    soc_access_32((axi_req_t){
        .addr = CLP_SHA512_ACC_CSR_DATAIN,
        .burst = AXI_BURST_FIXED,
        .len = 128,
        .write = true,
        .read = true,
        .ignore_resp = true
    });

    // While the SoC is granted access, make uC do a collision
    for (int i = 0; i < 20; i++)
        lsu_write_32(CLP_SHA512_ACC_CSR_MODE, SHA_STREAM_512);

    if (soc_access_await_done())
        FAIL("SHA DATAIN long write burst failed!\n");

    soc_release_sha_lock();


    // Case 2: Simultaneous uC + SoC access collision in DMA regs
    soc_access_32((axi_req_t){
        .addr = CLP_AXI_DMA_REG_STATUS0,
        .burst = AXI_BURST_FIXED,
        .len = 128,
        .write = false,
        .read = true,
        .ignore_resp = true
    });

    for (int i = 0; i < 20; i++)
        lsu_read_32(CLP_AXI_DMA_REG_STATUS0);

    if (soc_access_await_done())
        FAIL("DMA reg long read burst failed!\n");
}
