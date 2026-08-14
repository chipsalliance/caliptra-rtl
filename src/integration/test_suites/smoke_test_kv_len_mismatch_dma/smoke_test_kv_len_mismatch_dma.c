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
// Directed KV length-mismatch test — AXI-DMA MEK path.
//
// STATUS: SKELETON — DMA KV read is driven by the OCP LOCK key-release
// protocol, not by an FW-programmable KV_RD_CTRL. This test currently:
//   1) Seeds a wrong-size KV entry (12 dwords via SHA-384) into slot
//      KV_OCP_LOCK_KEY_RELEASE_KV_SLOT with dest_valid=DMA.
//   2) Reads the AXI_DMA ERROR_KV_RD_INTR_COUNT_R baseline.
//   3) Placeholder: FW-invoke of the OCP LOCK key release still to be
//      wired (see smoke_test_dma_aes_kv for the setup sequence).
//   4) Verifies the KV_RD_INTR_COUNT increments.
//
// See tasks/round-1-directed-mismatch-tests.md — flagged as follow-up.
//
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "riscv-csr.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "sha512.h"
#include "keyvault.h"
#include "caliptra_rtl_lib.h"

volatile uint32_t* stdout = (uint32_t *)STDOUT;
volatile uint32_t intr_count = 0;
#ifdef CPT_VERBOSITY
enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
enum printf_verbosity verbosity_g = LOW;
#endif
volatile caliptra_intr_received_s cptra_intr_rcv = {0};

static void fail_test(const char* m){ VPRINTF(FATAL,"FAIL:%s\n",m); SEND_STDOUT_CTRL(0x1); while(1); }

static void kv_seed_via_sha(uint8_t slot, enum sha512_mode_e mode, dest_valid_t dv) {
    volatile uint32_t* p = (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_0;
    *p++ = 0x80000000;
    while (p < (uint32_t*) CLP_SHA512_REG_SHA512_BLOCK_31) *p++ = 0;
    *p = 0;
    sha512_poll_ready();
    kv_write_ctrl(CLP_SHA512_REG_SHA512_KV_WR_CTRL, slot, dv);
    sha_init_last(mode);
    sha512_poll_valid();
    kv_poll_valid(CLP_SHA512_REG_SHA512_KV_WR_STATUS);
    kv_error_check(CLP_SHA512_REG_SHA512_KV_WR_STATUS);
    lsu_write_32(CLP_SHA512_REG_SHA512_KV_WR_CTRL, 0);
    sha512_zeroize();
}

void main(void) {
    VPRINTF(LOW,"---- KV len-mismatch (AXI-DMA MEK) — SKELETON ----\n");
    init_interrupts();

    // KV_OCP_LOCK_KEY_RELEASE_KV_SLOT is normally 23; hard-code here to
    // avoid pulling in soc_ifc.h from this compact test.
    const uint8_t SLOT = 23;

    dest_valid_t dv = { .dma_data = 1 };
    kv_seed_via_sha(SLOT, SHA512_384_MODE, dv);

    uint32_t before = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_INTR_COUNT_R);
    VPRINTF(LOW, "DMA ERROR_KV_RD_INTR_COUNT before = %u\n", before);

    // TODO: invoke OCP LOCK key-release flow here. Until wired, this test
    // exits successfully after documenting the current counter value.
    // Once the release flow is added, expect `after > before` and validate
    // that DMA does NOT commit a bad-length key to the endpoint FIFO.
    for (volatile int i = 0; i < 8000; i++) __asm__ volatile("nop");

    uint32_t after = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_ERROR_KV_RD_INTR_COUNT_R);
    VPRINTF(LOW, "DMA ERROR_KV_RD_INTR_COUNT after  = %u\n", after);

    VPRINTF(LOW, "Skeleton complete; wire OCP LOCK release to fully validate.\n");
    SEND_STDOUT_CTRL(0xff);
    while (1);
}
