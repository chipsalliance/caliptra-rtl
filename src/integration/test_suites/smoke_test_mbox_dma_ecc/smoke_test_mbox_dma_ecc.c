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
#include "riscv-csr.h"
#include "veer-csr.h"
#include "riscv_hw_if.h"
#include <stdint.h>
#include "printf.h"
#include "soc_ifc.h"

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count = 0;
volatile uint32_t fail __attribute__((section(".dccm.persistent"))) = 0;
volatile caliptra_intr_received_s cptra_intr_rcv = {0};
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

enum tb_fifo_mode {
    RAND_DELAY_TOGGLE = 0x8f,
};

void nmi_handler() {
    VPRINTF(FATAL, "NMI");
}

void main(void) {
    uint32_t reg;
    uint32_t src_payload[17] = {
        0x01234567,
        0x89abcdef,
        0x0fedcba9,
        0x76543210,
        0xa5a5a5a5,
        0x5a5a5a5a,
        0xdeadbeef,
        0xfeedface,
        0x11111111,
        0x22222222,
        0x33333333,
        0x44444444,
        0x55555555,
        0x66666666,
        0x77777777,
        0x88888888,
        0x99999999,
    };
    uint32_t readback[17];
    uint32_t byte_count = 17 * 4;
    uint32_t mbox_offset = (MBOX_DIR_SPAN - 4) - (17 * 4);
    uint32_t ii;

    VPRINTF(LOW, "----------------------------------\nSmoke Test Mailbox DMA ECC !!\n----------------------------------\n");

    lsu_write_32((uintptr_t) (CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR), (uint32_t) (nmi_handler));

    // Match the DMA smoke test initialization so the DMA engine is in a known idle state.
    init_interrupts();
    reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
    lsu_write_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R,
                 reg & ~(AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_EMPTY_EN_MASK |
                         AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_EMPTY_EN_MASK |
                         AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_FULL_EN_MASK |
                         AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_FULL_EN_MASK));

    SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);

    VPRINTF(LOW, "Staging payload into AXI SRAM\n");
    soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR, 0, src_payload, byte_count, 0);

    VPRINTF(LOW, "Writing payload into mailbox SRAM\n");
    soc_ifc_axi_dma_read_mbox_payload(AXI_SRAM_BASE_ADDR, mbox_offset, 0, byte_count, 0);

    if (soc_ifc_mbox_acquire_lock(1)) {
        VPRINTF(ERROR, "Failed to reacquire mailbox lock for readback\n");
        fail = 1;
    }

    for (ii = 0; ii < 17; ii++) {
        readback[ii] = lsu_read_32(CLP_MBOX_SRAM_BASE_ADDR + mbox_offset + (ii << 2));
        if (readback[ii] != src_payload[ii]) {
            VPRINTF(ERROR, "Mailbox readback mismatch at word %u: got 0x%08x expected 0x%08x\n", ii, readback[ii], src_payload[ii]);
            fail = 1;
        }
    }

    reg = lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS);
    if (reg & MBOX_CSR_MBOX_STATUS_ECC_SINGLE_ERROR_MASK) {
        VPRINTF(ERROR, "Mailbox ECC single error bit asserted (0x%08x)\n", reg);
        fail = 1;
    }
    if (reg & MBOX_CSR_MBOX_STATUS_ECC_DOUBLE_ERROR_MASK) {
        VPRINTF(ERROR, "Mailbox ECC double error bit asserted (0x%08x)\n", reg);
        fail = 1;
    }

done:
    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

    if (fail) {
        SEND_STDOUT_CTRL(0x1);
        while (1);
    }

    SEND_STDOUT_CTRL(0xff);
    while (1);
}
