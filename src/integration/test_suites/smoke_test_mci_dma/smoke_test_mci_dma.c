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
#include <string.h>
#include <stdint.h>
#include "printf.h"
#include "soc_ifc.h"

// FIXME should be from some macro
`define MCU_SRAM_SIZE_BYTES

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

void main(void) {
        int argc=0;
        char *argv[1];
        uint32_t reg;
        uint64_t mci_addr;
        uint64_t mcu_sram_addr;
        uint8_t fail = 0;
        uint32_t send_payload[16] = {
            0xabadface,
            0xba5eba11,
            0xcafebabe,
            0xdeadbeef,
            0xebbf1000,
            0xfadefee1,
            0x12344321,
            0xa5a5a5a5,
            0x14351375,
            0x8afdbe82,
            0xafb832ba,
            0x8843151a,
            0xbad831b1,
            0xf831ba83,
            0xad813451,
            0x67120ad3
        };
        uint32_t mbox_send_payload[16] = {
            0x0991c03c,
            0x7bc14838,
            0xb05f2c82,
            0x7b233274,
            0x01b7ba27,
            0x3f24db45,
            0xd945c472,
            0xabac3989,
            0x64af1d5e,
            0xda068da4,
            0xeb9102ab,
            0xf796de3e,
            0x88fc6af8,
            0x1a169287,
            0xc9a6e724,
            0x667f9dd5
        };
        uint32_t read_payload[16];
        uint32_t mbox_read_payload[16];

        VPRINTF(LOW, "----------------------------------\nSmoke Test AXI DMA -> MCI !!\n----------------------------------\n");

        // Setup the interrupt CSR configuration
        init_interrupts();
        reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
        lsu_write_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, reg & ~(AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_EMPTY_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_EMPTY_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_FULL_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_FULL_EN_MASK));

        // Get MCI addr from straps
        mci_addr = (uint64_t) ((lsu_read_32(CLP_SOC_IFC_REG_SS_MCI_BASE_ADDR_H) << 32) |
                               (lsu_read_32(CLP_SOC_IFC_REG_SS_MCI_BASE_ADDR_L)));
        mcu_sram_addr = mci_addr + 0x00200000; // FIXME magic number should be param

        // Send data through AHB interface to AXI_DMA, target the MCI
        VPRINTF(LOW, "Sending payload via AHB i/f\n");
        soc_ifc_axi_dma_send_ahb_payload(mcu_sram_addr, 0, send_payload, 16*4, 0);

        // Send data through Mailbox to AXI_DMA, target the MCI
        VPRINTF(LOW, "Writing payload to Mailbox via Direct Mode\n");
        // Acquire the mailbox lock
        if (soc_ifc_mbox_acquire_lock(1)) {
            VPRINTF(ERROR, "Acquire mailbox lock failed\n");
            fail = 1;
        }
        // Write data into mailbox using direct-mode
        for (uint32_t dw = 0; dw < 16; dw++) {
            lsu_write_32(CLP_MBOX_SRAM_BASE_ADDR + 0x4400 + (dw << 2), mbox_send_payload[dw]);
        }
        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
        VPRINTF(LOW, "Sending payload from Mailbox\n");
        if (soc_ifc_axi_dma_send_mbox_payload(0x4400, mcu_sram_addr + 16*4, 0, 16*4, 0)) {
            fail = 1;
        }

        // Move data from one address to another in MCI
        // Use the block-size feature
        VPRINTF(LOW, "Moving payload at SRAM via axi-to-axi xfer\n");
        soc_ifc_axi_dma_send_axi_to_axi(mcu_sram_addr, 0, mcu_sram_addr + MCU_SRAM_SIZE_BYTES/2, 0, 2*16*4, 16*2);

        // Read data back from MCI and confirm it matches
        VPRINTF(LOW, "Reading payload via AHB i/f\n");
        soc_ifc_axi_dma_read_ahb_payload(mcu_sram_addr + MCU_SRAM_SIZE_BYTES/2, 0, read_payload, 16*4, 0);
        for (uint8_t ii = 0; ii < 16; ii++) {
            if (read_payload[ii] != send_payload[ii]) {
                VPRINTF(ERROR, "read_payload[%d] (0x%x) does not match send_payload[%d] (0x%x)\n", ii, read_payload[ii], ii, send_payload[ii]);
                fail = 1;
            }
        }

        // Read data back through mailbox using direct-mode
        VPRINTF(LOW, "Reading payload to Mailbox\n");
        if (soc_ifc_axi_dma_read_mbox_payload(mcu_sram_addr + MCU_SRAM_SIZE_BYTES/2 + 16*4, 0x8800, 0, 16*4, 0)) {
            fail = 1;
        }
        VPRINTF(LOW, "Reading payload from Mailbox via Direct Mode\n");
        // Acquire the mailbox lock
        if (soc_ifc_mbox_acquire_lock(1)) {
            VPRINTF(ERROR, "Acquire mailbox lock failed\n");
            fail = 1;
        }
        for (uint32_t dw = 0; dw < 16; dw++) {
            mbox_read_payload[dw] = lsu_read_32(CLP_MBOX_SRAM_BASE_ADDR + 0x8800 + (dw << 2));
            if (mbox_read_payload[dw] != mbox_send_payload[dw]) {
                VPRINTF(ERROR, "mbox_read_payload[%d] (0x%x) does not match mbox_send_payload[%d] (0x%x)\n", dw, mbox_read_payload[dw], dw, mbox_send_payload[dw]);
                fail = 1;
            }
        }
        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);


        if (fail) {
            VPRINTF(FATAL, "smoke_test_mci_dma failed!\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
}
