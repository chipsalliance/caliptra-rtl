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
#include <stdlib.h>
#include "printf.h"
#include "soc_ifc.h"


volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
volatile uint32_t  rst_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t  fail      __attribute__((section(".dccm.persistent"))) = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#define MAX_FIFO_SIZE 1024
uint32_t rand_payload[MAX_FIFO_SIZE*2];

const enum tb_fifo_mode {
    RCVY_EMU_TOGGLE     = 0x88,
    FIFO_AUTO_READ_ON   = 0x8a,
    FIFO_AUTO_WRITE_ON  = 0x8b,
    FIFO_AUTO_READ_OFF  = 0x8c,
    FIFO_AUTO_WRITE_OFF = 0x8d,
    FIFO_CLEAR          = 0x8e,
    RAND_DELAY_TOGGLE   = 0x8f
};

enum err_inj_type {
//    cmd_inv_rd_route    ,
//    cmd_inv_wr_route    ,
    cmd_inv_route_combo ,
    cmd_inv_src_addr    ,
    cmd_inv_dst_addr    ,
    cmd_inv_byte_count  ,
    cmd_inv_block_size  ,
    cmd_inv_rd_fixed    ,
    cmd_inv_wr_fixed    ,
    cmd_inv_mbox_lock
//    cmd_inv_sha_lock
};

void nmi_handler() {
    VPRINTF(FATAL, "NMI");
}
uint8_t soc_ifc_axi_dma_inject_inv_error(enum err_inj_type err_type) {
    uint32_t reg;
    uint64_t src_addr;
    uint64_t dst_addr;
    uint32_t rd_route;
    uint32_t wr_route;
    uint8_t  rd_fixed;
    uint8_t  wr_fixed;
    uint32_t byte_count;
    uint16_t block_size;

    src_addr   = AXI_SRAM_BASE_ADDR + ((err_type == cmd_inv_src_addr) ? 0x3 : 0x0);
    dst_addr   = (err_type == cmd_inv_mbox_lock) ? 0x4000 : (AXI_SRAM_BASE_ADDR + 0x4000 + ((err_type == cmd_inv_dst_addr) ? 0x3 : 0x0));
    rd_route   = (err_type == cmd_inv_rd_fixed) ? axi_dma_rd_route_DISABLE : (err_type == cmd_inv_route_combo) ? axi_dma_rd_route_AHB_FIFO : (err_type == cmd_inv_mbox_lock) ? axi_dma_rd_route_MBOX    : axi_dma_rd_route_AXI_WR;
    wr_route   = (err_type == cmd_inv_wr_fixed) ? axi_dma_wr_route_DISABLE : (err_type == cmd_inv_route_combo) ? axi_dma_wr_route_AHB_FIFO : (err_type == cmd_inv_mbox_lock) ? axi_dma_wr_route_DISABLE : axi_dma_wr_route_AXI_RD;
    rd_fixed   = err_type == cmd_inv_rd_fixed;
    wr_fixed   = err_type == cmd_inv_wr_fixed;
    byte_count = (err_type == cmd_inv_byte_count) ? 0x43 : 0x40;
    block_size = (err_type == cmd_inv_block_size) ? 0x13 : 0x00;

    VPRINTF(HIGH, "param: src_addr   0x%x 0x%x\n", (uint32_t) (src_addr >> 32) , (uint32_t) (src_addr & 0xffffffff));
    VPRINTF(HIGH, "param: dst_addr   0x%x 0x%x\n", (uint32_t) (dst_addr >> 32) , (uint32_t) (dst_addr & 0xffffffff));
    VPRINTF(HIGH, "param: rd_route   0x%x\n"     , rd_route  );
    VPRINTF(HIGH, "param: wr_route   0x%x\n"     , wr_route  );
    VPRINTF(HIGH, "param: rd_fixed   0x%x\n"     , rd_fixed  );
    VPRINTF(HIGH, "param: wr_fixed   0x%x\n"     , wr_fixed  );
    VPRINTF(HIGH, "param: byte_count 0x%x\n"     , byte_count);
    VPRINTF(HIGH, "param: block_size 0x%x\n"     , block_size);

    // Disable txn_done interrupt since we'll poll it
    reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
    lsu_write_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, reg & ~AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_TXN_DONE_EN_MASK);

    // Arm the Error command
    while (lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_BUSY_MASK);
    VPRINTF(LOW, "FW: Arm err command\n");
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_L,  src_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_SRC_ADDR_H, (src_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_L,  dst_addr        & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_DST_ADDR_H, (dst_addr >> 32) & 0xffffffff);
    lsu_write_32(CLP_AXI_DMA_REG_BYTE_COUNT, byte_count);
    lsu_write_32(CLP_AXI_DMA_REG_BLOCK_SIZE, (uint32_t) block_size);
    reg = (AXI_DMA_REG_CTRL_GO_MASK)                      |
          (rd_route << AXI_DMA_REG_CTRL_RD_ROUTE_LOW)     |
          (wr_route << AXI_DMA_REG_CTRL_WR_ROUTE_LOW)     |
          (rd_fixed ? AXI_DMA_REG_CTRL_RD_FIXED_MASK : 0) |
          (wr_fixed ? AXI_DMA_REG_CTRL_WR_FIXED_MASK : 0);
    lsu_write_32(CLP_AXI_DMA_REG_CTRL, reg);

    // Check completion (error state expected)
    reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    VPRINTF(LOW, "FW: Poll DMA status\n");
    while ((reg & AXI_DMA_REG_STATUS0_BUSY_MASK) && !(reg & AXI_DMA_REG_STATUS0_ERROR_MASK)) {
        reg = lsu_read_32(CLP_AXI_DMA_REG_STATUS0);
    }

    // Check status
    VPRINTF(LOW, "FW: Check DMA status\n");
    if (reg & AXI_DMA_REG_STATUS0_ERROR_MASK) {
        VPRINTF(LOW, "AXI DMA reports err status for err injection xfer\n");
        lsu_write_32(CLP_AXI_DMA_REG_CTRL, AXI_DMA_REG_CTRL_FLUSH_MASK);
    } else {
        VPRINTF(ERROR, "ERROR: AXI DMA reports success status for err injection xfer!\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
        //return 1;
    }

    // Reenable txn_done interrupt
    reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
    lsu_write_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, reg | AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_TXN_DONE_EN_MASK);

    return 0;
}
void main(void) {
        int argc=0;
        char *argv[1];
        uint32_t reg;
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
        uint32_t fixed_send_payload[17] = {
            0x00000000,
            0x11111111,
            0x22222222,
            0x33333333,
            0x44444444,
            0x55555555,
            0x66666666,
            0x77777777,
            0x88888888,
            0x99999999,
            0xaaaaaaaa,
            0xbbbbbbbb,
            0xcccccccc,
            0xdddddddd,
            0xeeeeeeee,
            0xffffffff,
            0x234562ab
        };
        uint32_t post_rst_send_payload[16] = {
            0xC8F518D4,
            0xF3AA1BD4,
            0x6ED56C1C,
            0x3C9E16FB,
            0x5112DBBD,
            0x0AAE67FE,
            0xF26B465B,
            0xE935B48E,
            0x800AF504,
            0xDB988435,
            0x48C5F623,
            0xEE115F73,
            0xD4C62ABC,
            0x06D303B5,
            0xD90D9A17,
            0x5087290D
        };
        uint32_t read_payload[16];
        uint32_t mbox_read_payload[17];
        uint32_t fixed_read_payload[17];

        VPRINTF(LOW, "----------------------------------\nSmoke Test AXI DMA  !!\n----------------------------------\n");
        rst_count++;

        //set NMI vector
        lsu_write_32((uintptr_t) (CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR), (uint32_t) (nmi_handler));

        // Setup the interrupt CSR configuration
        init_interrupts();
        reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
        lsu_write_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, reg & ~(AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_EMPTY_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_EMPTY_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_FULL_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_FULL_EN_MASK));

        // Test each malformed command check
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_route_combo)) { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_src_addr   )) { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_dst_addr   )) { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_byte_count )) { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_block_size )) { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_rd_fixed   )) { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_wr_fixed   )) { fail = 1; }
        if (soc_ifc_axi_dma_inject_inv_error(cmd_inv_mbox_lock  )) { fail = 1; }

        // ===========================================================================
        // If reset was executed, try to run another simple DMA test to check for life
        // ===========================================================================
        if (rst_count == 2) {
            VPRINTF(LOW, "Observed reset! Running some short DMA tests for life\n");

            // ===========================================================================
            // Send data through AHB interface to AXI_DMA, target the AXI SRAM
            // ===========================================================================
            VPRINTF(LOW, "Sending payload via AHB i/f\n");
            soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR, 0, post_rst_send_payload, 16*4, 0);


            // ===========================================================================
            // Move data from one address to another in AXI SRAM
            // ===========================================================================
            VPRINTF(LOW, "Moving payload at SRAM via axi-to-axi xfer\n");
            soc_ifc_axi_dma_send_axi_to_axi(AXI_SRAM_BASE_ADDR, 0, AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, (16)*4, 0, 0, 0);

            // ===========================================================================
            // Read data back from AXI SRAM and confirm it matches
            // ===========================================================================
            VPRINTF(LOW, "Reading payload via AHB i/f\n");
            soc_ifc_axi_dma_read_ahb_payload(AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, read_payload, 16*4, 0);
            for (uint8_t ii = 0; ii < 16; ii++) {
                if (read_payload[ii] != post_rst_send_payload[ii]) {
                    VPRINTF(ERROR, "read_payload[%d] (0x%x) does not match post_rst_send_payload[%d] (0x%x)\n", ii, read_payload[ii], ii, post_rst_send_payload[ii]);
                    fail = 1;
                }
            }

        } else if (rst_count == 1) {

        if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_RESET_REASON) == SOC_IFC_REG_CPTRA_RESET_REASON_WARM_RESET_MASK) {
            VPRINTF(FATAL, "rst_count is still 1 after warm reset!\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);

        // ===========================================================================
        // Send data through AHB interface to AXI_DMA, target the AXI SRAM
        // ===========================================================================
        VPRINTF(LOW, "Sending payload via AHB i/f\n");
        soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR, 0, send_payload, 16*4, 0);


        // ===========================================================================
        // Send data through Mailbox to AXI_DMA, target the AXI SRAM
        // ===========================================================================
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
        if (soc_ifc_axi_dma_send_mbox_payload(0x4400, AXI_SRAM_BASE_ADDR + 16*4, 0, 16*4, 0)) {
            fail = 1;
        }


        // ===========================================================================
        // Send data through AHB interface to AXI_DMA, target the AXI SRAM
        // ===========================================================================
        // Use a FIXED transfer (only the final beat should be present at the target address)
        VPRINTF(LOW, "Sending fixed payload via AHB i/f\n");
        soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR + 2*16*4, 1, fixed_send_payload, 17*4, 0);


        // ===========================================================================
        // Move data from one address to another in AXI SRAM
        // ===========================================================================
        VPRINTF(LOW, "Moving payload at SRAM via axi-to-axi xfer\n");
        soc_ifc_axi_dma_send_axi_to_axi(AXI_SRAM_BASE_ADDR, 0, AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, (2*16+1)*4, 0, 0, 0);


        // ===========================================================================
        // Read data back from AXI SRAM and confirm it matches
        // ===========================================================================
        VPRINTF(LOW, "Reading payload via AHB i/f\n");
        soc_ifc_axi_dma_read_ahb_payload(AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, read_payload, 16*4, 0);
        for (uint8_t ii = 0; ii < 16; ii++) {
            if (read_payload[ii] != send_payload[ii]) {
                VPRINTF(ERROR, "read_payload[%d] (0x%x) does not match send_payload[%d] (0x%x)\n", ii, read_payload[ii], ii, send_payload[ii]);
                fail = 1;
            }
        }


        // ===========================================================================
        // Read data back through mailbox using direct-mode
        // ===========================================================================
        VPRINTF(LOW, "Reading payload to Mailbox\n");
        if (soc_ifc_axi_dma_read_mbox_payload(AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2 + 16*4, 0x8800, 0, 17*4, 0)) {
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
        mbox_read_payload[16] = lsu_read_32(CLP_MBOX_SRAM_BASE_ADDR + 0x8800 + (16 << 2));
        if (mbox_read_payload[16] != fixed_send_payload[16]) {
            VPRINTF(ERROR, "mbox_read_payload[%d] (0x%x) does not match fixed_send_payload[%d] (0x%x)\n", 16, mbox_read_payload[16], 16, fixed_send_payload[16]);
            fail = 1;
        }
        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);

        // ===========================================================================
        // FIFO test
        // ===========================================================================
        // Send data through AHB interface to AXI_DMA, target the AXI FIFO
        // Use a FIXED transfer
        VPRINTF(LOW, "Sending fixed payload to FIFO via AHB i/f\n");
        soc_ifc_axi_dma_send_ahb_payload(AXI_FIFO_BASE_ADDR, 1, fixed_send_payload, 17*4, 0);

        // Read data back from AXI FIFO and confirm it matches
        VPRINTF(LOW, "Reading fixed payload from FIFO via AHB i/f\n");
        soc_ifc_axi_dma_read_ahb_payload(AXI_FIFO_BASE_ADDR, 1, fixed_read_payload, 17*4, 0);
        for (uint8_t ii = 0; ii < 17; ii++) {
            if (fixed_read_payload[ii] != fixed_send_payload[ii]) {
                VPRINTF(ERROR, "fixed_read_payload[%d] (0x%x) does not match fixed_send_payload[%d] (0x%x)\n", ii, fixed_read_payload[ii], ii, fixed_send_payload[ii]);
                fail = 1;
            }
        }

        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);


        // ===========================================================================
        // Read rand FIFO data into mailbox
        // ===========================================================================
        // Set auto-write
        VPRINTF(LOW, "Enable FIFO to auto-write\n");
        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

        VPRINTF(LOW, "Reading rand payload to Mailbox\n");
        if (soc_ifc_axi_dma_read_mbox_payload(AXI_FIFO_BASE_ADDR, 0x0, 1, MAX_FIFO_SIZE*2, 0)) {
            fail = 1;
        }

        // Clear auto-write
        VPRINTF(LOW, "Disable FIFO to auto-write\n");
        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
        SEND_STDOUT_CTRL(FIFO_CLEAR);


        // ===========================================================================
        // Send rand data through Mailbox to AXI_DMA, target the AXI FIFO
        // ===========================================================================

        // Set auto-read
        VPRINTF(LOW, "Set FIFO to auto-read\n");
        SEND_STDOUT_CTRL(FIFO_AUTO_READ_ON);

        VPRINTF(LOW, "Sending payload from Mailbox\n");
        if (soc_ifc_axi_dma_send_mbox_payload(0, AXI_FIFO_BASE_ADDR, 1, MAX_FIFO_SIZE*2, 0)) {
            fail = 1;
        }

        // Clear auto-read
        VPRINTF(LOW, "Disable FIFO to auto-read\n");
        SEND_STDOUT_CTRL(FIFO_AUTO_READ_OFF);
        SEND_STDOUT_CTRL(FIFO_CLEAR);


        // ===========================================================================
        // Auto FIFO test
        // ===========================================================================

        // Set auto-read
        VPRINTF(LOW, "Set FIFO to auto-read\n");
        SEND_STDOUT_CTRL(FIFO_AUTO_READ_ON);

        // Generate rand data
        srand(17);
        for (uint32_t ii = 0; ii < (MAX_FIFO_SIZE/2); ii++) {
            rand_payload[ii] = rand();
            if ((ii & 0x7f) == 0x40) putchar('.');
        }
        putchar('\n');

        // Send data through AHB interface to AXI_DMA, target the AXI FIFO
        // Use a FIXED transfer
        // Use total byte-count that is 2x FIFO depth
        VPRINTF(LOW, "Sending large rand payload to FIFO via AHB i/f\n");
        soc_ifc_axi_dma_send_ahb_payload(AXI_FIFO_BASE_ADDR, 1, rand_payload, MAX_FIFO_SIZE*2, 0);

        // Clear auto-read
        VPRINTF(LOW, "Disable FIFO to auto-read\n");
        SEND_STDOUT_CTRL(FIFO_AUTO_READ_OFF);
        SEND_STDOUT_CTRL(FIFO_CLEAR);
        // Set auto-write
        VPRINTF(LOW, "Enable FIFO to auto-write\n");
        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

        // Read data from AXI FIFO
        VPRINTF(LOW, "Reading large payload from FIFO via AHB i/f\n");
        soc_ifc_axi_dma_read_ahb_payload(AXI_FIFO_BASE_ADDR, 1, rand_payload, MAX_FIFO_SIZE*2, 0);

        // Clear auto-write
        VPRINTF(LOW, "Disable FIFO to auto-write\n");
        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
        SEND_STDOUT_CTRL(FIFO_CLEAR);


        // ===========================================================================
        // Block Size test - AXItoMBOX Read
        // ===========================================================================
        VPRINTF(LOW, "Reading FIFO payload to Mailbox with block_size feature\n");
        if (soc_ifc_axi_dma_read_mbox_payload_no_wait(AXI_FIFO_BASE_ADDR, 0x0, 1, 0x415C, 256)) {
            fail = 1;
        }

        // Set auto-write
        VPRINTF(LOW, "Enable FIFO to auto-write and enable recovery-mode emulation\n");
        SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

        soc_ifc_axi_dma_wait_idle (1);

        VPRINTF(LOW, "Disable FIFO to auto-write\n");
        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
        SEND_STDOUT_CTRL(FIFO_CLEAR);
        SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);

        // Set auto-write and enable recovery emulation _before_ arming DMA
        VPRINTF(LOW, "Enable FIFO to auto-write and enable recovery-mode emulation\n");
        VPRINTF(LOW, "Reading FIFO payload to Mailbox with block_size feature\n");
        SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

        if (soc_ifc_axi_dma_read_mbox_payload_no_wait(AXI_FIFO_BASE_ADDR, 0x0, 1, 0x415C, 256)) {
            fail = 1;
        }

        soc_ifc_axi_dma_wait_idle (1);

        VPRINTF(LOW, "Disable FIFO to auto-write\n");
        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
        SEND_STDOUT_CTRL(FIFO_CLEAR);
        SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);


        // ===========================================================================
        // Move data in AXI SRAM using same src/dst addr, rand delays
        // ===========================================================================
        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);

        VPRINTF(LOW, "Moving payload within SRAM via axi-to-axi xfer\n");
        soc_ifc_axi_dma_send_axi_to_axi(AXI_SRAM_BASE_ADDR, 0, AXI_SRAM_BASE_ADDR, 0, (2*16+1)*4, 0, 0, 0);

        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);


        // ===========================================================================
        // Move data in AXI SRAM using dst_addr == src_addr + 256B, rand delays
        // ===========================================================================
        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);

        VPRINTF(LOW, "Moving payload at SRAM via axi-to-axi xfer; R/W non-determinism is expected!\n");
        soc_ifc_axi_dma_send_axi_to_axi(AXI_SRAM_BASE_ADDR, 0, AXI_SRAM_BASE_ADDR + 256, 0, (137)*4, 0, 0, 0); // arbitrary number > 512, i.e. more than 2 AXI transactions

        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);


        // ===========================================================================
        // Auto FIFO test with very large transfer and random RESET
        // ===========================================================================

        // Set auto-write
        VPRINTF(LOW, "Enable FIFO to auto-write\n");
        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

        // Read data from AXI FIFO
        VPRINTF(LOW, "Request random reset and read large payload from FIFO to Mailbox\n");
        SEND_STDOUT_CTRL(0xee);
        soc_ifc_axi_dma_read_mbox_payload(AXI_FIFO_BASE_ADDR, 0x0, 1, MAX_FIFO_SIZE*32, 0);

        // Clear auto-write
        // This shouldn't execute - the reset will clear the FIFO and auto-write flag
        VPRINTF(LOW, "Disable FIFO to auto-write\n");
        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
        SEND_STDOUT_CTRL(FIFO_CLEAR);

        }


        // ===========================================================================
        // Ending Status
        // ===========================================================================
        if (fail) {
            VPRINTF(FATAL, "smoke_test_dma failed!\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
}
