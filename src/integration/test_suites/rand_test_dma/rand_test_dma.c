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

// NOTE: Testbench pre-loads AXI SRAM with random data

#include "defines.h"
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

// Transfer types
typedef enum {
    AHB2AXI,
    MBOX2AXI,
    AXI2AXI,
    AXI2MBOX,
    AXI2AHB
} transfer_type_t;

#define MAX_TRANSFER_SIZE = 100

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
volatile uint32_t rst_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t num_transfers __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t dccm_addr __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t next_transfer_dccm_addr __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t payload_start_addr __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t payload_end_addr __attribute__((section(".dccm.persistent"))) = 0;
volatile transfer_type_t transfer_type __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t transfer_size __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t dma_control __attribute__((section(".dccm.persistent"))) = 0;
volatile uint8_t mbox_locked __attribute__((section(".dccm.persistent"))) = 0;
volatile uint8_t data_check __attribute__((section(".dccm.persistent"))) = 0;
volatile uint8_t src_is_fifo __attribute__((section(".dccm.persistent"))) = 0;
volatile uint8_t dst_is_fifo __attribute__((section(".dccm.persistent"))) = 0;
volatile uint8_t use_rd_fixed __attribute__((section(".dccm.persistent"))) = 0;
volatile uint8_t use_wr_fixed __attribute__((section(".dccm.persistent"))) = 0;
volatile uint8_t inject_rand_delays __attribute__((section(".dccm.persistent"))) = 0;
volatile uint8_t inject_rst __attribute__((section(".dccm.persistent"))) = 0;
volatile uint8_t rst_done __attribute__((section(".dccm.persistent"))) = 0;
volatile uint8_t test_block_size __attribute__((section(".dccm.persistent"))) = 0;
volatile uint8_t dma_xfer_type __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t src_offset __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t dst_offset __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t block_size __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t curr_transfer __attribute__((section(".dccm.persistent"))) = 0;

//volatile uint8_t dma_trasnfer_done[MAX_TRANSFER_ELEMENTS] __attribute__((section(".dccm.persistent"))) = {0};

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#ifndef MY_RANDOM_SEED
#define MY_RANDOM_SEED 17
#endif // MY_RANDOM_SEED

#define MAX_PAYLOAD_SIZE_TO_CHECK_DW 16384 //16K dwords

// Request random reset. Can also be used to request the TB to wait for some random time before issuing a warm reset
#define RAND_RST 0xee

// Transfer type is in bits 0-2
#define DMA_XFER_TYPE_POS        0
#define DMA_XFER_TYPE_WIDTH      3

// Other fields
#define TEST_BLOCK_SIZE_POS      3
#define INJECT_RST_POS           4
#define INJECT_RAND_DELAYS_POS   5
#define USE_WR_FIXED_POS         6
#define USE_RD_FIXED_POS         7
#define DST_IS_FIFO_POS          8
#define SRC_IS_FIFO_POS          9

#define WRM_RST_BIT_POS          1

// Block Size is in bits 10-21
#define DMA_BLOCK_SIZE_POS        10
#define DMA_BLOCK_SIZE_WIDTH      12


// Bit masks
#define DMA_XFER_TYPE_MASK       (((1 << DMA_XFER_TYPE_WIDTH) - 1) << DMA_XFER_TYPE_POS)
#define TEST_BLOCK_SIZE_MASK     (1 << TEST_BLOCK_SIZE_POS)
#define INJECT_RST_MASK          (1 << INJECT_RST_POS)
#define INJECT_RAND_DELAYS_MASK  (1 << INJECT_RAND_DELAYS_POS)
#define USE_WR_FIXED_MASK        (1 << USE_WR_FIXED_POS)
#define USE_RD_FIXED_MASK        (1 << USE_RD_FIXED_POS)
#define DST_IS_FIFO_MASK         (1 << DST_IS_FIFO_POS)
#define SRC_IS_FIFO_MASK         (1 << SRC_IS_FIFO_POS)
#define DMA_BLOCK_SIZE_MASK      (((1 << DMA_BLOCK_SIZE_WIDTH) - 1) << DMA_BLOCK_SIZE_POS)
#define WARM_RESET_MASK          (1 << WRM_RST_BIT_POS)

// Global declaration of arrays
static uint32_t read_payload[MAX_PAYLOAD_SIZE_TO_CHECK_DW];

// Convert enum value to string
const char* transfer_type_to_string(transfer_type_t transfer_type) {
    switch (transfer_type) {
        case AHB2AXI: return "AHB2AXI";
        case MBOX2AXI: return "MBOX2AXI";
        case AXI2AXI: return "AXI2AXI";
        case AXI2MBOX: return "AXI2MBOX";
        case AXI2AHB: return "AXI2AHB";
        default: return "UNKNOWN";
    }
}

const enum tb_fifo_mode {
    RCVY_EMU_TOGGLE     = 0x88,
    FIFO_AUTO_READ_ON   = 0x8a, // Should be set while the fifo is empty. 
                                // When pushing data to the fifo, it will automatically empty itself (with random speed).
                                // If set, this must be cleared using the off flag below before changing the auto_write flag.
                                // If set, should be cleared before FIFO_CLEAR.
    FIFO_AUTO_WRITE_ON  = 0x8b, // FIFO_CLEAR should be used before setting AUTO_WRITE_ON
                                // If set, this must be cleared with "OFF" before using the FIFO_CLEAR
    FIFO_AUTO_READ_OFF  = 0x8c, // Clear the fifo auto-read feature. Do this after every test that sets it.
    FIFO_AUTO_WRITE_OFF = 0x8d, // Clear the auto-write feature. Should be done after every test that sets it.
                                // MUST be followed by a FIFO_CLEAR (i.e. , disable auto-write then fifo_clear)
    FIFO_CLEAR          = 0x8e, // Generates a pulse and auto-clears itself. Write once to generate the fifo_clear pulse.
    RAND_DELAY_TOGGLE   = 0x8f  // Toggle random delays on the axi_sub. Applies to both. 
};

void main(void) {
        int argc=0;
        char *argv[1];
        uint32_t reg;
        uint8_t fail = 0;
        uint32_t *dccm_data;
        uint32_t mbox_data;
        uint32_t ahb_rdata;
        uint32_t ahb_wdata = 0xc001c0de;

        uint64_t src_addr, dst_addr;

        VPRINTF(LOW, "----------------------------------\nRand Test AXI DMA  !!\n----------------------------------\n");
        rst_count++;

        // Setup the interrupt CSR configuration
        init_interrupts();
        reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
        lsu_write_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, reg & ~(AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_EMPTY_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_EMPTY_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_FULL_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_FULL_EN_MASK));

        // Test each malformed command check
        // TODO

        // ===========================================================================
        // If reset was executed, read some status registers for sign of life
        // ===========================================================================
        if (rst_count > 1) {
            // Set rst_done = 1 so that reset is not injected again for the same test
            rst_done = 1;

            VPRINTF(LOW, "Observed reset! Reading status registers for sign of life\n");
            //TODO: Read RESET_REASON register
            uint32_t reset_reason = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_RESET_REASON) & WARM_RESET_MASK;
            if (reset_reason == 0x2) {
                VPRINTF(LOW, "Reset Reason: Warm reset\n");
            }
        }


        // Read DCCM to determine number of transfers
        num_transfers = lsu_read_32(RV_DCCM_EADR - 3);
        VPRINTF(LOW, "Number of transfers: %d\n\n", num_transfers);

        // Read transfer type and size for each transfer and perform the transfer
        dccm_addr = RV_DCCM_EADR - 7;

        for (int i = curr_transfer; i < num_transfers; i++) {
            // Keep track of transfer number so transfer can resume after reset
            curr_transfer = i; 

            VPRINTF(LOW, "TRANSFER #%d\n", i);
            // Read control word that includes transfer type and other control information for DMA transfer
            
            if (next_transfer_dccm_addr != 0) { 
                dccm_addr = next_transfer_dccm_addr;
            }
            VPRINTF(HIGH, "dccm_addr = 0x%0x", dccm_addr);
            dma_control = lsu_read_32(dccm_addr);
            
            // Extract fields
            src_is_fifo = (dma_control & SRC_IS_FIFO_MASK) ? 1 : 0;
            dst_is_fifo = (dma_control & DST_IS_FIFO_MASK) ? 1 : 0;
            use_rd_fixed = (dma_control & USE_RD_FIXED_MASK) ? 1 : 0;
            use_wr_fixed = (dma_control & USE_WR_FIXED_MASK) ? 1 : 0;
            inject_rand_delays = (dma_control & INJECT_RAND_DELAYS_MASK) ? 1 : 0;
            inject_rst = (dma_control & INJECT_RST_MASK) ? 1 : 0;
            test_block_size = (dma_control & TEST_BLOCK_SIZE_MASK) ? 1 : 0;
            dma_xfer_type = (dma_control & DMA_XFER_TYPE_MASK) >> DMA_XFER_TYPE_POS;
            block_size = test_block_size ? ((dma_control & DMA_BLOCK_SIZE_MASK) >> DMA_BLOCK_SIZE_POS) : 0;
            VPRINTF(HIGH,   "Raw dma_control: 0x%08x\n", dma_control);
            VPRINTF(ALL,    "DMA_XFER_TYPE_MASK: 0x%08x\n", DMA_XFER_TYPE_MASK);
            VPRINTF(HIGH,   "Masked value: 0x%08x\n", dma_control & DMA_XFER_TYPE_MASK);
            VPRINTF(MEDIUM, "Extracted dma_xfer_type value: %d (0x%x)\n", dma_xfer_type, dma_xfer_type);
            VPRINTF(LOW,    "Transfer type: %s\n", transfer_type_to_string((transfer_type_t)dma_xfer_type));
            VPRINTF(MEDIUM, "Block Size: %d\n", block_size);
            VPRINTF(LOW,    "Src is FIFO: %s\n", src_is_fifo ? "Yes" : "No");
            VPRINTF(LOW,    "Dst is FIFO: %s\n", dst_is_fifo ? "Yes" : "No");
            VPRINTF(LOW,    "Use Rd Fixed: %s\n", use_rd_fixed ? "Yes" : "No");
            VPRINTF(LOW,    "Use Wr Fixed: %s\n", use_wr_fixed ? "Yes" : "No");
            VPRINTF(MEDIUM, "Inject Rand Delays: %s\n", inject_rand_delays ? "Yes" : "No");
            VPRINTF(MEDIUM, "Inject Rst: %s\n", inject_rst ? "Yes" : "No");
            VPRINTF(LOW,    "Test Block Size: %s\n", test_block_size ? "Yes" : "No");


            // Read transfer size
            dccm_addr = dccm_addr - 4;
            transfer_size = lsu_read_32(dccm_addr);

            // Validate transfer size to prevent buffer overflow
            if (transfer_size <= MAX_PAYLOAD_SIZE_TO_CHECK_DW) {
                data_check = 1;
            }
            else {
                data_check = 0;
            }
            VPRINTF(LOW, "Transfer size: %d dwords\n", transfer_size);

            // Read source offset
            dccm_addr = dccm_addr - 4;
            src_offset = lsu_read_32(dccm_addr);
            src_addr = (uint64_t) src_offset + 
                       ((dma_xfer_type == MBOX2AXI) ? (uint64_t) CLP_MBOX_SRAM_BASE_ADDR :
                                        src_is_fifo ? (uint64_t) AXI_FIFO_BASE_ADDR :
                                                      (uint64_t) AXI_SRAM_BASE_ADDR);
            VPRINTF(LOW, "Source Offset = 0x%0x\n", src_offset);

            // Read destination offset
            dccm_addr = dccm_addr - 4;
            dst_offset = lsu_read_32(dccm_addr);
            dst_addr = (uint64_t) dst_offset + 
                       ((dma_xfer_type == AXI2MBOX) ? (uint64_t) CLP_MBOX_SRAM_BASE_ADDR :
                                        dst_is_fifo ? (uint64_t) AXI_FIFO_BASE_ADDR :
                                                      (uint64_t) AXI_SRAM_BASE_ADDR);
            VPRINTF(LOW, "Destination Offset = 0x%0x\n", dst_offset);
            
            // Calculate starting address of payload data
            if (data_check) {
                payload_end_addr = dccm_addr - 4;  // First payload word is 4 bytes after transfer_size
                payload_start_addr = payload_end_addr - ((transfer_size - 1) * 4);  // Last word of payload (lowest address)
            } else {
                payload_end_addr = dccm_addr;  // No payload, point to the last member of testcase (dst offset)
                payload_start_addr = payload_end_addr;
            }
        
            VPRINTF(LOW,    "Payload DCCM Start Address = 0x%0x\n", payload_start_addr);
            VPRINTF(MEDIUM, "Payload DCCM End Address = 0x%0x\n", payload_end_addr);

            switch ((transfer_type_t)dma_xfer_type) {
                
                case AHB2AXI:
                    // Inject random delay
                    if (inject_rand_delays) {
                        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);
                    }

                    if (data_check) {
                        VPRINTF(MEDIUM, "Sending payload via AHB i/f\n");

                        if (inject_rst && (rst_done == 0)) {
                            VPRINTF(LOW, "Request random reset");
                            SEND_STDOUT_CTRL(RAND_RST);
                        }

                        soc_ifc_axi_dma_send_ahb_payload(dst_addr, use_wr_fixed, (uint32_t*)payload_start_addr, transfer_size*4, 0);
                    } else {
                        if (inject_rst && (rst_done == 0)) {
                            VPRINTF(LOW, "Request random reset");
                            SEND_STDOUT_CTRL(RAND_RST);
                        }
                        if (!dst_is_fifo) {
                            for (uint32_t dw = 0; dw < transfer_size; dw++) {
                                soc_ifc_axi_dma_send_ahb_payload(dst_addr, use_wr_fixed, &ahb_wdata, 4, 0);
                            }
                        } else {
                            // Set auto-read
                            VPRINTF(LOW, "Set FIFO to auto-read\n");
                            SEND_STDOUT_CTRL(FIFO_AUTO_READ_ON);

                            VPRINTF(LOW, "Sending payload from AHB\n");
                            for (uint32_t dw = 0; dw < transfer_size; dw++) {
                                soc_ifc_axi_dma_send_ahb_payload(dst_addr, use_wr_fixed, &ahb_wdata, 4, 0);
                            }

                            // Clear auto-read
                            VPRINTF(LOW, "Disable FIFO to auto-read\n");
                            SEND_STDOUT_CTRL(FIFO_AUTO_READ_OFF);
                            SEND_STDOUT_CTRL(FIFO_CLEAR);
                        }
                    }

                    if (inject_rand_delays) {
                        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);
                    }

                    if (data_check) {
                        //Read back via AHB and compare data
                        // AXI2AHB: Read data back from AXI SRAM and confirm it matches
                        VPRINTF(MEDIUM, "Reading payload via AHB i/f\n");

                        // Use the same 'fixed' value that was used to send data
                        soc_ifc_axi_dma_read_ahb_payload(dst_addr, use_wr_fixed, read_payload, transfer_size*4, 0);

                        // Compare read_payload data with original dccm_data
                        dccm_data = (uint32_t*) payload_start_addr;
                        for (uint32_t dw = 0; dw < transfer_size; dw++) {
                            if (use_wr_fixed && !dst_is_fifo && read_payload[dw] != lsu_read_32(payload_end_addr)) {
                                VPRINTF(ERROR, "read_payload[%d] (0x%08x) does not match lsu_read_32(payload_end_addr) (0x%08x)\n", dw, read_payload[dw], lsu_read_32(payload_end_addr));
                                fail = 1;
                            }
                            else if ((!use_wr_fixed || dst_is_fifo) && read_payload[dw] != dccm_data[dw]) {
                                VPRINTF(ERROR, "read_payload[%d] (0x%08x) does not match dccm_data[%d] (0x%08x)\n", dw, read_payload[dw], dw, dccm_data[dw]);
                                fail = 1;
                            }
                        }
                        if (!fail) {
                            VPRINTF(HIGH, "AHB2AXI: Read-back data matches sent data\n");
                        }
                    } 
                    break;
                
                case MBOX2AXI:
                    // Send data through Mailbox to AXI_DMA, target the AXI SRAM
                    VPRINTF(MEDIUM, "Writing payload to Mailbox via Direct Mode\n");

                    if (data_check) {
                        // Acquire the mailbox lock
                        soc_ifc_mbox_acquire_lock(1);
                        mbox_locked = 1;

                        // Source = dccm address
                        // Destination = mailbox memory
                        uint32_t* dccm_ptr = (uint32_t*)payload_start_addr;

                        // MBOX2AXI: Write data into mailbox using direct-mode
                        for (uint32_t dw = 0; dw < transfer_size; dw++) {
                            lsu_write_32((uint32_t) src_addr + (dw << 2), dccm_ptr[dw]);
                        }

                        // Relese mailbox lock
                        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
                        mbox_locked = 0;
                    } else {
                        VPRINTF(MEDIUM, "Large transfer - auto-write FIFO --> MBOX --> auto-read FIFO\n");
                        VPRINTF(MEDIUM, "Set FIFO to auto-write\n");
                        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

                        VPRINTF(LOW, "Reading rand payload to Mailbox\n");
                        if (soc_ifc_axi_dma_read_mbox_payload(AXI_FIFO_BASE_ADDR, 0x0, 1, AXI_FIFO_SIZE_BYTES*2, 0)) {
                            fail = 1;
                        }

                        // Clear auto-write
                        VPRINTF(LOW, "Disable FIFO to auto-write\n");
                        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
                        SEND_STDOUT_CTRL(FIFO_CLEAR);
                    }

                    // Inject random delay
                    if (inject_rand_delays) {
                        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);
                    }

                    if (data_check) {
                        VPRINTF(HIGH, "Sending payload from Mailbox\n");

                        if (inject_rst && (rst_done==0)) {
                            VPRINTF(LOW, "Request random reset");
                            SEND_STDOUT_CTRL(RAND_RST);
                        }

                        soc_ifc_axi_dma_send_mbox_payload(src_offset, dst_addr, use_wr_fixed, transfer_size*4, 0);
                    } else {
                        VPRINTF(HIGH, "Sending large payload from Mailbox\n");

                        if (inject_rst && (rst_done==0)) {
                            VPRINTF(LOW, "Request random reset");
                            SEND_STDOUT_CTRL(RAND_RST);
                        }
                        if (!dst_is_fifo) {
                            soc_ifc_axi_dma_send_mbox_payload(src_offset, dst_addr, use_wr_fixed, transfer_size*4, 0);
                        }
                        else {
                            // Set auto-read
                            VPRINTF(LOW, "Set FIFO to auto-read\n");
                            SEND_STDOUT_CTRL(FIFO_AUTO_READ_ON);

                            VPRINTF(LOW, "Sending payload from Mailbox\n");
                            soc_ifc_axi_dma_send_mbox_payload(src_offset, AXI_FIFO_BASE_ADDR, use_wr_fixed, transfer_size*4, 0);

                            // Clear auto-read
                            VPRINTF(LOW, "Disable FIFO to auto-read\n");
                            SEND_STDOUT_CTRL(FIFO_AUTO_READ_OFF);
                            SEND_STDOUT_CTRL(FIFO_CLEAR);
                        }
                    }

                    if (inject_rand_delays) {
                        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);
                    }
                    
                    if (data_check) {
                        //Read back via AHB and compare data
                        // AXI2AHB: Read data back from AXI SRAM and confirm it matches
                        VPRINTF(HIGH, "Reading payload via AHB i/f\n");
                        soc_ifc_axi_dma_read_ahb_payload(dst_addr, use_wr_fixed, read_payload, transfer_size*4, 0);

                        // Compare read_payload data with original dccm_data
                        dccm_data = (uint32_t*) payload_start_addr;
                        for (uint32_t dw = 0; dw < transfer_size; dw++) {
                            if (use_wr_fixed && !dst_is_fifo && read_payload[dw] != lsu_read_32(payload_end_addr)) {
                                VPRINTF(ERROR, "read_payload[%d] (0x%08x) does not match lsu_read_32(payload_end_addr) (0x%08x)\n", dw, read_payload[dw], lsu_read_32(payload_end_addr));
                                fail = 1;
                            }
                            else if ((!use_wr_fixed || dst_is_fifo) && read_payload[dw] != dccm_data[dw]) {
                                VPRINTF(ERROR, "read_payload[%d] (0x%08x) does not match dccmdccm_data_data[%d] (0x%08x)\n", dw, read_payload[dw], dw, dccm_data[dw]);
                                fail = 1;
                            }
                        }
                        if (!fail) {
                            VPRINTF(HIGH, "MBOX2AXI: Read-back data matches sent data\n");
                        }
                    }

                    break;
                
                case AXI2AXI:
                    if (test_block_size) {
                        VPRINTF(HIGH, "Enable recovery mode emulation");
                        SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
                    }

                    if (data_check) {
                        // Populate AXI source via AHB2AXI transfer
                        VPRINTF(MEDIUM, "Sending payload via AHB i/f\n");
                        soc_ifc_axi_dma_send_ahb_payload(src_addr, use_rd_fixed, (uint32_t*)payload_start_addr, transfer_size*4, 0);
                        if (test_block_size && src_is_fifo) {
                            uint32_t tmp[block_size]; // Push in an extra "block_size" of data; in the pulse TB mode, fifo must be full before recovery_data_avail is set
                            soc_ifc_axi_dma_send_ahb_payload(src_addr, use_rd_fixed, tmp, block_size, 0);
                        }
                    } else {
                        VPRINTF(MEDIUM, "Large transfer\n");
                        

                        if (src_is_fifo) { 
                            VPRINTF(MEDIUM, "Set FIFO to auto-write\n");
                            SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

                            // Transfer FIFO --> AXI  SRAM
                            VPRINTF(HIGH, "Moving large payload from FIFO to SRAM\n");
                            soc_ifc_axi_dma_send_axi_to_axi(AXI_FIFO_BASE_ADDR, use_rd_fixed, src_addr, use_wr_fixed, transfer_size*4, 0);

                            // Clear auto-write
                            VPRINTF(LOW, "Disable FIFO to auto-write\n");
                            SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
                            SEND_STDOUT_CTRL(FIFO_CLEAR);
                        } else {
                            VPRINTF(LOW, "Data pre-loaded into SRAM will be transferred to destination") ;
                        }
                    }

                    if (inject_rand_delays) {
                        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);
                    }

                    // Test AXI2AXI
                    if (data_check) {
                        VPRINTF(HIGH, "Moving payload at SRAM via axi-to-axi xfer\n");
                        
                        if (inject_rst && (rst_done==0)) {
                            VPRINTF(LOW, "Request random reset");
                            SEND_STDOUT_CTRL(RAND_RST);
                        }

                        soc_ifc_axi_dma_send_axi_to_axi_no_wait(src_addr, use_rd_fixed, dst_addr, use_wr_fixed, (transfer_size)*4, block_size); // block_size to be updated with random value based on parameters
                        soc_ifc_axi_dma_wait_idle(0);
                        if (test_block_size) {
                            SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
                        }
                    } else {
                        VPRINTF(HIGH, "Moving large from FIFO via axi-to-axi xfer\n");

                        if (inject_rst && (rst_done==0)) {
                            VPRINTF(LOW, "Request random reset");
                            SEND_STDOUT_CTRL(RAND_RST);
                        }

                        if (!dst_is_fifo) {
                            soc_ifc_axi_dma_send_axi_to_axi_no_wait(src_addr, use_rd_fixed, dst_addr, use_wr_fixed, (transfer_size)*4, block_size);
                            soc_ifc_axi_dma_wait_idle(0);
                            if (test_block_size) {
                                SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
                            }
                        }
                        else {
                            VPRINTF(MEDIUM, "Set FIFO to auto-read\n");
                            SEND_STDOUT_CTRL(FIFO_AUTO_READ_ON);

                            // Transfer SRAM --> FIFO
                            VPRINTF(HIGH, "Moving large payload from SRAM to FIFO\n");
                            soc_ifc_axi_dma_send_axi_to_axi_no_wait(src_addr, use_rd_fixed, dst_addr, use_wr_fixed, transfer_size*4, block_size);
                            soc_ifc_axi_dma_wait_idle(0);
                            if (test_block_size) {
                                SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
                            }

                            // Clear auto-read
                            VPRINTF(LOW, "Disable FIFO to auto-write\n");
                            SEND_STDOUT_CTRL(FIFO_AUTO_READ_OFF);
                            SEND_STDOUT_CTRL(FIFO_CLEAR);
                        }
                    }
                    if (inject_rand_delays) {
                        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);
                    }

                    if (data_check) {
                        //Read back via AHB and compare data
                        // AXI2AHB: Read data back from AXI SRAM and confirm it matches
                        VPRINTF(HIGH, "Reading payload via AHB i/f\n");
                        soc_ifc_axi_dma_read_ahb_payload(dst_addr, use_wr_fixed, read_payload, transfer_size*4, 0);

                        // Compare read_payload data with original dccm_data
                        dccm_data = (uint32_t*) payload_start_addr;
                        for (uint32_t dw = 0; dw < transfer_size; dw++) {
                            if (((use_rd_fixed && !src_is_fifo) || (use_wr_fixed && !dst_is_fifo)) && (read_payload[dw] != lsu_read_32(payload_end_addr))) {
                                VPRINTF(ERROR, "read_payload[%d] (0x%08x) does not match lsu_read_32(payload_end_addr) (0x%08x)\n", dw, read_payload[dw], lsu_read_32(payload_end_addr));
                                fail = 1;
                            }
                            else if ((!use_rd_fixed || src_is_fifo) && (!use_wr_fixed || dst_is_fifo) && read_payload[dw] != dccm_data[dw]) {
                                VPRINTF(ERROR, "read_payload[%d] (0x%08x) does not match dccm_data[%d] (0x%08x)\n", dw, read_payload[dw], dw, dccm_data[dw]);
                                fail = 1;
                            }
                        }
                        if (!fail) {
                            VPRINTF(HIGH, "AXI2AXI: Read-back data matches sent data\n");
                        }
                    }
                    SEND_STDOUT_CTRL(FIFO_CLEAR);
                    break;

                case AXI2MBOX:
                    if (test_block_size) {
                        VPRINTF(HIGH, "Enable recovery mode emulation");
                        SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
                    }

                    if (data_check) {
                        // Populate AXI SRAM/FIFO via AHB2AXI transfer
                        VPRINTF(MEDIUM, "Sending payload via AHB i/f\n");
                        soc_ifc_axi_dma_send_ahb_payload(src_addr, use_rd_fixed, (uint32_t*)payload_start_addr, transfer_size*4, block_size);
                        if (test_block_size && src_is_fifo) {
                            uint32_t tmp[block_size]; // Push in an extra "block_size" of data; in the pulse TB mode, fifo must be full before recovery_data_avail is set
                            soc_ifc_axi_dma_send_ahb_payload(src_addr, use_rd_fixed, tmp, block_size, 0);
                        }
                    } else {
                        VPRINTF(MEDIUM, "Large transfer - enabling FIFO to auto-write\n");
                        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

                        if (!src_is_fifo) { 
                            // TRasnfer FIFO --> AXI  SRAM
                            VPRINTF(HIGH, "Moving large from FIFO via axi-to-axi xfer\n");
                            soc_ifc_axi_dma_send_axi_to_axi(AXI_FIFO_BASE_ADDR, use_rd_fixed, src_addr, use_wr_fixed, transfer_size*4, block_size);
                        }
                    }

                    // Inject random delay
                    if (inject_rand_delays) {
                        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);
                    }

                    // AXI2MBOX: Read data to mailbox
                    if (data_check) {
                        VPRINTF(HIGH, "Reading payload to Mailbox\n");

                        if (inject_rst && (rst_done==0)) {
                            VPRINTF(LOW, "Request random reset");
                            SEND_STDOUT_CTRL(RAND_RST);
                        }
                        soc_ifc_axi_dma_read_mbox_payload_no_wait(src_addr, dst_offset, use_rd_fixed, transfer_size*4, block_size);
                        soc_ifc_axi_dma_wait_idle(0);
                        if (test_block_size) {
                            SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
                        }
                    } else {
                        VPRINTF(HIGH, "Reading rand payload to Mailbox\n");

                        if (inject_rst && (rst_done==0)) {
                            VPRINTF(LOW, "Request random reset");
                            SEND_STDOUT_CTRL(RAND_RST);
                        }

                        soc_ifc_axi_dma_read_mbox_payload_no_wait(src_addr, dst_offset, use_rd_fixed, transfer_size*4, block_size);
                        soc_ifc_axi_dma_wait_idle(0);
                        if (test_block_size) {
                            SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
                        }

                        // Clear auto-write
                        VPRINTF(LOW, "Disable FIFO to auto-write\n");
                        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_OFF);
                        SEND_STDOUT_CTRL(FIFO_CLEAR);
                    }
                    if (inject_rand_delays) {
                        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);
                    }

                    if (data_check) {
                        VPRINTF(HIGH, "Reading payload from Mailbox via Direct Mode\n");
                        // Acquire the mailbox lock
                        soc_ifc_mbox_acquire_lock(1);
                        mbox_locked = 1;

                        // Verify data from mailbox against original data from DCCM
                        dccm_data = (uint32_t*) payload_start_addr;
                        for (uint32_t dw = 0; dw < transfer_size; dw++) {
                            mbox_data = lsu_read_32(((uint32_t) dst_addr) + (dw << 2));
                            if (use_rd_fixed && !src_is_fifo && (mbox_data != lsu_read_32(payload_end_addr))) {
                                VPRINTF(ERROR, "mbox_data[%d] (0x%08x) does not match lsu_read_32(payload_end_addr) (0x%08x)\n", dw, mbox_data, lsu_read_32(payload_end_addr));
                                fail = 1;
                            }
                            else if ((!use_rd_fixed || src_is_fifo) && (mbox_data != dccm_data[dw])){
                                VPRINTF(ERROR, "mbox_data[%d] (0x%08x) does not match dccm_data[%d] (0x%08x)\n", dw, mbox_data, dw, dccm_data[dw]);
                                fail = 1;
                            }
                        }
                        if (!fail) {
                            VPRINTF(HIGH, "AXI2MBOX: Read-back data matches sent data\n");
                        }
                    
                        // Release mailbox lock
                        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
                        mbox_locked = 0;
                    }
                    SEND_STDOUT_CTRL(FIFO_CLEAR);
                    break;

                case AXI2AHB:
                    if (test_block_size) {
                        VPRINTF(HIGH, "Enable recovery mode emulation");
                        SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
                    }

                    if (data_check) {
                        // Populate AXI SRAM via AHB2AXI transfer
                        VPRINTF(MEDIUM, "Sending payload via AHB i/f\n");
                        soc_ifc_axi_dma_send_ahb_payload(src_addr, use_rd_fixed, (uint32_t*)payload_start_addr, transfer_size*4, 0);
                        if (test_block_size && src_is_fifo) {
                            uint32_t tmp[block_size]; // Push in an extra "block_size" of data; in the pulse TB mode, fifo must be full before recovery_data_avail is set
                            soc_ifc_axi_dma_send_ahb_payload(src_addr, use_rd_fixed, tmp, block_size, 0);
                        }
                    } else {
                        VPRINTF(MEDIUM, "Large transfer - enabling FIFO to auto-write\n");
                        SEND_STDOUT_CTRL(FIFO_AUTO_WRITE_ON);

                        if (!src_is_fifo) {
                            // TRasnfer FIFO --> AXI  SRAM
                            VPRINTF(HIGH, "Moving large from FIFO via axi-to-axi xfer\n");
                            soc_ifc_axi_dma_send_axi_to_axi(AXI_FIFO_BASE_ADDR, use_rd_fixed, src_addr, use_wr_fixed, AXI_FIFO_SIZE_BYTES*2, 0);
                        }
                    }

                    // inject random delay
                    if (inject_rand_delays) {
                        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);
                    }

                    if (data_check) {
                        // AXI2AHB: Read data back from AXI SRAM and confirm it matches
                        VPRINTF(HIGH, "Reading payload via AHB i/f\n");

                        if (inject_rst && (rst_done==0)) {
                            VPRINTF(LOW, "Request random reset");
                            SEND_STDOUT_CTRL(RAND_RST);
                        }

                        soc_ifc_axi_dma_read_ahb_payload(src_addr, use_rd_fixed, read_payload, transfer_size*4, block_size);
                        soc_ifc_axi_dma_wait_idle(0);
                        if (test_block_size) {
                            SEND_STDOUT_CTRL(RCVY_EMU_TOGGLE);
                        }
                    } else {
                        // AXI2AHB: Read data from AXI FIFO 
                        VPRINTF(HIGH, "Reading payload via AHB i/f\n");

                        if (inject_rst && (rst_done==0)) {
                            VPRINTF(LOW, "Request random reset");
                            SEND_STDOUT_CTRL(RAND_RST);
                        }

                        for (uint32_t dw = 0; dw < transfer_size; dw++) {
                            soc_ifc_axi_dma_read_ahb_payload(src_addr, use_rd_fixed, &ahb_rdata, 4, block_size);
                        }
                    }

                    if (inject_rand_delays) {
                        SEND_STDOUT_CTRL(RAND_DELAY_TOGGLE);
                    }

                    if (data_check) {
                        // Compare read_payload data with original dccm_data
                        dccm_data = (uint32_t*) payload_start_addr;
                        for (uint32_t dw = 0; dw < transfer_size; dw++) {
                            if (use_rd_fixed && !src_is_fifo && (read_payload[dw] != lsu_read_32(payload_end_addr))) {
                                VPRINTF(ERROR, "read_payload[%d] (0x%08x) does not match lsu_read_32(payload_end_addr) (0x%08x)\n", dw, read_payload[dw], lsu_read_32(payload_end_addr));
                                fail = 1;
                            }
                            else if ((!use_rd_fixed || src_is_fifo) && read_payload[dw] != dccm_data[dw]) {
                                VPRINTF(ERROR, "read_payload[%d] (0x%08x) does not match dccm_data[%d] (0x%08x)\n", dw, read_payload[dw], dw, dccm_data[dw]);
                                fail = 1;
                            }
                        }
                        if (!fail) {
                            VPRINTF(HIGH, "AXI2AHB: Read-back data matches sent data\n");
                        }
                    }
                    SEND_STDOUT_CTRL(FIFO_CLEAR);
                    break;

                default:
                    VPRINTF(ERROR, "Unknown transfer type: %d\n", transfer_type);
                    fail = 1;
                    break;
            }

            // Calculate address for the next transfer
            // Need to move past: transfer_type (4 bytes) + transfer_size (4 bytes) + payload (transfer_size*4 bytes) + gap (4 bytes)
            dccm_addr = payload_start_addr - 4;

            // CUrrent iteration complete. Reset rst_done
            rst_done = 0;

            next_transfer_dccm_addr = dccm_addr;
            VPRINTF(MEDIUM, "Next Transfer start address (dccm_addr) = 0x%0x\n", dccm_addr);
            VPRINTF(MEDIUM, "Next Transfer start address (next_transfer_dccm_addr) = 0x%0x\n", next_transfer_dccm_addr);

        }

        // Unlock mailbox if exited due to failure
        if (mbox_locked) {
            lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
        }

        if (fail) {
            VPRINTF(FATAL, "rand_test_dma failed!\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        } else {
            VPRINTF(LOW, "rand_test_dma completed successfully!\n");
        }
}

