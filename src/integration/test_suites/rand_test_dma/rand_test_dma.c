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


volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};

#ifndef MY_RANDOM_SEED
#define MY_RANDOM_SEED 17
#endif // MY_RANDOM_SEED

#define MAX_PAYLOAD_SIZE 2048

// Global declaration of arrays
static uint32_t read_payload[MAX_PAYLOAD_SIZE];

// Transfer types
typedef enum {
    AHB2AXI,
    MBOX2AXI,
    AXI2AXI,
    AXI2MBOX,
    AXI2AHB
} transfer_type_t;

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

void main(void) {
        int argc=0;
        char *argv[1];
        uint32_t reg;
        uint8_t fail = 0;
        uint32_t num_transfers;
        uint32_t dccm_addr;
        uint32_t payload_start_addr, payload_end_addr;
        transfer_type_t transfer_type;
        uint32_t transfer_size;
        int mbox_locked = 0;

        VPRINTF(LOW, "----------------------------------\nSmoke Test AXI DMA  !!\n----------------------------------\n");

        // Setup the interrupt CSR configuration
        init_interrupts();
        reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
        lsu_write_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, reg & ~(AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_EMPTY_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_EMPTY_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_FULL_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_FULL_EN_MASK));

        // Test each malformed command check
        // TODO

        // Read DCCM to determine number of transfers
        num_transfers = lsu_read_32(RV_DCCM_EADR - 3);
        printf("Number of transfers: %d\n", num_transfers);

        // Read transfer type and size for each transfer and perform the transfer
        dccm_addr = RV_DCCM_EADR - 7;
        for (int i = 0; i < num_transfers; i++) {
            // Read transfer type
            transfer_type = (transfer_type_t)lsu_read_32(dccm_addr);
            printf("Transfer type: %s\n", transfer_type_to_string(transfer_type));

            // Read transfer size
            dccm_addr = dccm_addr - 4;
            transfer_size = lsu_read_32(dccm_addr);

            // Validate transfer size to prevent buffer overflow
            if (transfer_size > MAX_PAYLOAD_SIZE) {
                VPRINTF(ERROR, "Transfer size %d exceeds maximum allowed %d\n", transfer_size, MAX_PAYLOAD_SIZE);
                fail = 1;
                break;
            }
            printf("Transfer size: %d dwords\n", transfer_size);
            
            // Calculate starting address of payload data
            payload_end_addr = dccm_addr - 4;  // First payload word is 4 bytes after transfer_size
            payload_start_addr = payload_end_addr - ((transfer_size - 1) * 4);  // Last word of payload (lowest address)
        
            printf("Payload Start Address = 0x%0x\n", payload_start_addr);
            printf("Payload End Address = 0x%0x\n", payload_end_addr);

            switch (transfer_type) {
                
                case AHB2AXI:
                    VPRINTF(LOW, "Sending payload via AHB i/f\n");
                    soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR, 0, (uint32_t*)payload_start_addr, transfer_size*4, 0);

                    //Read back via AHB and compare data
                    // AXI2AHB: Read data back from AXI SRAM and confirm it matches
                    VPRINTF(LOW, "Reading payload via AHB i/f\n");
                    soc_ifc_axi_dma_read_ahb_payload(AXI_SRAM_BASE_ADDR, 0, read_payload, transfer_size*4, 0);

                    // Compare read_payload data with original dccm_data
                    for (uint32_t dw = 0; dw < transfer_size; dw++) {
                        uint32_t dccm_data = lsu_read_32(payload_start_addr + (dw * 4));
                        if (read_payload[dw] != dccm_data) {
                            VPRINTF(ERROR, "read_payload[%d] (0x%08x) does not match dccm_data[%d] (0x%08x)\n", dw, read_payload[dw], dw, dccm_data);
                            fail = 1;
                        }
                    }
                    break;
                
                case MBOX2AXI:
                    // Send data through Mailbox to AXI_DMA, target the AXI SRAM
                    VPRINTF(LOW, "Writing payload to Mailbox via Direct Mode\n");
                    // Acquire the mailbox lock
                    soc_ifc_mbox_acquire_lock(1);
                    mbox_locked = 1;

                    // Source = dccm address
                    // Destination = mailbox memory
                    uint32_t* dccm_ptr = (uint32_t*)payload_start_addr;

                    // MBOX2AXI: Write data into mailbox using direct-mode
                    for (uint32_t dw = 0; dw < transfer_size; dw++) {
                        lsu_write_32(CLP_MBOX_SRAM_BASE_ADDR + 0x4400 + (dw << 2), dccm_ptr[dw]);
                    }

                    // Relese mailbox lock
                    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
                    mbox_locked = 0;

                    VPRINTF(LOW, "Sending payload from Mailbox\n");
                    soc_ifc_axi_dma_send_mbox_payload(0x4400, AXI_SRAM_BASE_ADDR, 0, transfer_size*4, 0);
                    
                    //Read back via AHB and compare data
                    // AXI2AHB: Read data back from AXI SRAM and confirm it matches
                    VPRINTF(LOW, "Reading payload via AHB i/f\n");
                    soc_ifc_axi_dma_read_ahb_payload(AXI_SRAM_BASE_ADDR, 0, read_payload, transfer_size*4, 0);

                    // Compare read_payload data with original dccm_data
                    for (uint32_t dw = 0; dw < transfer_size; dw++) {
                        uint32_t dccm_data = lsu_read_32(payload_start_addr + (dw * 4));
                        if (read_payload[dw] != dccm_data) {
                            VPRINTF(ERROR, "read_payload[%d] (0x%08x) does not match dccm_data[%d] (0x%08x)\n", dw, read_payload[dw], dw, dccm_data);
                            fail = 1;
                        }
                    }

                    break;
                
                case AXI2AXI:
                    // Populate AXI SRAM via AHB2AXI transfer
                    VPRINTF(LOW, "Sending payload via AHB i/f\n");
                    soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR, 0, (uint32_t*)payload_start_addr, transfer_size*4, 0);

                    // Use the block-size feature
                    VPRINTF(LOW, "Moving payload at SRAM via axi-to-axi xfer\n");
                    soc_ifc_axi_dma_send_axi_to_axi(AXI_SRAM_BASE_ADDR, 0, AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, (transfer_size)*4, 16*2);

                    //Read back via AHB and compare data
                    // AXI2AHB: Read data back from AXI SRAM and confirm it matches
                    VPRINTF(LOW, "Reading payload via AHB i/f\n");
                    soc_ifc_axi_dma_read_ahb_payload(AXI_SRAM_BASE_ADDR, 0, read_payload, transfer_size*4, 0);

                    // Compare read_payload data with original dccm_data
                    for (uint32_t dw = 0; dw < transfer_size; dw++) {
                        uint32_t dccm_data = lsu_read_32(payload_start_addr + (dw * 4));
                        if (read_payload[dw] != dccm_data) {
                            VPRINTF(ERROR, "read_payload[%d] (0x%08x) does not match dccm_data[%d] (0x%08x)\n", dw, read_payload[dw], dw, dccm_data);
                            fail = 1;
                        }
                    }
                    break;

                case AXI2MBOX:
                    // Populate AXI SRAM via AHB2AXI transfer
                    VPRINTF(LOW, "Sending payload via AHB i/f\n");
                    soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR, 0, (uint32_t*)payload_start_addr, transfer_size*4, 0);

                    // AXI2MBOX: Read data back through mailbox using direct-mode
                    VPRINTF(LOW, "Reading payload to Mailbox\n");
                    soc_ifc_axi_dma_read_mbox_payload(AXI_SRAM_BASE_ADDR, 0x8800, 0, transfer_size*4, 0);

                    VPRINTF(LOW, "Reading payload from Mailbox via Direct Mode\n");
                    // Acquire the mailbox lock
                    soc_ifc_mbox_acquire_lock(1);
                    mbox_locked = 1;

                    // Verify data from mailbox against original data from DCCM
                    for (uint32_t dw = 0; dw < transfer_size; dw++) {
                        uint32_t mbox_data = lsu_read_32(CLP_MBOX_SRAM_BASE_ADDR + 0x8800 + (dw << 2));
                        uint32_t dccm_data = lsu_read_32(payload_start_addr + (dw * 4));
                        if (mbox_data != dccm_data) {
                            VPRINTF(ERROR, "mbox_data[%d] (0x%08x) does not match dccm_data[%d] (0x%08x)\n", dw, mbox_data, dw, dccm_data);
                            fail = 1;
                        }
                    }

                    // Release mailbox lock
                    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
                    mbox_locked = 0;
                    break;

                case AXI2AHB:
                    // Populate AXI SRAM via AHB2AXI transfer
                    VPRINTF(LOW, "Sending payload via AHB i/f\n");
                    soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR, 0, (uint32_t*)payload_start_addr, transfer_size*4, 0);

                    // AXI2AHB: Read data back from AXI SRAM and confirm it matches
                    VPRINTF(LOW, "Reading payload via AHB i/f\n");
                    soc_ifc_axi_dma_read_ahb_payload(AXI_SRAM_BASE_ADDR, 0, read_payload, transfer_size*4, 0);

                    // Compare read_payload data with original dccm_data
                     for (uint32_t dw = 0; dw < transfer_size; dw++) {
                        uint32_t dccm_data = lsu_read_32(payload_start_addr + (dw * 4));
                        if (read_payload[dw] != dccm_data) {
                            VPRINTF(ERROR, "read_payload[%d] (0x%08x) does not match dccm_data[%d] (0x%08x)\n", dw, read_payload[dw], dw, dccm_data);
                            fail = 1;
                        }
                    }
                    break;

                default:
                    VPRINTF(ERROR, "Unknown transfer type: %d\n", transfer_type);
                    fail = 1;
                    break;
            }

            // Calculate address for the next transfer
            // Need to move past: transfer_type (4 bytes) + transfer_size (4 bytes) + payload (transfer_size*4 bytes) + gap (4 bytes)
            dccm_addr = payload_start_addr - 4;
            printf("Next Transfer start address = 0x%0x\n", dccm_addr);

        }

        // Unlock mailbox if exited due to failure
        if (mbox_locked) {
            lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
        }

        if (fail) {
            VPRINTF(FATAL, "smoke_test_dma failed!\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        } else {
            VPRINTF(LOW, "smoke_test_dma completed successfully!\n");
        }
}

//const long seed = MY_RANDOM_SEED;

/*
const enum tb_fifo_mode {
    FIFO_AUTO_READ_ON   = 0x8a,
    FIFO_AUTO_WRITE_ON  = 0x8b,
    FIFO_AUTO_READ_OFF  = 0x8c,
    FIFO_AUTO_WRITE_OFF = 0x8d,
    FIFO_CLEAR          = 0x8e,
    RAND_DELAY_TOGGLE   = 0x8f
};
*/

/*
// Function to generate random payloads and number of dwords
void generate_random_payloads(int *num_dwords_send, int *num_dwords_mbox) {
    
    printf("In generate_random_payloads function\n");
    // Initialize random number generator
    srand(seed);
    printf("Random number generator initialized\n");

    // Possible cases for num_dwords_send
    int cases[] = {15, 17, 31, 32, 33, 48, 64, 256};
    int num_cases = sizeof(cases) / sizeof(cases[0]);

    printf ("Number of cases = %d\n", num_cases);

    // Randomly select one of the cases for num_dwords_send
    *num_dwords_send = cases[rand() % num_cases];
    printf("Num dwords_send = %d\n", *num_dwords_send);
    
    // Random number of dwords (between 1 and 16) for num_dwords_mbox
    *num_dwords_mbox = cases[rand() % num_cases];
    printf("Num dwords_mbox = %d\n", *num_dwords_mbox);

    // Randomize data in send_payload and mbox_payload and print the values
    printf("Randomized send_payload:\n");
    for (int i = 0; i < *num_dwords_send; i++) {
        send_payload[i] = rand();
        printf("0x%08x ", send_payload[i]);
    }
    printf("\n");

    printf("Randomized mbox_send_payload:\n");
    for (int i = 0; i < *num_dwords_mbox; i++) {
        mbox_send_payload[i] = rand();
        printf("0x%08x ", mbox_send_payload[i]);
    }
    printf("\n");

}
*/

/*
        printf("Generating random payloads\n");
        //Generate payload of random size and randomly generated data
        generate_random_payloads(&num_dwords_send, &num_dwords_mbox);

        // AHB2AXI: Send data through AHB interface to AXI_DMA, target the AXI SRAM
        VPRINTF(LOW, "Sending payload via AHB i/f\n");
        soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR, 0, send_payload, num_dwords_send*4, 0);

        // Send data through Mailbox to AXI_DMA, target the AXI SRAM
        VPRINTF(LOW, "Writing payload to Mailbox via Direct Mode\n");
        // Acquire the mailbox lock
        if (soc_ifc_mbox_acquire_lock(1)) {
            VPRINTF(ERROR, "Acquire mailbox lock failed\n");
            fail = 1;
        }
        // MBOX2AXI: Write data into mailbox using direct-mode
        for (uint32_t dw = 0; dw < num_dwords_mbox; dw++) {
            lsu_write_32(CLP_MBOX_SRAM_BASE_ADDR + 0x4400 + (dw << 2), mbox_send_payload[dw]);
        }
        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
        VPRINTF(LOW, "Sending payload from Mailbox\n");
        if (soc_ifc_axi_dma_send_mbox_payload(0x4400, AXI_SRAM_BASE_ADDR + num_dwords_send*4, 0, num_dwords_mbox*4, 0)) {
            fail = 1;
        }

        // AXI2AXI: Move data from one address to another in AXI SRAM
        // Use the block-size feature
        VPRINTF(LOW, "Moving payload at SRAM via axi-to-axi xfer\n");
        soc_ifc_axi_dma_send_axi_to_axi(AXI_SRAM_BASE_ADDR, 0, AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, (num_dwords_send + num_dwords_mbox)*4, 16*2);

        // AXI2AHB: Read data back from AXI SRAM and confirm it matches
        VPRINTF(LOW, "Reading payload via AHB i/f\n");
        soc_ifc_axi_dma_read_ahb_payload(AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, read_payload, num_dwords_send*4, 0);
        for (uint8_t ii = 0; ii < num_dwords_send; ii++) {
            if (read_payload[ii] != send_payload[ii]) {
                VPRINTF(ERROR, "read_payload[%d] (0x%x) does not match send_payload[%d] (0x%x)\n", ii, read_payload[ii], ii, send_payload[ii]);
                fail = 1;
            }
        }

        // AXI2MBOX: Read data back through mailbox using direct-mode
        VPRINTF(LOW, "Reading payload to Mailbox\n");
        if (soc_ifc_axi_dma_read_mbox_payload(AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2 + num_dwords_send*4, 0x8800, 0, num_dwords_send*4, 0)) {
            fail = 1;
        }
        VPRINTF(LOW, "Reading payload from Mailbox via Direct Mode\n");
        // Acquire the mailbox lock
        if (soc_ifc_mbox_acquire_lock(1)) {
            VPRINTF(ERROR, "Acquire mailbox lock failed\n");
            fail = 1;
        }
        for (uint32_t dw = 0; dw < num_dwords_send; dw++) {
            mbox_read_payload[dw] = lsu_read_32(CLP_MBOX_SRAM_BASE_ADDR + 0x8800 + (dw << 2));
            if (mbox_read_payload[dw] != mbox_send_payload[dw]) {
                VPRINTF(ERROR, "mbox_read_payload[%d] (0x%x) does not match mbox_send_payload[%d] (0x%x)\n", dw, mbox_read_payload[dw], dw, mbox_send_payload[dw]);
                fail = 1;
            }
        }
        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
        */
