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
#include "caliptra_reg.h"
#include "soc_address_map.h"


volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;

#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

volatile caliptra_intr_received_s cptra_intr_rcv = {0};


//  Function Name : update_prot_cap
void update_prot_cap(){
    
    uint32_t i3c_reg_data; 
    
    // 0x52454356 = "RECOVERY"
    i3c_reg_data = 0x52454356;
    VPRINTF(LOW, "CPTRA: Writing SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_0 with 'h %0x\n", i3c_reg_data);
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_0, 0, &i3c_reg_data, 4, 0);
    
    // 0x4f435020 = "OCP"
    i3c_reg_data = 0x4f435020;
    VPRINTF(LOW, "CPTRA: Writing SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_1 with 'h %0x\n", i3c_reg_data);
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_1, 0, &i3c_reg_data, 4, 0);
    
    // Write PROT_CAP_2
    // value {0x1} to Bit 11: Flashless boot (from reset) 
    // value {0x1} to Bit 12: FIFO CMS support (INDIRECT_FIFO_CTRL)
	i3c_reg_data = 0x00000000;
    i3c_reg_data = 0x1 << 11 | i3c_reg_data;
    i3c_reg_data = 0x1 << 12 | i3c_reg_data;
    VPRINTF(LOW, "CPTRA: Writing SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2 with 'h %0x\n", i3c_reg_data);
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2, 0, &i3c_reg_data, 4, 0);	

}

// Function Name : update_device_status
void update_device_status() {

    uint32_t i3c_reg_data; 
    
    // Write DEVICE_STATUS_0
    // Byte 0    : 0x3 : Recovery mode - ready to accept recovery image
    // Byte 2,3  : 0x12: Flashless/Streaming Boot (FSB) (Reason of recovery)
    i3c_reg_data = 0x00000000;
    i3c_reg_data = 0x3 | i3c_reg_data;
    i3c_reg_data = 0x12 << 16 | i3c_reg_data;
    VPRINTF(LOW, "CPTRA: Writing SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0 with 'h %0x\n", i3c_reg_data);
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0, 0, &i3c_reg_data, 4, 0);

    // Write DEVICE_STATUS_1
    // Byte 6: Vendor Status Length, 0x0
    i3c_reg_data = 0x00000000;
    VPRINTF(LOW, "CPTRA: Writing SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_1 with 'h %0x\n", i3c_reg_data);
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_1, 0, &i3c_reg_data, 4, 0);

}

// Function Name : update_recovery_status
void update_recovery_status(uint32_t recovery_status) {
    
    uint32_t i3c_reg_data; 
    
    // Write RECOVERY_STATUS
    // 0x0: Not in recovery mode
    // 0x1: Awaiting recovery image
    // 0x2: Booting recovery image
    // 0x3: Recovery successful
    // 0xc: Recovery failed
    // 0xd: Recovery image authentication error
    // 0xe: Error entering  Recovery mode (might be administratively disabled)
    // 0xf: Invalid component address space

    i3c_reg_data = recovery_status;

    switch (recovery_status) {
        case 0x0:
            VPRINTF(LOW, "CPTRA: Recovery Status is Not in recovery mode\n");
            break;
        case 0x1:
            VPRINTF(LOW, "CPTRA: Recovery Status is Awaiting recovery image\n");
            break;
        case 0x2:
            VPRINTF(LOW, "CPTRA: Recovery Status is Booting recovery image\n");
            break;
        case 0x3:
            VPRINTF(LOW, "CPTRA: Recovery Status is Recovery successful\n");
            break;
        case 0xc:
            VPRINTF(LOW, "CPTRA: Recovery Status is Recovery failed\n");
            break;
        case 0xd:
            VPRINTF(LOW, "CPTRA: Recovery Status is Recovery image authentication error\n");
            break;
        case 0xe:
            VPRINTF(LOW, "CPTRA: Recovery Status is Error entering Recovery mode (might be administratively disabled)\n");
            break;
        case 0xf:
            VPRINTF(LOW, "CPTRA: Recovery Status is Invalid component address space\n");
            break;
        default:
            VPRINTF(ERROR, "CPTRA: Invalid recovery status value\n");
    }
    
    VPRINTF(LOW, "CPTRA: Writing SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS with 'h %0x\n", i3c_reg_data);
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS, 0, &i3c_reg_data, 4, 0);
    
}

// Function Name : Poll for Payload Available
void poll_for_payload_available() {
    
    uint32_t reg_data;
    
    // Poll for payload available
    for (uint16_t slp = 0; slp < 100; slp++) {

        reg_data = 0x00000000;
        reg_data = lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_PAYLOAD_AVAILABLE_MASK;
        
        VPRINTF(LOW, "CPTRA: Payload Available is 'h %0x\n", reg_data);
        if (reg_data == 0) {
            VPRINTF(LOW, "CPTRA: Waiting before reading Payload available status again\n");
            for (uint8_t ii = 0; ii < 16; ii++) {
                __asm__ volatile ("nop");
            }
        } else {
            VPRINTF(LOW, "CPTRA: Payload is available\n");
            break;
        }
        if(slp == 99) {
            VPRINTF(ERROR, "CPTRA: Payload not available after 100 attempts\n");
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

    }

}


// 	Read  INDIRECT_FIFO_CTRL_0 (Byte 2,3) for the Image Size
// 	Read  INDIRECT_FIFO_CTRL_1 (Byte 0,1) for the Image Size
// Combine Byte{1,0,3,2} for Size of the image to be loaded in 4B units
uint32_t read_image_size(){

    uint32_t i3c_reg_data;
    uint32_t img_size;
    
    VPRINTF(LOW, "CPTRA: Reading Image Size from INDIRECT_FIFO_CTRL Register\n");

    // Read INDIRECT_FIFO_CTRL_0
    soc_ifc_axi_dma_read_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_0, 0, &i3c_reg_data, 4, 0);
    VPRINTF(LOW, "CPTRA: Reading SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_0 with 'h %0x\n", i3c_reg_data);
    img_size = (i3c_reg_data & 0xFFFF0000) >> 16; // Byte 2,3
    
    // Read INDIRECT_FIFO_CTRL_1
    i3c_reg_data = 0x00000000;
    soc_ifc_axi_dma_read_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1, 0, &i3c_reg_data, 4, 0);
    VPRINTF(LOW, "CPTRA: Reading SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1 with 'h %0x\n", i3c_reg_data);
    img_size = (i3c_reg_data & 0x0000FFFF) << 16 | img_size; // Byte 0,1
    
    VPRINTF(LOW, "CPTRA: Image Size is 'h %0x , 'd %0d\n", img_size, img_size);
    return img_size;

}

// Read the image from the FIFO
void read_image_from_fifo(uint32_t fw_image_size) {
     
    // Program DMA to read the payload from the FIFO
    VPRINTF(LOW, "CPTRA: Programming DMA to read DWORDS : 'h %0x , 'd %0d \n", fw_image_size, fw_image_size);
    soc_ifc_axi_dma_read_mbox_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_DATA, 0x4400, 1, fw_image_size*4, 256);
    VPRINTF(LOW, "CPTRA: Reading payload from Mailbox via Direct Mode\n");
           
}

// Read the image activation
void read_image_activation() {
    
    uint32_t i3c_reg_data;

    // read RECOVERY_CTRL Byte 2 for the value 0xf (indicates Image activation) 100 times
    // 0x000f0000 = 0xf << 16

    for (uint16_t slp = 0; slp < 10; slp++) {

        i3c_reg_data = 0x00000000;
        soc_ifc_axi_dma_read_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL, 0, &i3c_reg_data, 4, 0);
        i3c_reg_data = (i3c_reg_data & 0x00ff0000) >> 16; // - shift to get the value
        VPRINTF(LOW, "CPTRA: Read SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL for expected value of 0xf vs rcvd 'h %0x\n", i3c_reg_data);
        if (i3c_reg_data == 0x0f) {
            VPRINTF(LOW, "CPTRA: Image Activation is done\n");
            break;
        } else {
            VPRINTF(LOW, "CPTRA: Waiting for Image Activation\n");
            for (uint8_t ii = 0; ii < 16; ii++) {
                __asm__ volatile ("nop");
            }
        }

        VPRINTF(LOW, "CPTRA: Reading Image Activation status from DMA\n");
        i3c_reg_data = (lsu_read_32(CLP_AXI_DMA_REG_STATUS0) & AXI_DMA_REG_STATUS0_IMAGE_ACTIVATED_MASK); // Dummy read to clear the FIFO
        if (i3c_reg_data != 0) {
            VPRINTF(LOW, "CPTRA: Image Activation Completed \n");
            break;
        }
    }
    
}

// Clear Image Activation
void update_recovery_ctrl(uint32_t recovery_ctrl) {
    
    uint32_t i3c_reg_data;
    // Clear Image Activation
    i3c_reg_data = recovery_ctrl;
    VPRINTF(LOW, "CPTRA: Writing SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL with 'h %0x\n", i3c_reg_data);
    soc_ifc_axi_dma_send_ahb_payload(SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL, 0, &i3c_reg_data, 4, 0);
    
}

// Wait function
void wait(uint32_t wait_time) {
    for (uint32_t ii = 0; ii < wait_time; ii++) {
        for (uint8_t jj = 0; jj < 16; jj++) {
            __asm__ volatile ("nop");
        }
    }
}

// Recovery Sequence
void recovery_sequence() {
    
    uint32_t fw_image_size;

    update_prot_cap();
    update_device_status();
    update_recovery_status(0x1); // Awaiting recovery image
    poll_for_payload_available();

    fw_image_size = read_image_size();
    
    // Read the image from the FIFO
    read_image_from_fifo(fw_image_size);
    read_image_activation();

    update_recovery_status(0x2); // Booting recovery image
    wait(10);
    update_recovery_status(0x3); // Recovery successful

    update_recovery_ctrl(0x00010000); // Clear Image Activation

    VPRINTF(LOW, "CPTRA: Recovery Sequence completed successfully\n");
    SEND_STDOUT_CTRL(0xff);
        
}

void main(void) {
    
    int argc=0;
    char *argv[1];
    uint32_t reg;
    uint8_t fail = 0;

    uint32_t send_payload[4] = {0xabadface, 0xba5eba11, 0xcafebabe, 0xdeadbeef};
    uint32_t read_payload[16];

    VPRINTF(LOW, "----------------------------------\n Caliptra SS Test Streaming Boot\n----------------------------------\n");

    // Setup the interrupt CSR configuration
    init_interrupts();
    fail = 0;

    // Send data through AHB interface to AXI_DMA, target the AXI SRAM
    VPRINTF(LOW, "Sending payload via AHB i/f\n");
    soc_ifc_axi_dma_send_ahb_payload(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR, 0, &send_payload, 16*4, 0);
    
    // Move data from one address to another in AXI SRAM
    // Use the block-size feature
    VPRINTF(LOW, "Moving payload at SRAM via axi-to-axi xfer\n");
    soc_ifc_axi_dma_read_ahb_payload(SOC_MCI_TOP_MCU_SRAM_BASE_ADDR, 0, &read_payload, 16*4, 0);

    //set ready for FW so tb will push FW
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_MB_PROCESSING_MASK);


    recovery_sequence();

    if (fail) {
        VPRINTF(FATAL, " cptra_ss_test_rom failed!\n");
        SEND_STDOUT_CTRL(0x1);
        while(1);
    }
}