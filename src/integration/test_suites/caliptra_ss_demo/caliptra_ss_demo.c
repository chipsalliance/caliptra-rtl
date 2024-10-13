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
//#include "i3c_csr_accessors.h"

#ifdef CALIPTRA_SS_FPGA
    #include "soc_address_map_fpga.h"
    #define RECOVERY_BASE_ADDR SOC_I3CCSR_BASE_ADDR
    #define MCU_LMEM_BASE_ADDR 0x80010000
#else
    #include "soc_address_map.h"
    #define RECOVERY_BASE_ADDR SOC_I3CCSR_BASE_ADDR
    #define MCU_LMEM_BASE_ADDR 0x90010000
#endif

#define HCI_VERSION (0x120)
#define I3C_RECOVERY_LOCAL_IMAGE 0x0

// Helpers for Recovery Flow CSRs
#define I3C_DEVICE_ID_LOW 0x0
#define I3C_DEVICE_ID_MASK 0x1
#define I3C_DEVICE_STATUS_MODE_LOW 0
#define I3C_DEVICE_STATUS_MODE_MASK 0xFF
#define I3C_DEVICE_STATUS_REASON_LOW 16
#define I3C_DEVICE_STATUS_REASON_MASK 0xFFFF0000
enum recovery_reason_e {
    RCVY_STREAMING_BOOT = 0x12,
};
#define I3C_RECOVERY_STATUS_STATUS_LOW 0
#define I3C_RECOVERY_STATUS_STATUS_MASK 0xF
#define I3C_RECOVERY_STATUS_INDEX_LOW 4
#define I3C_RECOVERY_STATUS_INDEX_MASK 0xF0
enum recovery_status_e {
    RCVY_STS_NOT_RCVY       = 0x0,
    RCVY_STS_AWAITING_IMAGE = 0x1,
    RCVY_STS_BOOTING_IMAGE  = 0x2,
    RCVY_STS_RCVY_SUCCESS   = 0x3,
    RCVY_STS_RCVY_FAILED    = 0xC,
    RCVY_STS_RCVY_AUTH_ERR  = 0xD,
    RCVY_STS_RCVY_ENTER_ERR = 0xE,
    RCVY_STS_INV_CMS        = 0xF,
};
#define I3C_LOCAL_C_IMAGE_SUPPORT_LOW 0x6
#define I3C_LOCAL_C_IMAGE_SUPPORT_MASK 0x40
#define I3C_PUSH_C_IMAGE_SUPPORT_LOW 0x7
#define I3C_PUSH_C_IMAGE_SUPPORT_MASK 0x80
#define I3C_INDIRECT_CONTROL_LOW 0x5
#define I3C_INDIRECT_CONTROL_MASK 0x20

#define MCU_RECOVERY_STORE_ADDR (MCU_LMEM_BASE_ADDR + 0xB000)
#define RCVY_IMG_ACTIVATE 0xF
#define RECOVERY_IMAGE_READY_WR_ADDR (MCU_LMEM_BASE_ADDR + 0xA000)

volatile char* stdout = (char *)STDOUT;
volatile uint32_t intr_count       = 0;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif

void caliptra_sleep(int cycles) {
      for (uint16_t slp = 0; slp < cycles; slp++) {
        __asm__ volatile ("nop");
    }
}

volatile caliptra_intr_received_s cptra_intr_rcv = {
    .doe_error        = 0,
    .doe_notif        = 0,
    .ecc_error        = 0,
    .ecc_notif        = 0,
    .hmac_error       = 0,
    .hmac_notif       = 0,
    .kv_error         = 0,
    .kv_notif         = 0,
    .sha512_error     = 0,
    .sha512_notif     = 0,
    .sha256_error     = 0,
    .sha256_notif     = 0,
    .qspi_error       = 0,
    .qspi_notif       = 0,
    .uart_error       = 0,
    .uart_notif       = 0,
    .i3c_error        = 0,
    .i3c_notif        = 0,
    .soc_ifc_error    = 0,
    .soc_ifc_notif    = 0,
    .sha512_acc_error = 0,
    .sha512_acc_notif = 0,
    .axi_dma_notif    = 0,
    .axi_dma_notif    = 0,
};

inline uint32_t get_field_from_reg(uint32_t reg_data, uint32_t mask, uint32_t lsb) {
    // Clear field by setting masked bits to 0
    reg_data &= mask;
    // Set new field value
    reg_data >>= lsb;

    // Return updated field value
    return reg_data;
}
inline uint32_t set_field_in_reg(uint32_t reg_data, uint32_t mask, uint32_t lsb, uint32_t field_data) {
    // Clear field by setting masked bits to 0
    reg_data &= ~mask;
    // Set new field value
    reg_data |= (field_data << lsb) & mask;
    return reg_data;
}

void enable_recovery_mode() {
    uint32_t data;
    uint32_t image_size;
    uint8_t flag = 1;
   
    // Enter recovery mode
    VPRINTF(LOW, "CLP: Enable recovery mode\n");

    // Write 1 to "Flashless Boot" and "FIFO CMS"
    VPRINTF(LOW, "  * CLP: Set PROT_CAP to flashless boot\n");
    soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2, 0, &data, 4, 0);
    data = set_field_in_reg(data, 0x3 << 27, 27, 0x3); // Set 'Flashless boot + FIFO CMS'
    soc_ifc_axi_dma_send_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_PROT_CAP_2, 0,  &data, 4, 0);

    // Write `0x3` to `DEVICE_STATUS` and set RECOVERY STREAMING BOOT
    VPRINTF(LOW, "  * CLP: Set DEVICE STATUS\n");
    soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0, 0, &data, 4, 0);
    data = set_field_in_reg(data, I3C_DEVICE_STATUS_MODE_MASK, I3C_DEVICE_STATUS_MODE_LOW, 0x3);
    data = set_field_in_reg(data, I3C_DEVICE_STATUS_REASON_MASK, I3C_DEVICE_STATUS_REASON_LOW, RCVY_STREAMING_BOOT);
    soc_ifc_axi_dma_send_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_DEVICE_STATUS_0, 0,  &data, 4, 0);

    // Set Recovery Mode + Index = 0
    VPRINTF(LOW, "  * CLP: Set RECOVERY STATUS\n");
    soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS, 0, &data, 4, 0);
    data = set_field_in_reg(data, I3C_RECOVERY_STATUS_STATUS_MASK, I3C_RECOVERY_STATUS_STATUS_LOW, RCVY_STS_AWAITING_IMAGE);
    data = set_field_in_reg(data, I3C_RECOVERY_STATUS_INDEX_MASK, I3C_RECOVERY_STATUS_INDEX_LOW, 0);
    soc_ifc_axi_dma_send_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS, 0,  &data, 4, 0);

    // Ensure the recovery handler changed mode and is awaiting recovery image
    // Read `RECOVERY_STATUS` - should be `1`
    soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS, 0, &data, 4, 0);
    data = get_field_from_reg(data, I3C_RECOVERY_STATUS_STATUS_MASK, I3C_RECOVERY_STATUS_STATUS_LOW);
    // TODO: Add timeout
    while (!data) {
        if (flag) {
            VPRINTF(LOW, "  * CLP: Poll for recovery status...\n");
            flag = 0;
        }
        soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_STATUS, 0, &data, 4, 0);
        data = get_field_from_reg(data, I3C_RECOVERY_STATUS_STATUS_MASK, I3C_RECOVERY_STATUS_STATUS_LOW);
    }
    flag = 1; // reset flag 
    VPRINTF(LOW, "  * CLP: Recovery mode enabled\n\n");


}

void wait_for_payload(){  
    
    uint32_t data;
    uint8_t flag = 1;

    // check if payload is available, if not wait for sometime
    soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0, 0, &data, 4, 0);
    data = get_field_from_reg(data, 0x1, 0); // extract byte 0 - Payload Available;
    // check if payload is available, if not wait for sometime
    while (data != 0) {
        if (flag) {
            VPRINTF(LOW, "  * CLP: Polling for payload availability...\n");
            flag = 0;
        }
//        caliptra_sleep(1);
        // check if payload is available, if not wait for sometime
        soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_STATUS_0, 0, &data, 4, 0);
        data = get_field_from_reg(data, 0x1, 0); // extract byte 0 - Payload Available;
    }
    flag = 1; // reset flag
    VPRINTF(LOW, "  * CLP: Payload available\n");
}

void read_recovery_image() {

    uint32_t data;
    uint32_t image_size;
    uint8_t flag = 1;
    uint32_t mcu_address_offset = 0;

    VPRINTF(LOW, "CLP: Read payload from recovery FIFO\n");


    // check if payload is available, if not wait for sometime
    // wait for payload_available to be set
    // for (uint32_t payload_cnt = 0; payload_cnt < 4; payload_cnt++) {
    //     wait_for_payload(); 

    wait_for_payload();

    // read from I3C FIFO CTRL to get the payload size
    soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_0, 0, &data, 4, 0);
    // get the payload size from the FIFO_CTRL byte 2 and 3
    VPRINTF(LOW, "  * CLP: FIFO_CTRL data: %0x\n", data);
    image_size = get_field_from_reg(data, 0xFFFF0000, 16) ;
    soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_INDIRECT_FIFO_CTRL_1, 0, &data, 4, 0);
    // get the payload size (upper) from the FIFO_CTRL byte 4 and 5
    image_size |= get_field_from_reg(data, 0xFFFF, 0) << 16;
    VPRINTF(LOW, "  * CLP: Payload size: %d\n", image_size);

    // read the payload from the FIFO and write it to the local image
    for (uint32_t image_block = 0; image_block < (image_size/4); image_block += 1) {

        VPRINTF(LOW, "  * CLP: Fetching image block %d\n", image_block);
        wait_for_payload();
        for (uint32_t fifo_loc = 0; fifo_loc < 4; fifo_loc++) {
            VPRINTF(LOW, "  * CLP: reading from address 0x%0x\n", (uint64_t) SOC_I3CCSR_PIOCONTROL_RX_DATA_PORT);
            // read the payload from the FIFO
            soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_PIOCONTROL_RX_DATA_PORT, 0, &data, 4, 0);
            VPRINTF(LOW, "  * CLP: Data Read : 0x%x\n", data);
            // write the payload to the local image
            soc_ifc_axi_dma_send_ahb_payload((uint64_t) MCU_RECOVERY_STORE_ADDR + mcu_address_offset + 4*fifo_loc , 0, &data, 4, 0);
            VPRINTF(LOW, "  * CLP: Data Written : 0x%x to address : 0x%x\n", data, (uint64_t) MCU_RECOVERY_STORE_ADDR + mcu_address_offset + 4*fifo_loc);
        }
        mcu_address_offset += 16;
    }
    
    // for (uint32_t fifo_loc = 0; fifo_loc < (image_size % 64); fifo_loc++) {
    for (uint32_t fifo_loc = 0; fifo_loc < (image_size%4); fifo_loc++) {

        VPRINTF(LOW, "  * CLP: reading from address 0x%0x\n", (uint64_t) SOC_I3CCSR_PIOCONTROL_RX_DATA_PORT);
        // read the payload from the FIFO
        soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_PIOCONTROL_RX_DATA_PORT, 0, &data, 4, 0);
        VPRINTF(LOW, "  * CLP: Data Read : 0x%x\n", data);
        // write the payload to the local image
        soc_ifc_axi_dma_send_ahb_payload((uint64_t) MCU_RECOVERY_STORE_ADDR + mcu_address_offset + 4*fifo_loc , 0, &data, 4, 0);
        VPRINTF(LOW, "  * CLP: Data Written : 0x%x to address : 0x%x\n", data, (uint64_t) MCU_RECOVERY_STORE_ADDR + mcu_address_offset + 4*fifo_loc);
    }
    VPRINTF(LOW, "  * CLP: Image read from recovery FIFO and stored at RAM address 0x%x\n", MCU_RECOVERY_STORE_ADDR);

    // Wait for image Activation
    // Read `RECOVERY_STATUS` byte 2 should be 0xf
    soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL, 0, &data, 4, 0);
    data = get_field_from_reg(data, 0xFF0000, 16); // extract byte 2 - Activate Recovery Image
    while (data != RCVY_IMG_ACTIVATE) {
        if (flag) {
            VPRINTF(LOW, "  * CLP: Poll for recovery image activation...\n");
            flag = 0;
        }
        soc_ifc_axi_dma_read_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL, 0, &data, 4, 0);
        data = get_field_from_reg(data, 0xFF0000, 16); // extract byte 2 - Activate Recovery Image
    }
    flag = 1; // reset flag
    VPRINTF(LOW, "  * CLP: Recovery image activated\n\n");

    // Clear Image Activated status by writing byte 2 with 0x1 to RECOVERY_CTRL
    data = 0x10000;
    soc_ifc_axi_dma_send_ahb_payload((uint64_t) SOC_I3CCSR_I3C_EC_SECFWRECOVERYIF_RECOVERY_CTRL, 0, &data, 4, 0);
    VPRINTF(LOW, "  * CLP: Recovery image activated status cleared\n\n");
    
}

void set_mcu_recovery_image_ready() {
    
    uint32_t data;
    VPRINTF(LOW, "CLP: setting MCU Recovery image ready\n");
    data = 0x00000001; 
    soc_ifc_axi_dma_send_ahb_payload((uint64_t) RECOVERY_IMAGE_READY_WR_ADDR, 0,  &data, 4, 0);
    VPRINTF(LOW, "CLP: setting MCU Recovery image ready done\n");

}


void main(void) {
        int argc=0;
        char *argv[1];
        uint32_t reg;
        uint8_t fail = 0;
//        uint32_t send_payload[16] = {
//            0xabadface,
//            0xba5eba11,
//            0xcafebabe,
//            0xdeadbeef,
//            0xebbf1000,
//            0xfadefee1,
//            0x12344321,
//            0xa5a5a5a5,
//            0x14351375,
//            0x8afdbe82,
//            0xafb832ba,
//            0x8843151a,
//            0xbad831b1,
//            0xf831ba83,
//            0xad813451,
//            0x67120ad3
//        };
//        uint32_t mbox_send_payload[16] = {
//            0x0991c03c,
//            0x7bc14838,
//            0xb05f2c82,
//            0x7b233274,
//            0x01b7ba27,
//            0x3f24db45,
//            0xd945c472,
//            0xabac3989,
//            0x64af1d5e,
//            0xda068da4,
//            0xeb9102ab,
//            0xf796de3e,
//            0x88fc6af8,
//            0x1a169287,
//            0xc9a6e724,
//            0x667f9dd5
//        };
//        uint32_t read_payload[16];
//        uint32_t mbox_read_payload[16];

        VPRINTF(LOW, "----------------------------------\nCaliptra Subsystem Recovery Demo!!\n----------------------------------\n");

        // Setup the interrupt CSR configuration
        init_interrupts();
        VPRINTF(LOW, "CLP: Interrupts initialized\n");
        reg = lsu_read_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R);
        lsu_write_32(CLP_AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R, reg & ~(AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_EMPTY_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_EMPTY_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_FULL_EN_MASK |
                                                                            AXI_DMA_REG_INTR_BLOCK_RF_NOTIF_INTR_EN_R_NOTIF_FIFO_NOT_FULL_EN_MASK));


        // Use DMA to initialize Recovery i/f
        enable_recovery_mode();

        // Use DMA to read payload from recovery FIFO
        read_recovery_image();

        // Use DMA to set image ready for MCU
        set_mcu_recovery_image_ready(); 

        // Done
        VPRINTF(LOW, "CLP: Done!\n");

        while(1);




//        // Test each malformed command check
//        // TODO
//
//        // Send data through AHB interface to AXI_DMA, target the AXI SRAM
//        VPRINTF(LOW, "Sending payload via AHB i/f\n");
//        soc_ifc_axi_dma_send_ahb_payload(AXI_SRAM_BASE_ADDR, 0, send_payload, 16*4, 0);
//
//        // Send data through Mailbox to AXI_DMA, target the AXI SRAM
//        VPRINTF(LOW, "Writing payload to Mailbox via Direct Mode\n");
//        // Acquire the mailbox lock
//        if (soc_ifc_mbox_acquire_lock(1)) {
//            VPRINTF(ERROR, "Acquire mailbox lock failed\n");
//            fail = 1;
//        }
//        // Write data into mailbox using direct-mode
//        for (uint32_t dw = 0; dw < 16; dw++) {
//            lsu_write_32(MBOX_DIR_BASE_ADDR + 0x4400 + (dw << 2), mbox_send_payload[dw]);
//        }
//        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
//        VPRINTF(LOW, "Sending payload from Mailbox\n");
//        if (soc_ifc_axi_dma_send_mbox_payload(0x4400, AXI_SRAM_BASE_ADDR + 16*4, 0, 16*4, 0)) {
//            fail = 1;
//        }
//
//        // Move data from one address to another in AXI SRAM
//        // Use the block-size feature
//        VPRINTF(LOW, "Moving payload at SRAM via axi-to-axi xfer\n");
//        soc_ifc_axi_dma_send_axi_to_axi(AXI_SRAM_BASE_ADDR, 0, AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, 2*16*4, 16*2);
//
//        // Read data back from AXI SRAM and confirm it matches
//        VPRINTF(LOW, "Reading payload via AHB i/f\n");
//        soc_ifc_axi_dma_read_ahb_payload(AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2, 0, read_payload, 16*4, 0);
//        for (uint8_t ii = 0; ii < 16; ii++) {
//            if (read_payload[ii] != send_payload[ii]) {
//                VPRINTF(ERROR, "read_payload[%d] (0x%x) does not match send_payload[%d] (0x%x)\n", ii, read_payload[ii], ii, send_payload[ii]);
//                fail = 1;
//            }
//        }
//
//        // Read data back through mailbox using direct-mode
//        VPRINTF(LOW, "Reading payload to Mailbox\n");
//        if (soc_ifc_axi_dma_read_mbox_payload(AXI_SRAM_BASE_ADDR + AXI_SRAM_SIZE_BYTES/2 + 16*4, 0x8800, 0, 16*4, 0)) {
//            fail = 1;
//        }
//        VPRINTF(LOW, "Reading payload from Mailbox via Direct Mode\n");
//        // Acquire the mailbox lock
//        if (soc_ifc_mbox_acquire_lock(1)) {
//            VPRINTF(ERROR, "Acquire mailbox lock failed\n");
//            fail = 1;
//        }
//        for (uint32_t dw = 0; dw < 16; dw++) {
//            mbox_read_payload[dw] = lsu_read_32(MBOX_DIR_BASE_ADDR + 0x8800 + (dw << 2));
//            if (mbox_read_payload[dw] != mbox_send_payload[dw]) {
//                VPRINTF(ERROR, "mbox_read_payload[%d] (0x%x) does not match mbox_send_payload[%d] (0x%x)\n", dw, mbox_read_payload[dw], dw, mbox_send_payload[dw]);
//                fail = 1;
//            }
//        }
//        lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
//
//
//        if (fail) {
//            VPRINTF(FATAL, "smoke_test_dma failed!\n");
//            SEND_STDOUT_CTRL(0x1);
//            while(1);
//        }
}
