// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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
#include "riscv_hw_if.h"
#include "aes.h"
#include "doe.h"
#include "ecc.h"
#include "hmac.h"
#include "keyvault.h"
#include "sha256.h"
#include "sha512.h"
#include "soc_ifc.h"
#include "caliptra_isr.h"
#include <string.h>
#include <stdint.h>
#include "printf.h"

/* --------------- Global symbols/typedefs --------------- */

/* --------------- Global vars --------------- */
volatile char* stdout = (char *)STDOUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity verbosity_g = LOW;
#endif
volatile caliptra_intr_received_s cptra_intr_rcv;
volatile uint32_t                 intr_count       = 0;


/* --------------- Function Prototypes --------------- */

/* --------------- Function Definitions --------------- */
void main() {

    uint32_t intr_sts;
    uint32_t reset_reason;
    mbox_op_s op;
    void (* iccm_fmc) (void) = (void*) (RV_ICCM_SADR + MBOX_ICCM_OFFSET_FMC);
    void (* iccm_rt) (void) = (void*) (RV_ICCM_SADR + MBOX_ICCM_OFFSET_RT);
    void (* iccm_fn) (void) = (void*) (RV_ICCM_SADR);


    uint32_t iv_data_uds[] = {0x2eb94297,
                              0x77285196,
                              0x3dd39a1e,
                              0xb95d438f};
    uint32_t iv_data_fe[] = {0x14451624,
                             0x6a752c32,
                             0x9056d884,
                             0xdaf3c89d};

    VPRINTF(MEDIUM, "----------------------------------\n");
    VPRINTF(LOW,    "- Caliptra Validation ROM!!\n"       );
    VPRINTF(MEDIUM, "----------------------------------\n");

    // TODO other init tasks? (interrupts later)

    //Check the reset reason FIXME (as soc_ifc fn)
    reset_reason = lsu_read_32(CLP_SOC_IFC_REG_CPTRA_RESET_REASON);

    //Cold Boot, run DOE flows, wait for FW image
    if (reset_reason == 0x0) {
        doe_init(iv_data_uds, iv_data_fe, 0x6); // TODO replace 0x6 with entry indicators

        soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FW_MASK);

        // Wait for FW available (FMC)
        do {
            intr_sts = lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);
            intr_sts &= SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK;
        } while (!intr_sts);
        //clear the interrupt
        lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R, SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK);

        op = soc_ifc_read_mbox_cmd();
        if (op.cmd != MBOX_CMD_FMC_UPDATE) {
            VPRINTF(FATAL, "Received invalid mailbox command from SOC! Expected 0x%x, got 0x%x\n", MBOX_CMD_FMC_UPDATE, op.cmd);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        //TODO: Enhancement - Check the integrity of the firmware

        // Load FMC from mailbox
        soc_ifc_mbox_fw_flow(op);

        // Wait for FW available (RT)
        do {
            intr_sts = lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);
            intr_sts &= SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK;
        } while (!intr_sts);
        //clear the interrupt
        lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R, SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK);
        //read the mbox command
        op = soc_ifc_read_mbox_cmd();
        if (op.cmd != MBOX_CMD_RT_UPDATE) {
            VPRINTF(FATAL, "Received invalid mailbox command from SOC! Expected 0x%x, got 0x%x\n", MBOX_CMD_RT_UPDATE, op.cmd);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        // Clear 'ready for fw'
        soc_ifc_clr_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FW_MASK);

        // Jump to ICCM (this is the FMC image, a.k.a. Section 0)
        iccm_fmc();
    }  
    //FW Update Reset
    else if (reset_reason == 0x1) {
        VPRINTF(LOW, "Beginning FW Update Reset flow\n");
        op = soc_ifc_read_mbox_cmd();
        if (op.cmd != MBOX_CMD_RT_UPDATE) {
            VPRINTF(FATAL, "Received invalid mailbox command from SOC! Expected 0x%x, got 0x%x\n", MBOX_CMD_RT_UPDATE, op.cmd);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        // Jump to ICCM (this is the FMC image, a.k.a. Section 0)
        iccm_fmc();
    }
    //Warm Reset
    else if (reset_reason == 0x2) {
        // TODO: Check for NMI Cause?
        VPRINTF(LOW, "Beginning Warm Reset flow\n");

        // skip doe_init

        // Ready for FW (need to reload the FMC)
        soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FW_MASK);

        // Wait for FW available (FMC)
        do {
            intr_sts = lsu_read_32( (uintptr_t) CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);
            intr_sts &= SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK;
        } while (!intr_sts);
        //clear the interrupt
        lsu_write_32((uintptr_t) CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R, SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK);

        op = soc_ifc_read_mbox_cmd();
        if (op.cmd != MBOX_CMD_FMC_UPDATE) {
            VPRINTF(FATAL, "Received invalid mailbox command from SOC! Expected 0x%x, got 0x%x\n", MBOX_CMD_FMC_UPDATE, op.cmd);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }
        //TODO: Enhancement - Check the integrity of the firmware

        // Load FMC from mailbox
        soc_ifc_mbox_fw_flow(op);

        // Wait for FW available (RT)
        do {
            intr_sts = lsu_read_32( (uintptr_t) CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R);
            intr_sts &= SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK;
        } while (!intr_sts);
        //clear the interrupt
        lsu_write_32((uintptr_t) CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R, SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK);
        //read the mbox command
        op = soc_ifc_read_mbox_cmd();
        if (op.cmd != MBOX_CMD_RT_UPDATE) {
            VPRINTF(FATAL, "Received invalid mailbox command from SOC! Expected 0x%x, got 0x%x\n", MBOX_CMD_RT_UPDATE, op.cmd);
            SEND_STDOUT_CTRL(0x1);
            while(1);
        }

        // Clear 'ready for fw'
        soc_ifc_clr_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_FW_MASK);

        // Jump to ICCM (this is the FMC image, a.k.a. Section 0)
        iccm_fmc();
    }


    // Should never get here
    VPRINTF(FATAL, "----------------------------------\n");
    VPRINTF(FATAL, " Reached end of val FW unexpectedly! \n");
    VPRINTF(FATAL, "----------------------------------\n");
    SEND_STDOUT_CTRL(0x1);
    while(1);
}

