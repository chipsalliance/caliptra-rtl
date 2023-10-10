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
// Description:
//   This file defines RunTime (rt) firmware that is initialized to memory at
//   the testbench level (outside Caliptra) and loaded to Caliptra RV memory via
//   mailbox firmware update.
//   Firmware defined here will execute from ICCM.

#include "caliptra_rt.h"
#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
#include "veer-csr.h"
#include "aes.h"
#include "doe.h"
#include "ecc.h"
#include "hmac.h"
#include "keyvault.h"
#include "sha256.h"
#include "sha512.h"
#include "soc_ifc.h"
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include "printf.h"
#include "wdt.h"

/* --------------- Global symbols/typedefs --------------- */
extern uintptr_t STACK;

/* --------------- Global vars --------------- */
volatile char*                    stdout           = (char *)STDOUT;
#ifdef CPT_VERBOSITY
    enum printf_verbosity             verbosity_g = CPT_VERBOSITY;
#else
    enum printf_verbosity             verbosity_g = LOW;
#endif
volatile uint32_t                 intr_count       = 0;
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
};
#define CLEAR_INTR_FLAG_SAFELY(flag, mask) \
    csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK); \
    flag &= mask; \
    csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);

#ifndef MY_RANDOM_SEED
#define MY_RANDOM_SEED 17
#endif // MY_RANDOM_SEED


enum gen_in_value {
    WDT_CASCADE     = 0x0000abab,
    WDT_INDEPENDENT = 0x0000efef
};

/* --------------- Function Definitions --------------- */
void nmi_handler() {
    mbox_op_s op;
    //Confirm this was the expected
    if ((csr_read_mcause() & MCAUSE_NMI_CODE_DBUS_LOAD_VALUE) == MCAUSE_NMI_CODE_DBUS_LOAD_VALUE) {
        csr_write_mcause(0x0);
        csr_write_mdeau(0x0);
        //mailbox command should be OOB ACCESS
        op = soc_ifc_read_mbox_cmd();
        if (op.cmd == MBOX_CMD_OOB_ACCESS) {
            //Recovering from expected NMI
            soc_ifc_set_mbox_status_field(CMD_FAILURE);
            caliptra_rt();
        }
        else {
            VPRINTF(FATAL, "Unexpected NMI\n");
            SEND_STDOUT_CTRL(0x1);
        }
    }
    else {
        VPRINTF(LOW, "In NMI handler\n");
        if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_HW_ERROR_FATAL) & SOC_IFC_REG_CPTRA_HW_ERROR_FATAL_NMI_PIN_MASK)
            VPRINTF(LOW, "Saw hw_error_fatal.nmi_pin assertion\n");
        while(1);
    }
}

void caliptra_rt() {
    // Set stack pointer value pointed in linker script
    __asm__ volatile ("la sp, %0"
                      : /* output */
                      : "i" ((uintptr_t) &STACK) /* input: */
                      : /* clobbers */);

    mbox_op_s op;
    uint32_t reg_addr;
    uint32_t read_data;
    uint32_t loop_iter;
    uint32_t loop_iter2;
    uint32_t temp; // multi-purpose variable

    //WDT vars
    int i;
    int wdt_rand_t1_val;
    int wdt_rand_t2_val;
    int mode = 0;

    VPRINTF(MEDIUM, "----------------------------------\n");
    VPRINTF(LOW,    "- Caliptra Validation RT!!\n"        );
    VPRINTF(MEDIUM, "----------------------------------\n");

    //set NMI vector
    lsu_write_32((uintptr_t) (CLP_SOC_IFC_REG_INTERNAL_NMI_VECTOR), (uint32_t) (nmi_handler));

    // Initialize rand num generator
    VPRINTF(LOW,"\nUsing random seed = %d\n\n", MY_RANDOM_SEED);
    srand((uint32_t) MY_RANDOM_SEED);

    // Runtime flow -- set ready for RT
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK);

#ifdef WDT_TEST
    VPRINTF(LOW, "Enabling WDT intr\n");
    lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R, SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER1_TIMEOUT_EN_MASK | SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTR_EN_R_ERROR_WDT_TIMER2_TIMEOUT_EN_MASK);
    lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R, SOC_IFC_REG_INTR_BLOCK_RF_GLOBAL_INTR_EN_R_ERROR_EN_MASK);
    
    //Generate constrained random WDT timer periods
    wdt_rand_t1_val = rand() % 0xfff;
    wdt_rand_t2_val = rand() % 0xfff;
    
    while (!(lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK));
    if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) == WDT_CASCADE) { //rand() % 2; //0 - independent mode, 1 - cascade mode
        VPRINTF(LOW, "Restarting WDT in cascade mode\n");
        // //Enable timer1 to start cascade mode
        configure_wdt_cascade(wdt_rand_t1_val, 0x00000000, 0xffffffff, 0xffffffff);
        service_t1_intr();

        //Disable timers before next testing
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER1_EN, 0);
        lsu_write_32(CLP_SOC_IFC_REG_CPTRA_WDT_TIMER2_EN, 0);

        //Program timer1 and 2 periods to <= 0x100 to test NMI generation. First check if there is any pending timer1 interrupt. In a corner case scenario, timer1 can timeout a second time (if the period is small enough)
        //before its timeout value is changed in prep for NMI testing. In that case, the subsequent timer1 interrupt will not be serviced resulting in a hang
        wdt_rand_t1_val = (rand() % 0x100) + 0x5;
        wdt_rand_t2_val = (rand() % 0x100) + 0x5;

        if (lsu_read_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R) & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK)
            lsu_write_32(CLP_SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R, SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK);

        // //WDT cascade mode with t2 timeout
        configure_wdt_cascade(wdt_rand_t1_val, 0x00000000, wdt_rand_t2_val, 0x00000000);
        //Don't service interrupts so it can timeout and cause NMI
    }
    else if (lsu_read_32(CLP_SOC_IFC_REG_CPTRA_GENERIC_INPUT_WIRES_0) == WDT_INDEPENDENT){
        
        //-------------------------------------------
        //Test independent mode - both timers enabled
        //-------------------------------------------
        configure_wdt_independent(BOTH_TIMERS_EN, wdt_rand_t1_val, 0x00000000, wdt_rand_t2_val, 0x00000000);

        while (!(lsu_read_32(CLP_SOC_IFC_REG_CPTRA_WDT_STATUS) & SOC_IFC_REG_CPTRA_WDT_STATUS_T1_TIMEOUT_MASK));
        //Reset timer1 period to avoid hangs in test
        set_default_t1_period();

        service_t1_intr();
        cptra_intr_rcv.soc_ifc_error |= SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK;

        //Reset timer2 period to avoid hangs in test
        while (!(lsu_read_32(CLP_SOC_IFC_REG_CPTRA_WDT_STATUS) & SOC_IFC_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_MASK));
        set_default_t2_period();

        service_t2_intr();
        cptra_intr_rcv.soc_ifc_error |= SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK;

        //-------------------------------------------
        //Test independent mode - only timer2 enabled
        //-------------------------------------------
        configure_wdt_independent(T1_DIS_T2_EN, wdt_rand_t1_val, 0x00000000, wdt_rand_t2_val, 0x00000000);
        
        //Reset timer2 period to avoid hangs in test
        while (!(lsu_read_32(CLP_SOC_IFC_REG_CPTRA_WDT_STATUS) & SOC_IFC_REG_CPTRA_WDT_STATUS_T2_TIMEOUT_MASK));
        set_default_t2_period();

        service_t2_intr();
        cptra_intr_rcv.soc_ifc_error |= SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK;
    }
#endif
    // Initialization
    init_interrupts();
    lsu_write_32(CLP_SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTR_EN_R, 0); // FIXME tmp workaround to UVM issue with predicting SHA accelerator interrupts

    while(1) {
        // Service received interrupts
        // Start with highest priority
        if (cptra_intr_rcv.soc_ifc_error   ) {
            VPRINTF(ERROR, "Intr received: soc_ifc_error\n");
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK)
            }
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK)
            }
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK) {
                enum mbox_fsm_e state;
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK)
                // If we entered the error state, we must use force-unlock to reset the mailbox state
                state = (lsu_read_32(CLP_MBOX_CSR_MBOX_STATUS) & MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_MASK) >> MBOX_CSR_MBOX_STATUS_MBOX_FSM_PS_LOW;
                if (state == MBOX_ERROR) {
                    // clr command interrupt to avoid attempted re-processing after force-unlock
                    if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK) {
                        CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_notif, ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK)
                    }
                    lsu_write_32(CLP_MBOX_CSR_MBOX_UNLOCK, MBOX_CSR_MBOX_UNLOCK_UNLOCK_MASK);
                }
            }
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK)
            }
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_MASK)
            }
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK)
            }
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK)
            }
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK)
            }
            if (cptra_intr_rcv.soc_ifc_error & (~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER1_TIMEOUT_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_WDT_TIMER2_TIMEOUT_STS_MASK)) {
                VPRINTF(FATAL, "Intr received: unsupported soc_ifc_error (0x%x)\n", cptra_intr_rcv.soc_ifc_error);
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }

        if (cptra_intr_rcv.doe_error       ) {
            VPRINTF(ERROR, "Intr received: doe_error\n");
        }

        if (cptra_intr_rcv.ecc_error       ) {
            VPRINTF(ERROR, "Intr received: ecc_error\n");
            if (cptra_intr_rcv.ecc_error & ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.ecc_error, ~ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK)
            }
            if (cptra_intr_rcv.ecc_error & ~ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK) {
                VPRINTF(FATAL, "Intr received: unsupported ecc_error (0x%x)\n", cptra_intr_rcv.ecc_error);
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }

        if (cptra_intr_rcv.hmac_error      ) {
            VPRINTF(ERROR, "Intr received: hmac_error\n");
        }

        if (cptra_intr_rcv.kv_error        ) {
            VPRINTF(ERROR, "Intr received: kv_error\n");
        }

        if (cptra_intr_rcv.sha512_error    ) {
            VPRINTF(ERROR, "Intr received: sha512_error\n");
        }

        if (cptra_intr_rcv.sha256_error    ) {
            VPRINTF(ERROR, "Intr received: sha256_error\n");
        }

        if (cptra_intr_rcv.sha512_acc_error) {
            VPRINTF(ERROR, "Intr received: sha512_acc_error\n");
        }

        if (cptra_intr_rcv.qspi_error      ) {
            VPRINTF(ERROR, "Intr received: qspi_error\n");
        }

        if (cptra_intr_rcv.uart_error      ) {
            VPRINTF(ERROR, "Intr received: uart_error\n");
        }

        if (cptra_intr_rcv.i3c_error       ) {
            VPRINTF(ERROR, "Intr received: i3c_error\n");
        }

        if (cptra_intr_rcv.soc_ifc_notif   ) {
            uint8_t fsm_chk;
            VPRINTF(LOW, "Intr received: soc_ifc_notif\n");
            if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_notif, ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK)
                fsm_chk = soc_ifc_chk_execute_uc();
                if (fsm_chk != 0) {
                    if (fsm_chk == 0xF) {
                        if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK) {
                            CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK)
                            VPRINTF(LOW, "Clearing FW soc_ifc_error intr bit (cmd fail) after servicing\n");
                        } else {
                            VPRINTF(ERROR, "After finding an error and resetting the mailbox with force unlock, RT firmware has not received an soc_ifc_err_intr!\n");
                            SEND_STDOUT_CTRL(0x1);
                            while(1);
                        }
                    }
                    continue;
                }
                // Clear any uncorrectable ECC error interrupts that may have held over from the previous operation
                // This can happen after the command flow is transferred back to SOC
                // if the ECC error occurred at address 0, since ending the flow triggers
                // rst_mbox_rdptr and a final read from 0. This might be missed by the above
                // soc_ifc_error handler.
                if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK) {
                    CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK)
                }
                // Any other errors that are flagged at this point are unexpected and should cause a test failure
                if (cptra_intr_rcv.soc_ifc_error) {
                    VPRINTF(ERROR, "Unexpected err intr 0x%x\n", cptra_intr_rcv.soc_ifc_error);
                    SEND_STDOUT_CTRL(0x1);
                    while(1);
                }
                //read the mbox command
                op = soc_ifc_read_mbox_cmd();
                if (op.cmd & MBOX_CMD_FIELD_FW_MASK) {
                    VPRINTF(MEDIUM, "Received mailbox firmware command from SOC! Got 0x%x\n", op.cmd);
                    if (op.cmd & MBOX_CMD_FIELD_RESP_MASK) {
                        VPRINTF(ERROR, "Mailbox firmware command unexpectedly has response expected field set!\n");
                    }
                    VPRINTF(MEDIUM, "Triggering FW update reset\n");
                    //Trigger firmware update reset, new fw will get copied over from ROM
                    soc_ifc_set_fw_update_reset((uint8_t) (rand() & 0xFF));
                }
                else if (op.cmd & MBOX_CMD_FIELD_RESP_MASK) {
                    VPRINTF(MEDIUM, "Received mailbox command (expecting RESP) from SOC! Got 0x%x\n", op.cmd);
                    if (op.cmd == MBOX_CMD_REG_ACCESS) {
                        for (loop_iter = 0; loop_iter<op.dlen; loop_iter+=4) {
                            reg_addr = soc_ifc_mbox_read_dataout_single();
                            VPRINTF(MEDIUM, "Reading reg addr 0x%x from mailbox req\n", reg_addr);
                            read_data = lsu_read_32((uintptr_t) reg_addr);
                            lsu_write_32((uintptr_t) (CLP_MBOX_CSR_MBOX_DATAIN), read_data);
                        }
                        lsu_write_32((uintptr_t) (CLP_MBOX_CSR_MBOX_DLEN), op.dlen);
                    }
                    else if (op.cmd == MBOX_CMD_OOB_ACCESS) {
                        //set the ERROR FATAL register to indicate the expected error
                        lsu_write_32((uintptr_t) CLP_SOC_IFC_REG_CPTRA_FW_ERROR_FATAL, 0xF0000001);
                        //just read one address, it's going to trigger NMI by going OOB
                        reg_addr = soc_ifc_mbox_read_dataout_single();
                        VPRINTF(MEDIUM, "Reading reg addr 0x%x from mailbox req\n", reg_addr);
                        read_data = lsu_read_32((uintptr_t) reg_addr);
                        VPRINTF(FATAL, "Received MBOX_CMD_OOB_ACCESS but didn't trigger NMI\n");
                        SEND_STDOUT_CTRL(0x1);
                    }
                    else if ((op.cmd == MBOX_CMD_SHA384_REQ) | (op.cmd == MBOX_CMD_SHA512_REQ)) {
                        enum sha_accel_mode_e mode;
                        mode = (op.cmd == MBOX_CMD_SHA384_REQ) ? SHA_MBOX_384 : SHA_MBOX_512;
                        //First dword contains the start address
                        temp = soc_ifc_mbox_read_dataout_single();
                        //ignore the bytes used for start address
                        op.dlen = op.dlen - 4;
                        //Copy the KAT to the start address using direct access
                        for (loop_iter = 0; loop_iter<op.dlen; loop_iter+=4) {
                            read_data = soc_ifc_mbox_read_dataout_single();
                            soc_ifc_mbox_dir_write_single(temp+loop_iter, read_data);
                        }
                        //Acquire SHA Accel lock
                        soc_ifc_sha_accel_acquire_lock();
                        soc_ifc_sha_accel_wr_mode(mode);
                        //write start addr in bytes
                        lsu_write_32((uintptr_t) (CLP_SHA512_ACC_CSR_START_ADDRESS), temp);
                        //write dlen in bytes
                        lsu_write_32((uintptr_t) (CLP_SHA512_ACC_CSR_DLEN), op.dlen);
                        soc_ifc_sha_accel_execute();
                        soc_ifc_sha_accel_poll_status();
                        lsu_write_32((uintptr_t) (CLP_MBOX_CSR_MBOX_DLEN), (mode == SHA_MBOX_384) ? 48 : 64);
                        //read the digest and write it back to the mailbox
                        reg_addr = CLP_SHA512_ACC_CSR_DIGEST_0;
                        while (reg_addr <= ((mode == SHA_MBOX_384) ? CLP_SHA512_ACC_CSR_DIGEST_11 : CLP_SHA512_ACC_CSR_DIGEST_15)) {
                            read_data = lsu_read_32(reg_addr);
                            lsu_write_32((uintptr_t) (CLP_MBOX_CSR_MBOX_DATAIN), read_data);
                            reg_addr = reg_addr + 4;
                        }
                        soc_ifc_sha_accel_clr_lock();
                    }
                    else {
                        // Read provided data
                        read_data = soc_ifc_mbox_read_dataout_single();
                        temp      = soc_ifc_mbox_read_dataout_single(); // Capture resp dlen
                        for (loop_iter = 8; loop_iter<op.dlen; loop_iter+=4) {
                            read_data = soc_ifc_mbox_read_dataout_single();
                        }

                        // Set resp dlen
                        lsu_write_32((uintptr_t) (CLP_MBOX_CSR_MBOX_DLEN), temp);

                        // Write response data
                        for (loop_iter = 0; loop_iter<temp; loop_iter+=4) {
                            lsu_write_32((uintptr_t) (CLP_MBOX_CSR_MBOX_DATAIN), rand());
                        }

                    }

                    fsm_chk = soc_ifc_chk_execute_uc();
                    if (fsm_chk != 0) {
                        if (fsm_chk == 0xF) {
                            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK) {
                                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK)
                                VPRINTF(LOW, "Clearing FW soc_ifc_error intr bit (cmd fail) after servicing\n");
                            } else {
                                VPRINTF(ERROR, "After finding an error and resetting the mailbox with force unlock, RT firmware has not received an soc_ifc_err_intr!\n");
                                SEND_STDOUT_CTRL(0x1);
                                while(1);
                            }
                        }
                        continue;
                    }
                    if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK) {
                        CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK)
                        VPRINTF(LOW, "Clearing FW soc_ifc_error intr bit (ECC unc) after servicing\n");
                        soc_ifc_set_mbox_status_field(CMD_FAILURE);
                    } else {
                        soc_ifc_set_mbox_status_field(DATA_READY);
                    }
                }
                else {
                    VPRINTF(MEDIUM, "Received mailbox command (no expected RESP) from SOC! Got 0x%x\n", op.cmd);
                    VPRINTF(MEDIUM, "Got command with DLEN 0x%x\n", op.dlen);
                    //Command to exercise direct read path to mailbox
                    if (op.cmd == MBOX_CMD_DIR_RD) {
                        // Read provided data through direct path
                        for (loop_iter = 0; loop_iter<op.dlen; loop_iter+=4) {
                            read_data = soc_ifc_mbox_dir_read_single(loop_iter);
                        }
                    }
                    //For overrun command, read an extra dword
                    else {
                        if (op.cmd == MBOX_CMD_UC_OVERRUN) op.dlen = op.dlen + 4;
                        // Read provided data
                        for (loop_iter = 0; loop_iter<op.dlen; loop_iter+=4) {
                            read_data = soc_ifc_mbox_read_dataout_single();
                        }
                    }
                    lsu_write_32((uintptr_t) (CLP_MBOX_CSR_MBOX_DLEN), 0);
                    // Check for an error
                    fsm_chk = soc_ifc_chk_execute_uc();
                    if (fsm_chk != 0) {
                        if (fsm_chk == 0xF) {
                            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK) {
                                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK)
                                VPRINTF(LOW, "Clearing FW soc_ifc_error intr bit (cmd fail) after servicing\n");
                            } else {
                                VPRINTF(ERROR, "After finding an error and resetting the mailbox with force unlock, RT firmware has not received an soc_ifc_err_intr!\n");
                                SEND_STDOUT_CTRL(0x1);
                                while(1);
                            }
                        }
                        continue;
                    }
                    //Mark the command complete
                    if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK) {
                        CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_error, ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK)
                        VPRINTF(LOW, "Clearing FW soc_ifc_error intr bit (ECC unc) after servicing\n");
                        soc_ifc_set_mbox_status_field(CMD_FAILURE);
                    } else {
                        soc_ifc_set_mbox_status_field(CMD_COMPLETE);
                    }
                }
            }
            if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_notif, ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK)
            }
            if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_notif, ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK)
            }
            if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_notif, ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK)
            }
            if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SOC_REQ_LOCK_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_notif, ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SOC_REQ_LOCK_STS_MASK)
            }
            if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.soc_ifc_notif, ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK)
            }
            if (cptra_intr_rcv.soc_ifc_notif & (~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SCAN_MODE_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_SOC_REQ_LOCK_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_GEN_IN_TOGGLE_STS_MASK )) {
                VPRINTF(FATAL, "Intr received: unsupported soc_ifc_notif (0x%x)\n", cptra_intr_rcv.soc_ifc_notif);
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }

        if (cptra_intr_rcv.doe_notif       ) {
            VPRINTF(LOW, "Intr received: doe_notif\n");
            if (cptra_intr_rcv.doe_notif & DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.doe_notif, ~DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK)
            }
            if (cptra_intr_rcv.doe_notif & (~DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK)) {
                VPRINTF(FATAL, "Intr received: unsupported doe_notif (0x%x)\n", cptra_intr_rcv.doe_notif);
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }

        if (cptra_intr_rcv.ecc_notif       ) {
            VPRINTF(LOW, "Intr received: ecc_notif\n");
            if (cptra_intr_rcv.ecc_notif & ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.ecc_notif, ~ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK)
            }
            if (cptra_intr_rcv.ecc_notif & (~ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK)) {
                VPRINTF(FATAL, "Intr received: unsupported ecc_notif (0x%x)\n", cptra_intr_rcv.ecc_notif);
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }

        if (cptra_intr_rcv.hmac_notif      ) {
            VPRINTF(LOW, "Intr received: hmac_notif\n");
            if (cptra_intr_rcv.hmac_notif & HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.hmac_notif, ~HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK)
            }
            if (cptra_intr_rcv.hmac_notif & (~HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK)) {
                VPRINTF(FATAL, "Intr received: unsupported hmac_notif (0x%x)\n", cptra_intr_rcv.hmac_notif);
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }

        if (cptra_intr_rcv.kv_notif        ) {
            VPRINTF(LOW, "Intr received: kv_notif\n");
        }

        if (cptra_intr_rcv.sha512_notif    ) {
            VPRINTF(LOW, "Intr received: sha512_notif\n");
            if (cptra_intr_rcv.sha512_notif & SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.sha512_notif, ~SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK)
            }
            if (cptra_intr_rcv.sha512_notif & (~SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK)) {
                VPRINTF(FATAL, "Intr received: unsupported sha512_notif (0x%x)\n", cptra_intr_rcv.sha512_notif);
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }

        if (cptra_intr_rcv.sha256_notif    ) {
            VPRINTF(LOW, "Intr received: sha256_notif\n");
            if (cptra_intr_rcv.sha256_notif & SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.sha256_notif, ~SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK)
            }
            if (cptra_intr_rcv.sha256_notif & (~SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK)) {
                VPRINTF(FATAL, "Intr received: unsupported sha256_notif (0x%x)\n", cptra_intr_rcv.sha256_notif);
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }

        if (cptra_intr_rcv.sha512_acc_notif) {
            VPRINTF(LOW, "Intr received: sha512_acc_notif");
            if (cptra_intr_rcv.sha512_acc_notif & SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
                CLEAR_INTR_FLAG_SAFELY(cptra_intr_rcv.sha512_acc_notif, ~SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK)
            }
            if (cptra_intr_rcv.sha512_acc_notif & (~SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK)) {
                VPRINTF(FATAL, "Intr received: unsupported sha512_acc_notif (0x%x)\n", cptra_intr_rcv.sha512_acc_notif);
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }

        if (cptra_intr_rcv.qspi_notif      ) {
            VPRINTF(LOW, "Intr received: qspi_notif\n");
        }

        if (cptra_intr_rcv.uart_notif      ) {
            VPRINTF(LOW, "Intr received: uart_notif\n");
        }

        if (cptra_intr_rcv.i3c_notif       ) {
            VPRINTF(LOW, "Intr received: i3c_notif\n");
        }
    };

}
