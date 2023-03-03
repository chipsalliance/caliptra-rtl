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

#include "caliptra_defines.h"
#include "caliptra_isr.h"
#include "riscv_hw_if.h"
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
#include "printf.h"

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

/* --------------- Function Definitions --------------- */
void caliptra_rt() {
    // Set stack pointer value pointed in linker script
    __asm__ volatile ("la sp, %0"
                      : /* output */
                      : "i" ((uintptr_t) &STACK) /* input: */
                      : /* clobbers */);

    mbox_op_s op;

    VPRINTF(LOW, "----------------------------------\n");
    VPRINTF(LOW, " Caliptra Validation RT!!\n"         );
    VPRINTF(LOW, "----------------------------------\n");

    // Runtime flow -- set ready for RT
    soc_ifc_set_flow_status_field(SOC_IFC_REG_CPTRA_FLOW_STATUS_READY_FOR_RUNTIME_MASK);

    // Initialization
    init_interrupts();

    while(1) {
        // Service received interrupts
        // Start with highest priority
        if (cptra_intr_rcv.soc_ifc_error   ) {
            VPRINTF(ERROR, "Intr received: soc_ifc_error\n");
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK) {
                cptra_intr_rcv.soc_ifc_error &= ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK;
            }
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK) {
                cptra_intr_rcv.soc_ifc_error &= ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK;
            }
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK) {
                cptra_intr_rcv.soc_ifc_error &= ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK;
            }
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK) {
                cptra_intr_rcv.soc_ifc_error &= ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK;
            }
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_MASK) {
                cptra_intr_rcv.soc_ifc_error &= ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_MASK;
            }
            if (cptra_intr_rcv.soc_ifc_error & SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK) {
                cptra_intr_rcv.soc_ifc_error &= ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK;
            }
            if (cptra_intr_rcv.soc_ifc_error & (~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INV_DEV_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_CMD_FAIL_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_BAD_FUSE_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_ICCM_BLOCKED_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_MBOX_ECC_UNC_STS_MASK)) {
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
                cptra_intr_rcv.ecc_error &= ~ECC_REG_INTR_BLOCK_RF_ERROR_INTERNAL_INTR_R_ERROR_INTERNAL_STS_MASK;
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
            VPRINTF(LOW, "Intr received: soc_ifc_notif\n");
            if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK) {
                cptra_intr_rcv.soc_ifc_notif &= ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK;
                //read the mbox command
                op = soc_ifc_read_mbox_cmd();
                if (op.cmd & MBOX_CMD_FIELD_FW_MASK) {
                    VPRINTF(LOW, "Received mailbox firmware command from SOC! Got 0x%x\n", op.cmd);
                    if (op.cmd & MBOX_CMD_FIELD_RESP_MASK) {
                        VPRINTF(ERROR, "Mailbox firmware command unexpectedly has response expected field set!\n");
                    }
                    VPRINTF(MEDIUM, "Triggering FW update reset\n");
                    //Trigger firmware update reset, new fw will get copied over from ROM
                    soc_ifc_set_fw_update_reset();
                }
                else if (op.cmd & MBOX_CMD_FIELD_RESP_MASK) {
                    VPRINTF(FATAL, "Received unexpected mailbox command (expecting RESP) from SOC! Got 0x%x\n", op.cmd);
                    SEND_STDOUT_CTRL(0x1);
                    while(1);
                }
                else {
                    VPRINTF(FATAL, "Received unexpected mailbox command (no expected RESP) from SOC! Got 0x%x\n", op.cmd);
                    SEND_STDOUT_CTRL(0x1);
                    while(1);
                }
            }
            if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK) {
                cptra_intr_rcv.soc_ifc_notif &= ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK;
            }
            if (cptra_intr_rcv.soc_ifc_notif & SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK) {
                cptra_intr_rcv.soc_ifc_notif &= ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK;
            }
            if (cptra_intr_rcv.soc_ifc_notif & (~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_AVAIL_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_MBOX_ECC_COR_STS_MASK &
                                                ~SOC_IFC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_DEBUG_LOCKED_STS_MASK)) {
                VPRINTF(FATAL, "Intr received: unsupported soc_ifc_notif (0x%x)\n", cptra_intr_rcv.soc_ifc_notif);
                SEND_STDOUT_CTRL(0x1);
                while(1);
            }
        }

        if (cptra_intr_rcv.doe_notif       ) {
            VPRINTF(LOW, "Intr received: doe_notif\n");
            if (cptra_intr_rcv.doe_notif & DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK) {
                cptra_intr_rcv.doe_notif &= ~DOE_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK;
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
                cptra_intr_rcv.ecc_notif &= ~ECC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK;
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
                cptra_intr_rcv.hmac_notif &= ~HMAC_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK;
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
                cptra_intr_rcv.sha512_notif &= ~SHA512_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK;
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
                cptra_intr_rcv.sha256_notif &= ~SHA256_REG_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK;
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
                cptra_intr_rcv.sha512_acc_notif &= ~SHA512_ACC_CSR_INTR_BLOCK_RF_NOTIF_INTERNAL_INTR_R_NOTIF_CMD_DONE_STS_MASK;
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
